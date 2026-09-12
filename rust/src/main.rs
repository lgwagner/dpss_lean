//! # DPSS Algorithm A, in Rust, verified with Verus
//!
//! The executable half of `dpss_lean`. The Lean development proves Theorem 2.1 —
//! `n` patrol drones synchronize by time `2 - 1/n` — about a real-valued model;
//! this crate is a program that implements that model, with Verus proving that the
//! executable step computes exactly the specified step and preserves the standing
//! invariants.
//!
//! ## Integers, and why nothing is lost
//!
//! Verus has no real numbers. Positions and times here are integers, scaled by
//! `S = 2*K*n`: segment boundaries land on the even integers `2*K*i`, and because a
//! gap only ever changes by `sepRate * dt` with `sepRate` in `{-2, 0, 2}`, gap
//! parity is invariant — so `meetTime = gap/2` is always exact. The integer runs
//! are a sublattice of the real runs, not an approximation of them.
//!
//! `Dpss/IntModel.lean` states that correspondence and proves it.
//!
//! ## What is proved where
//!
//! | | |
//! |---|---|
//! | Verus, here | the executable step equals the spec step; the invariants are preserved; no overflow |
//! | Lean, `Dpss/` | `2 - 1/n`, sharp, for every resolution of the nondeterminism |
//!
//! The convergence bound is **imported, not reproved**: `converges_by` is written
//! down below as a `spec fn` so the property exists in this crate's own language,
//! but it is neither proved nor `assume`d here. Assuming it would be a silent trust
//! hole, and nothing in this crate depends on it.

#![allow(unused_imports)]

use vstd::prelude::*;

pub mod dir;
pub mod snapshot;
pub mod vehicle;
pub mod spec;
pub mod inv;
pub mod geometry;
pub mod schedule;
pub mod facts;
pub mod step_lemmas;
pub mod coherence;
pub mod reachable;
pub mod exec;
pub mod fence;
pub mod separation;
pub mod comms;

/// A trace harness, not part of the verified development.
///
/// `#[verifier::external]` excludes it from verification entirely. That is not a
/// proof hole: unlike `external_body`, it gives the function no specification, so
/// nothing verified can depend on it. It exists to *run* the verified stepper and
/// print what it produces, so that `rust/traces.sh` can check the output against
/// traces that Lean has already proved.
#[verifier::external]
fn main() {
    use crate::dir::Dir;

    // The scaled image of `ThreeConverge.cfgS` at resolution K = 1: three drones
    // on their own left endpoints, all heading right. Lean proves this run step by
    // step in `Dpss/IntModel.lean` (`cfgSI_run_1` .. `cfgSI_run_4`), and the real
    // model proves the same run in `Dpss/ThreeConverge.lean`.
    //
    // Step 2 is the one to watch: the drones land on odd positions. Positions do
    // not stay even -- every *gap* does, which is what `meet_time` needs.
    trace("cfgS  (n=3, K=1)", 1, vec![0, 2, 4],
          vec![Dir::Right, Dir::Right, Dir::Right], 4);

    // The scaled image of `Examples.spread` at resolution K = 2: two drones near
    // the left border, a quarter apart, both heading out. Lean proves this run in
    // `Dpss/Examples.lean` (`run_spread_1` .. `run_spread_3`); it settles at real
    // time 5/4, which is 10 in these units.
    trace("spread (n=2, K=2)", 2, vec![0, 2],
          vec![Dir::Right, Dir::Right], 3);

    // S2, the margined fence. One drone, one wall, worst case throughout: every
    // leftward leg is a full `dmax`, the sensor always reads high (which delays
    // the turn maximally, so it is the adversarial choice at a *left* fence),
    // every reversal costs the full `turn` allowance and yields no net progress,
    // and the surveillance algorithm asks for Left at every sample.
    //
    // `Dpss/Fence.lean` proves the drone stays clear when the margin is at least
    // `dmax + turn + eps`, and `margin_sharp` proves it need not when the margin
    // is any smaller. The second run below is that theorem at runtime: the same
    // verified controller, a margin one term short, and a breach.
    fence_trace("fence (dmax=10, turn=3, eps=2, margin=15)", 10, 3, 2, 15, 44, 6);
    fence_trace("fence, margin short by eps (margin=13 < 10+3+2)", 10, 3, 2, 13, 42, 6);

    // S3, margined separation. A pair closing on each other, worst case
    // throughout: both drones move a full `dmax` every leg so the gap shrinks by
    // `2*dmax`; the gap reads high by `2*eps`, which is adverse because it makes
    // the pair believe it has room it does not have; both reversals cost the full
    // `turn`; and the algorithm asks them to keep closing at every sample.
    //
    // The guarantee is `d <= gap`, not `0 <= gap`: in DPSS the pair is *supposed*
    // to close, so the standoff is the floor, not the wall.
    pair_trace("separation (dmax=10, turn=3, eps=2, d=5, margin=30)", 10, 3, 2, 5, 30, 52, 4);
    pair_trace("separation, margin short by 2*eps (margin=26 < 30)", 10, 3, 2, 5, 26, 48, 4);

    // S5, a stale link. The drone controls on a report of its neighbour taken
    // `age` samples ago, so its gap estimate reads high by `age*dmax + 2*eps`:
    // the neighbour's drift since the report, plus both sensing errors, all
    // adverse. The margin has to absorb that, and the second run is what happens
    // when it is not given the chance.
    comms_trace("stale link (dmax=10, turn=3, eps=2, d=5, age=2, margin=50)",
                10, 3, 2, 5, 2, 50, 52, 4);
    comms_trace("stale link on the fresh margin (margin=30 < 2*(10+3+2) + 2*10)",
                10, 3, 2, 5, 2, 30, 52, 4);

    // S6b, the link itself. The two blocks above apply the steady-state
    // staleness from the first sample, which is a bound and not a history; this
    // one is a history, so `link_ok`'s own clauses can be evaluated on it.
    link_trace("link (dmax=10, turn=3, eps=2, d=5, age=2, margin=50)",
               10, 3, 2, 5, 2, 50, 52, 4);

    // S7b, the team's standing conditions. `on_perimeter`, `adj_ordered`,
    // `escorts_coherent` and `on_lattice` are hand-written transcriptions of
    // Dpss/IntModel.lean -- the generator refuses them -- and until S7b they
    // never executed, so nothing checked them against the Lean at all. Most of
    // these rows violate one condition apiece, which is the point: on a valid
    // state a wrong transcription and a right one both answer `true`, and what
    // separates them is which states they reject. `EmitTraces.lean` prints the
    // same block from the Lean twins and scripts/check_traces.py compares them.
    standing_conditions();

    // The negative control for all of the above. A contract check that never
    // says no is not a check, so here is a drone that breaks the contract: its
    // reversal loses ground, which `leg_ok`'s `hold_leg` clause forbids. The
    // same executable specification must -- and does -- reject it, at the first
    // sample where the controller commands the reversal.
    fence_violation("fence, vehicle contract violated (a reversal that loses ground)",
                    10, 3, 2, 15, 44, 6);
}

/// `T`/`F`, as the harness prints a verdict.
#[verifier::external]
fn tf(b: bool) -> &'static str { if b { "T" } else { "F" } }

/// One configuration, with each standing condition evaluated on it.
///
/// The order is forced by the contracts, not by taste: `on_perimeter_ex` needs
/// only `repr_wf`, and the other three need `repr_bounded` — the position bounds
/// are what stop the gap subtraction from overflowing. So when the perimeter
/// check fails there is nothing further this may legitimately call, and the row
/// prints `-`. `EmitTraces.lean` mirrors the gate so the outputs compare.
///
/// Returns `apart_on_boundaries`, which is reported separately: it is stated in
/// Lean over the real-valued `Config`, not over `IntConfig`, so Lean has nothing
/// to compare and it goes on a `contract:` line.
#[verifier::external]
fn cond_row(label: &str, k: i64, pos: Vec<i64>, dir: Vec<crate::dir::Dir>) -> Option<bool> {
    use crate::exec::{Ensemble, on_perimeter_ex, adj_ordered_ex, escorts_coherent_ex,
                      on_lattice_ex, inv_ex, apart_on_boundaries_ex};
    let e = Ensemble { k, pos, dir, time: Ghost::assume_new() };
    if !on_perimeter_ex(&e) {
        println!("c={} perim=F ord=- esc=- lat=- inv=F", label);
        return None;
    }
    println!("c={} perim=T ord={} esc={} lat={} inv={}", label,
             tf(adj_ordered_ex(&e)), tf(escorts_coherent_ex(&e)),
             tf(on_lattice_ex(&e)), tf(inv_ex(&e)));
    Some(apart_on_boundaries_ex(&e))
}

/// The standing-conditions block. Same rows, same order, as `condBlock` in
/// `EmitTraces.lean`.
#[verifier::external]
fn standing_conditions() {
    use crate::dir::Dir::{Left, Right};
    println!("--- standing conditions ---");
    let rows: Vec<(&str, i64, Vec<i64>, Vec<crate::dir::Dir>)> = vec![
        ("cfgS@0",            1, vec![0, 2, 4], vec![Right, Right, Right]),
        ("cfgS@2",            1, vec![3, 5, 5], vec![Right, Left,  Left ]),
        ("spread@1",          2, vec![6, 8],    vec![Right, Left ]),
        ("off-perimeter",     1, vec![0, 2, 8], vec![Right, Right, Right]),
        ("unordered",         1, vec![0, 4, 2], vec![Right, Right, Right]),
        // the same violation at the quantifier's lower boundary: only gap 0 is
        // negative, so a range slip of `0 <= i` to `1 <= i` shows up here and
        // nowhere else in this block
        ("unordered-at-0",    1, vec![4, 0, 2], vec![Right, Right, Right]),
        ("off-lattice",       1, vec![0, 1, 4], vec![Right, Right, Right]),
        ("escort-incoherent", 1, vec![4, 4, 4], vec![Right, Right, Right]),
        ("inv-but-not-apart", 1, vec![3, 3, 5], vec![Left,  Right, Right]),
    ];
    let mut apart = String::new();
    for (label, k, pos, dir) in rows {
        match cond_row(label, k, pos, dir) {
            Some(a) => apart.push_str(&format!(" {}={}", label, tf(a))),
            None => apart.push_str(&format!(" {}=-", label)),
        }
    }
    println!("contract: apart_on_boundaries{}", apart);
}

/// The negative control for the `contract:` lines. Same vehicle, same
/// controller, but the drone slips back by the turn allowance on a reversal
/// instead of holding station — so `hold_leg` fails, and `traj_step_ok_ex` must
/// say so.
#[verifier::external]
fn fence_violation(name: &str, dmax: i64, turn: i64, eps: i64, margin: i64,
                   p0: i64, samples: usize) {
    use crate::dir::Dir;
    use crate::fence::{fence_control, traj_step_ok_ex, VehicleEx};
    println!("--- {} ---", name);
    let v = VehicleEx { dmax, turn, eps };
    let mut p = p0;
    let mut bad: i64 = -1;
    for k in 0..samples {
        let obs = p + eps;
        let d = fence_control(margin, obs, Dir::Left);
        let low = if d == Dir::Left { p - dmax } else { p - turn };
        // the violation: a reversal that does not hold station
        let p_next = if d == Dir::Left { p - dmax } else { p - turn };
        if !traj_step_ok_ex(&v, margin, p, d, low, obs, Dir::Left, p_next) && bad < 0 {
            bad = k as i64;
        }
        println!("k={} p={} obs={} dir={} low={}", k, p, obs,
                 if d == Dir::Left { "<" } else { ">" }, low);
        p = p_next;
    }
    println!("contract: traj_ok {}", verdict(bad, samples));
}

/// Worst-case separation across a stale link, driven by the *verified*
/// controller, and checked against the *specification* by `comms_step_ok_ex`
/// (S6b). The steady-state staleness is applied from the first sample.
#[verifier::external]
fn comms_trace(name: &str, dmax: i64, turn: i64, eps: i64, d: i64, age: i64,
               margin: i64, g0: i64, samples: usize) {
    use crate::dir::Dir;
    use crate::fence::VehicleEx;
    use crate::comms::comms_step_ok_ex;
    use crate::separation::separation_control;
    println!("--- {} ---", name);
    let v = VehicleEx { dmax, turn, eps };
    let mut g = g0;
    let mut min_low = i64::MAX;
    let mut bad: i64 = -1;
    for k in 0..samples {
        // the neighbour has drifted `age*dmax` since the report, and both
        // positions carry `eps` of error, all in the direction that flatters
        let obs = g + age * dmax + 2 * eps;
        let m = separation_control(margin, obs, d, Dir::Left);
        let low = if m == Dir::Left { g - 2 * dmax } else { g - 2 * turn };
        let g_next = if m == Dir::Left { g - 2 * dmax } else { g };
        if low < min_low { min_low = low; }
        if !comms_step_ok_ex(&v, age as u64, d, margin, g, obs, m, low, Dir::Left, g_next)
            && bad < 0 {
            bad = k as i64;
        }
        println!("k={} gap={} obs={} mode={} low={}", k, g, obs,
                 if m == Dir::Left { "closing" } else { "apart  " }, low);
        g = g_next;
    }
    println!("min low = {}  (standoff {}; {})", min_low, d,
             if min_low >= d { "clear of the standoff" } else { "BREACH" });
    println!("contract: comms_step_ok {}", verdict(bad, samples));
}

/// **A realizable stale link**, checked clause by clause against `link_ok` with
/// the executable mirrors of S6b.
///
/// The worst-case gap traces above are deliberately *not* realizable at their
/// first samples: they apply the full steady-state staleness from `k = 0`, which
/// is a bound rather than a history. This block is the history — two drones
/// closing at `dmax` each, a report `age` samples old, adverse sensing — so that
/// `link_ok`'s own clauses have something to be evaluated on.
#[verifier::external]
fn link_trace(name: &str, dmax: i64, turn: i64, eps: i64, d: i64, age: usize,
              margin: i64, g0: i64, samples: usize) {
    use crate::dir::Dir;
    use crate::fence::VehicleEx;
    use crate::comms::{drift_ok_ex, link_step_ok_ex};
    use crate::separation::separation_control;
    let _ = turn;
    println!("--- {} ---", name);
    let v = VehicleEx { dmax, turn, eps };
    // Own drone moves right by dmax a sample. The neighbour moves left by dmax
    // while the pair is closing and right by dmax once the controller has
    // stopped the approach, so the gap follows the same course as the trace
    // above -- and the neighbour never moves more than dmax in a sample, which
    // is the clause `drift_ok` checks.
    let pos: Vec<i64> = (0..samples).map(|k| (k as i64) * dmax).collect();
    let mut gap: Vec<i64> = Vec::new();
    let mut g = g0;
    for _ in 0..samples {
        gap.push(g);
        let obs = g + (age as i64) * dmax + 2 * eps;
        let m = separation_control(margin, obs, d, Dir::Left);
        g = if m == Dir::Left { g - 2 * dmax } else { g };
    }
    let q: Vec<i64> = (0..samples).map(|k| pos[k] + gap[k]).collect();
    let src: Vec<usize> = (0..samples).map(|k| k.saturating_sub(age)).collect();
    let rep: Vec<i64> = (0..samples).map(|k| q[src[k]] + eps).collect();
    let mut bad_link: i64 = -1;
    let mut bad_drift: i64 = -1;
    for k in 0..samples {
        println!("k={} p={} q={} gap={} src={} rep={}", k, pos[k], q[k], gap[k],
                 src[k], rep[k]);
        if !link_step_ok_ex(&v, age as u64, k as u64, src[k] as u64, rep[k], q[src[k]])
            && bad_link < 0 {
            bad_link = k as i64;
        }
        for j in 0..=k {
            if !drift_ok_ex(&v, j as u64, k as u64, q[j], q[k]) && bad_drift < 0 {
                bad_drift = k as i64;
            }
        }
    }
    println!("contract: link_step_ok {}; drift_ok {}",
             verdict(bad_link, samples), verdict(bad_drift, samples));
}

/// How a contract check reads in a trace: which sample it first failed at, or
/// that it held at all of them.
#[verifier::external]
fn verdict(bad: i64, samples: usize) -> String {
    if bad < 0 {
        format!("holds at all {} samples", samples)
    } else {
        format!("FAILS first at k={}", bad)
    }
}

/// Worst-case separation simulation, driven by the *verified* controller, and
/// checked against the *specification* by `pair_traj_step_ok_ex` (S6b).
#[verifier::external]
fn pair_trace(name: &str, dmax: i64, turn: i64, eps: i64, d: i64, margin: i64,
              g0: i64, samples: usize) {
    use crate::dir::Dir;
    use crate::fence::VehicleEx;
    use crate::separation::{pair_safe_ex, pair_traj_step_ok_ex, separation_control};
    println!("--- {} ---", name);
    let v = VehicleEx { dmax, turn, eps };
    let mut g = g0;
    let mut min_low = i64::MAX;
    let mut bad: i64 = -1;
    let m0 = separation_control(margin, g0 + 2 * eps, d, Dir::Left);
    let safe0 = pair_safe_ex(&v, d, g0, m0);
    for k in 0..samples {
        let obs = g + 2 * eps;                             // adverse sensing
        let m = separation_control(margin, obs, d, Dir::Left);   // adverse request
        let low = if m == Dir::Left { g - 2 * dmax } else { g - 2 * turn };
        let g_next = if m == Dir::Left { g - 2 * dmax } else { g };
        if low < min_low { min_low = low; }
        if !pair_traj_step_ok_ex(&v, d, margin, g, m, low, obs, Dir::Left, g_next)
            && bad < 0 {
            bad = k as i64;
        }
        println!("k={} gap={} obs={} mode={} low={}", k, g, obs,
                 if m == Dir::Left { "closing" } else { "apart  " }, low);
        g = g_next;
    }
    println!("min low = {}  (standoff {}; {})", min_low, d,
             if min_low >= d { "clear of the standoff" } else { "BREACH" });
    println!("contract: pair_traj_ok {}; pair_safe(0) {}", verdict(bad, samples), safe0);
}

/// Worst-case fence simulation, driven by the *verified* controller, and
/// checked against the *specification* by `traj_step_ok_ex` (S6b).
#[verifier::external]
fn fence_trace(name: &str, dmax: i64, turn: i64, eps: i64, margin: i64,
               p0: i64, samples: usize) {
    use crate::dir::Dir;
    use crate::fence::{fence_control, safe_ex, traj_step_ok_ex, VehicleEx};
    println!("--- {} ---", name);
    let v = VehicleEx { dmax, turn, eps };
    let mut p = p0;
    let mut min_low = i64::MAX;
    let mut bad: i64 = -1;
    let d0 = fence_control(margin, p0 + eps, Dir::Left);
    let safe0 = safe_ex(&v, p0, d0);
    for k in 0..samples {
        let obs = p + eps;                       // adverse sensing
        let d = fence_control(margin, obs, Dir::Left);   // adverse request
        let low = if d == Dir::Left { p - dmax } else { p - turn };
        let p_next = if d == Dir::Left { p - dmax } else { p };  // no gain on a reversal
        if low < min_low { min_low = low; }
        if !traj_step_ok_ex(&v, margin, p, d, low, obs, Dir::Left, p_next) && bad < 0 {
            bad = k as i64;
        }
        println!("k={} p={} obs={} dir={} low={}", k, p, obs,
                 if d == Dir::Left { "<" } else { ">" }, low);
        p = p_next;
    }
    println!("min low = {}  ({})", min_low,
             if min_low >= 0 { "clear of the fence" } else { "BREACH" });
    println!("contract: traj_ok {}; safe(0) {}", verdict(bad, samples), safe0);
}

#[verifier::external]
fn trace(name: &str, k: i64, pos: Vec<i64>, dir: Vec<crate::dir::Dir>, steps: usize) {
    use crate::exec::{Ensemble, step_ex, time_to_next_event_ex};
    let mut e = Ensemble { k, pos, dir, time: Ghost::assume_new() };
    let mut t: i64 = 0;
    println!("--- {} ---", name);
    println!("{}", render(t, &e));
    for _ in 0..steps {
        t += time_to_next_event_ex(&e);
        step_ex(&mut e);
        println!("{}", render(t, &e));
    }
}

#[verifier::external]
fn render(t: i64, e: &crate::exec::Ensemble) -> String {
    use crate::dir::Dir;
    let dirs: Vec<&str> = e.dir.iter()
        .map(|d| if *d == Dir::Left { "<" } else { ">" })
        .collect();
    let poss: Vec<String> = e.pos.iter().map(|p| p.to_string()).collect();
    format!("t={} pos=[{}] dir=[{}]", t, poss.join(","), dirs.join(","))
}
