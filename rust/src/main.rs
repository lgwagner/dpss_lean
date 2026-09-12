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
}

/// Worst-case separation across a stale link, driven by the *verified*
/// controller. The steady-state staleness is applied from the first sample.
#[verifier::external]
fn comms_trace(name: &str, dmax: i64, turn: i64, eps: i64, d: i64, age: i64,
               margin: i64, g0: i64, samples: usize) {
    use crate::dir::Dir;
    use crate::separation::separation_control;
    println!("--- {} ---", name);
    let mut g = g0;
    let mut min_low = i64::MAX;
    for k in 0..samples {
        // the neighbour has drifted `age*dmax` since the report, and both
        // positions carry `eps` of error, all in the direction that flatters
        let obs = g + age * dmax + 2 * eps;
        let m = separation_control(margin, obs, d, Dir::Left);
        let low = if m == Dir::Left { g - 2 * dmax } else { g - 2 * turn };
        if low < min_low { min_low = low; }
        println!("k={} gap={} obs={} mode={} low={}", k, g, obs,
                 if m == Dir::Left { "closing" } else { "apart  " }, low);
        g = if m == Dir::Left { g - 2 * dmax } else { g };
    }
    println!("min low = {}  (standoff {}; {})", min_low, d,
             if min_low >= d { "clear of the standoff" } else { "BREACH" });
}

/// Worst-case separation simulation, driven by the *verified* controller.
#[verifier::external]
fn pair_trace(name: &str, dmax: i64, turn: i64, eps: i64, d: i64, margin: i64,
              g0: i64, samples: usize) {
    use crate::dir::Dir;
    use crate::separation::separation_control;
    println!("--- {} ---", name);
    let mut g = g0;
    let mut min_low = i64::MAX;
    for k in 0..samples {
        let obs = g + 2 * eps;                             // adverse sensing
        let m = separation_control(margin, obs, d, Dir::Left);   // adverse request
        let low = if m == Dir::Left { g - 2 * dmax } else { g - 2 * turn };
        if low < min_low { min_low = low; }
        println!("k={} gap={} obs={} mode={} low={}", k, g, obs,
                 if m == Dir::Left { "closing" } else { "apart  " }, low);
        g = if m == Dir::Left { g - 2 * dmax } else { g };
    }
    println!("min low = {}  (standoff {}; {})", min_low, d,
             if min_low >= d { "clear of the standoff" } else { "BREACH" });
}

/// Worst-case fence simulation, driven by the *verified* controller.
#[verifier::external]
fn fence_trace(name: &str, dmax: i64, turn: i64, eps: i64, margin: i64,
               p0: i64, samples: usize) {
    use crate::dir::Dir;
    use crate::fence::fence_control;
    println!("--- {} ---", name);
    let mut p = p0;
    let mut min_low = i64::MAX;
    for k in 0..samples {
        let obs = p + eps;                       // adverse sensing
        let d = fence_control(margin, obs, Dir::Left);   // adverse request
        let low = if d == Dir::Left { p - dmax } else { p - turn };
        if low < min_low { min_low = low; }
        println!("k={} p={} obs={} dir={} low={}", k, p, obs,
                 if d == Dir::Left { "<" } else { ">" }, low);
        p = if d == Dir::Left { p - dmax } else { p };   // no net gain on a reversal
    }
    println!("min low = {}  ({})", min_low,
             if min_low >= 0 { "clear of the fence" } else { "BREACH" });
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
