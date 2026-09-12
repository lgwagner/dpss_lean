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
