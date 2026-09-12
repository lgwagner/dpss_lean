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

pub mod dir;
