//! The specification, generated from Lean.
//!
//! Both files here are produced by `scripts/lean_to_verus.py` and must not be
//! edited by hand; CI regenerates them and fails if either has drifted.
//!
//! * `model.rs` — the team model, from `Dpss/IntModel.lean`.
//! * `fence_model.rs` — the drone-level safety predicates, from
//!   `Dpss/FenceInt.lean`. These are the ones that never execute, so the
//!   generator is the only thing that checks them against the Lean.

pub mod model;
pub mod fence_model;
