//! The airframe numbers, as the specification sees them.
//!
//! Mirrors `DPSS.FenceInt.Vehicle` in `Dpss/FenceInt.lean`: a displacement bound,
//! a turn allowance and a sensing error, all lengths in the same units as
//! position. Stating the vehicle contract in *displacement per sample* rather
//! than in speed is what keeps every quantity a length and the whole argument in
//! integers, with no division and nothing to be inexact about
//! (`INSIGHTS.md` §20).
//!
//! This is specification-only, like `Snapshot`. The executable `VehicleEx` in
//! `fence.rs` holds machine integers and views to this. It is hand-written
//! rather than generated for the same reason `Dir` and `Snapshot` are: it is a
//! type, and the generator translates arithmetic.
//!
//! Its two specification functions — `wf` and `clearance` — *are* generated,
//! into `spec/fence_model.rs`.

use vstd::prelude::*;

verus! {

/// What the proof needs to know about the airframe.
///
/// `Dpss/FenceInt.lean`, `DPSS.FenceInt.Vehicle`.
pub struct Vehicle {
    /// The furthest the drone travels in one sample period.
    pub dmax: int,
    /// Overshoot allowance for a commanded reversal.
    pub turn: int,
    /// Position sensing error bound.
    pub eps: int,
}

} // verus!
