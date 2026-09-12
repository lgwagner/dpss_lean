//! A snapshot of the team, as the specification sees it.
//!
//! Mirrors `DPSS.IntConfig` in `Dpss/IntModel.lean`: a clock, a position per drone
//! and a heading per drone, all in scaled integer units where the perimeter is
//! `2*k*n` and the segment boundaries are the even integers `2*k*i`.
//!
//! This is specification-only. The executable `Ensemble` in `exec.rs` holds
//! machine integers and a `Vec`; `Snapshot` is what it abstracts to.

use vstd::prelude::*;
use crate::dir::Dir;

verus! {

/// A snapshot of the team, in scaled integer units.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig`.
pub struct Snapshot {
    /// Number of drones. `Fin n` in Lean; a range side-condition here.
    pub n: int,
    /// The resolution. One unit of the original perimeter is `2*k*n` here.
    pub k: int,
    /// The instant, scaled.
    pub time: int,
    /// Where each drone is, scaled.
    pub pos: Seq<int>,
    /// Which way each drone is heading.
    pub dir: Seq<Dir>,
}

impl Snapshot {
    /// Well-formedness of the view itself: the sequences have one entry per drone
    /// and the geometry is non-degenerate.
    pub open spec fn wf(self) -> bool {
        &&& self.n > 0
        &&& self.k > 0
        &&& self.pos.len() == self.n
        &&& self.dir.len() == self.n
    }
}

} // verus!
