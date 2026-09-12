//! Headings.
//!
//! Mirrors `DPSS.Dir` in `Dpss/Basic.lean`. Speed is normalized to one, so a
//! heading *is* a velocity — which is why `isign` (generated into `spec::model`
//! from `Dpss/IntModel.lean`) is the only arithmetic a heading ever needs.

use vstd::prelude::*;

verus! {

/// A drone is, at every moment, travelling left or right along the perimeter.
///
/// `Dpss/Basic.lean`, `DPSS.Dir`.
#[derive(PartialEq, Eq, Structural, Clone, Copy)]
pub enum Dir {
    Left,
    Right,
}

} // verus!
