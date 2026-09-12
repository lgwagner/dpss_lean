//! Headings.
//!
//! Mirrors `DPSS.Dir` in `Dpss/Basic.lean` and `DPSS.Dir.isign` in
//! `Dpss/IntModel.lean`. Speed is normalized to one, so a heading *is* a velocity.

use vstd::prelude::*;

verus! {

/// A drone is, at every moment, travelling left or right along the perimeter.
#[derive(PartialEq, Eq, Structural, Clone, Copy)]
pub enum Dir {
    Left,
    Right,
}

impl Dir {
    /// The velocity, as an integer: `-1` leftward, `+1` rightward.
    ///
    /// `Dpss/IntModel.lean`, `DPSS.Dir.isign`.
    pub open spec fn isign(self) -> int {
        match self {
            Dir::Left => -1int,
            Dir::Right => 1int,
        }
    }

    /// Reversing a heading. `Dpss/Basic.lean`, `DPSS.Dir.flip`.
    pub open spec fn flip(self) -> Dir {
        match self {
            Dir::Left => Dir::Right,
            Dir::Right => Dir::Left,
        }
    }
}

/// A heading's velocity squares to one — what makes "distance to a point, divided
/// by speed" come out right. `Dpss/IntModel.lean`, `DPSS.Dir.isign_mul_self`.
pub proof fn lemma_isign_mul_self(d: Dir)
    ensures d.isign() * d.isign() == 1
{
    match d {
        Dir::Left => {},
        Dir::Right => {},
    }
}

/// A drone never stands still.
pub proof fn lemma_isign_ne_zero(d: Dir)
    ensures d.isign() != 0
{
}

} // verus!

