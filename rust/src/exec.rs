//! The executable ensemble, and the step that runs on it.
//!
//! `Ensemble` holds machine integers and a `Vec`; `view_of` abstracts it to the
//! ghost `Snapshot` the specification is written over. The obligation each executable
//! function carries is that it computes exactly its specification.
//!
//! ## The clock is ghost
//!
//! Positions are bounded by the perimeter, so they fit comfortably in `i64`. The
//! clock is not bounded — a run goes on for ever — so `Ensemble` does not store it.
//! The step computes `dt` and advances positions; absolute time is carried only in
//! ghost state, where it is an unbounded `int`. That removes the one genuine
//! overflow hazard rather than papering over it.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::snapshot::Snapshot;
use crate::spec::model::*;
use crate::inv::*;

verus! {

/// The perimeter is kept well inside `i64` so that no intermediate can overflow.
/// One unit of the original perimeter is `2*k*n` here, so this is a generous
/// resolution for any realistic team.
pub open spec fn fits(c: Snapshot) -> bool {
    &&& 0 < c.n <= 1_000_000
    &&& 0 < c.k <= 1_000_000
    &&& perimeter(c) <= 1_000_000_000
}

/// A team of drones, executable.
pub struct Ensemble {
    /// The resolution.
    pub k: i64,
    /// Where each drone is, in scaled units.
    pub pos: Vec<i64>,
    /// Which way each drone is heading.
    pub dir: Vec<Dir>,
    /// The clock. Ghost, because it is unbounded — see the module note.
    pub time: Ghost<int>,
}

/// The ghost view of an executable ensemble.
pub open spec fn view_of(e: Ensemble) -> Snapshot {
    Snapshot {
        n: e.pos.len() as int,
        k: e.k as int,
        time: e.time@,
        pos: Seq::new(e.pos.len() as nat, |j: int| e.pos@[j] as int),
        dir: e.dir@,
    }
}

/// What an executable ensemble must satisfy: the representation is faithful, the
/// standing invariant holds of its view, and the numbers fit.
///
/// The invariant is part of this rather than an extra hypothesis because the
/// position bounds are exactly what rules out overflow — a drone on the perimeter
/// is a drone whose coordinate fits.
pub open spec fn repr_ok(e: Ensemble) -> bool {
    &&& e.pos.len() == e.dir.len()
    &&& e.k > 0
    &&& inv(view_of(e))
    &&& fits(view_of(e))
}

/// The perimeter, computed, with its bound.
pub fn perimeter_ex(e: &Ensemble) -> (r: i64)
    requires repr_ok(*e)
    ensures r as int == perimeter(view_of(*e)), 0 <= r <= 1_000_000_000
{
    2 * e.k * (e.pos.len() as i64)
}

pub proof fn lemma_view_pos(e: Ensemble, i: int)
    requires 0 <= i < e.pos.len()
    ensures view_of(e).pos[i] == e.pos@[i] as int
{
}

/// `border_time`, computed.
pub fn border_time_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r as int == border_time(view_of(*e), i as int)
{
    proof { lemma_view_pos(*e, i as int); }
    let perim = perimeter_ex(e);
    assert(0 <= view_of(*e).pos[i as int] <= perimeter(view_of(*e)));
    if e.dir[i] == Dir::Left {
        e.pos[i]
    } else {
        perim - e.pos[i]
    }
}

/// `gap`, computed.
pub fn gap_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i, i + 1 < e.pos.len()
    ensures r as int == gap(view_of(*e), i as int)
{
    proof {
        lemma_view_pos(*e, i as int);
        lemma_view_pos(*e, i as int + 1);
    }
    assert(0 <= view_of(*e).pos[i as int] <= perimeter(view_of(*e)));
    assert(0 <= view_of(*e).pos[i as int + 1] <= perimeter(view_of(*e)));
    e.pos[i + 1] - e.pos[i]
}

/// `meet_time`, computed.
pub fn meet_time_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i, i + 1 < e.pos.len()
    ensures r as int == meet_time(view_of(*e), i as int)
{
    let g = gap_ex(e, i);
    // the gap is nonnegative and even, so Rust's truncating division and the
    // specification's agree -- there is no convention to get wrong here
    assert(0 <= gap(view_of(*e), i as int));
    g / 2
}

/// `separation_time`, computed.
pub fn separation_time_ex(e: &Ensemble, i: usize) -> (r: i64)
    requires repr_ok(*e), 0 <= i < e.pos.len()
    ensures r as int == separation_time(view_of(*e), i as int)
{
    proof { lemma_view_pos(*e, i as int); }
    let perim = perimeter_ex(e);
    // the bound must be established before the arithmetic, not after it
    proof { crate::geometry::lemma_common_le_perimeter(view_of(*e), i as int); }
    let ce: i64 = 2 * e.k * ((i as i64) + 1);
    assert(ce as int == common_end(view_of(*e), i as int));
    assert(0 <= view_of(*e).pos[i as int] <= perimeter(view_of(*e)));
    if e.dir[i] == Dir::Left {
        e.pos[i] - ce
    } else {
        ce - e.pos[i]
    }
}

} // verus!
