//! The standing conditions, and the parts of the model the generator does not
//! translate.
//!
//! Four kinds of definition are hand-written rather than generated, each because
//! it is not arithmetic — which is where a transcription error would hide — and
//! each citing its Lean source:
//!
//! * the standing conditions, which quantify over `Fin n` with a dependent proof
//!   argument in Lean and over a bounded `int` here;
//! * `time_to_next_event`, a `Finset.inf'` over `Fin n` in Lean and a recursive
//!   minimum here;
//! * `advance` and `step`, which build a new configuration.
//!
//! The differential tests cover all of them end to end.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::snapshot::Snapshot;
use crate::spec::model::*;

verus! {

/// Every drone is somewhere on the perimeter.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.OnPerimeter`.
pub open spec fn on_perimeter(c: Snapshot) -> bool {
    forall|i: int| 0 <= i < c.n ==> 0 <= #[trigger] c.pos[i] <= perimeter(c)
}

/// Drones are indexed left to right and never pass each other.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.AdjOrdered`.
pub open spec fn adj_ordered(c: Snapshot) -> bool {
    forall|i: int| 0 <= i && i + 1 < c.n ==> 0 <= #[trigger] gap(c, i)
}

/// Escorts point at the boundary they are escorting to.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.EscortsCoherent`.
pub open spec fn escorts_coherent(c: Snapshot) -> bool {
    forall|i: int|
        0 <= i && i + 1 < c.n && #[trigger] escorting(c, i)
            ==> 0 <= separation_time(c, i)
}

/// **The lattice condition.** Every adjacent gap is even — equivalently, all the
/// drones are congruent mod 2. This is what makes `meet_time` exact.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.OnLattice`.
pub open spec fn on_lattice(c: Snapshot) -> bool {
    forall|i: int| 0 <= i && i + 1 < c.n ==> #[trigger] gap(c, i) % 2 == 0
}

/// The standing invariant: well-formed, on the perimeter, ordered, escorts
/// coherent, on the lattice.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.Invariant`, plus `wf` and the lattice.
pub open spec fn inv(c: Snapshot) -> bool {
    &&& c.wf()
    &&& on_perimeter(c)
    &&& adj_ordered(c)
    &&& escorts_coherent(c)
    &&& on_lattice(c)
}

/// A co-located pair heading apart sits on the boundary it shares.
///
/// **Not** part of `inv`: it is false of arbitrary well-formed configurations —
/// `Dpss/Counterexample.lean` exhibits four drones at `3/8` — and is a
/// *reachability* invariant, carried separately.
///
/// `Dpss/InductionStep.lean`, `DPSS.Config.ApartOnBoundaries`.
pub open spec fn apart_on_boundaries(c: Snapshot) -> bool {
    forall|i: int|
        0 <= i && i + 1 < c.n && #[trigger] co_located(c, i)
            && c.dir[i] == Dir::Left && c.dir[i + 1] == Dir::Right
            ==> c.pos[i] == common_end(c, i)
}

/// The earliest deadline across the team, as a minimum over the first `m` drones.
///
/// `Dpss/IntModel.lean` takes a `Finset.inf'` over `Fin n`; this is the same
/// minimum written as a recursion, which is what the executable loop computes.
pub open spec fn min_deadline(c: Snapshot, m: int) -> int
    decreases m
{
    if m <= 1 {
        drone_next_time(c, 0)
    } else {
        let rest = min_deadline(c, m - 1);
        let here = drone_next_time(c, m - 1);
        if here < rest { here } else { rest }
    }
}

/// The step length: the earliest deadline across all `n` drones.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.timeToNextEvent`.
pub open spec fn time_to_next_event(c: Snapshot) -> int {
    min_deadline(c, c.n)
}

/// Flying the whole team forward by `dt`.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.advance`.
pub open spec fn advance(c: Snapshot, dt: int) -> Snapshot {
    Snapshot {
        n: c.n,
        k: c.k,
        time: c.time + dt,
        pos: Seq::new(c.pos.len(), |i: int| c.pos[i] + isign(c.dir[i]) * dt),
        dir: c.dir,
    }
}

/// The configuration after the flight and before the events fire.
///
/// Named because `new_dir` is evaluated on *this*, not on the configuration the
/// step started from — an off-by-one that `Dpss/NonZeno.lean` warns about at
/// length.
pub open spec fn flown(c: Snapshot) -> Snapshot {
    advance(c, time_to_next_event(c))
}

/// One step: fly to the next event, then let every due event fire.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.step`.
pub open spec fn spec_step(c: Snapshot) -> Snapshot {
    Snapshot {
        n: flown(c).n,
        k: flown(c).k,
        time: flown(c).time,
        pos: flown(c).pos,
        dir: Seq::new(flown(c).dir.len(), |i: int| new_dir(flown(c), i)),
    }
}

/// `k` steps.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.run`.
pub open spec fn spec_run(c: Snapshot, k: nat) -> Snapshot
    decreases k
{
    if k == 0 { c } else { spec_step(spec_run(c, (k - 1) as nat)) }
}

/// **Theorem 2.1, written down.**
///
/// Proved in Lean — `Dpss/IntModel.lean`, `DPSS.IntConfig.intRun_converges`, which
/// applies `Config.convergesBy` to the embedded run. It is stated here so the
/// property exists in this crate's own language, and it is deliberately **neither
/// proved nor assumed** here: an `assume` would be a silent trust hole, and nothing
/// in this crate depends on it.
///
/// In scaled units the bound `2 - 1/n` is `4*k*n - 2*k`.
pub open spec fn converges_by(c: Snapshot, j: nat) -> bool {
    c.time + (4 * c.k * c.n - 2 * c.k) <= spec_run(c, j).time
        ==> forall|i: int| 0 <= i < c.n
                ==> left_end(c, i) <= #[trigger] spec_run(c, j).pos[i] <= right_end(c, i)
}

} // verus!
