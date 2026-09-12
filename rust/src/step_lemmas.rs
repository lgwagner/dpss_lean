//! The step preserves the standing conditions.
//!
//! Each lemma mirrors one in `Dpss/`, and each is arithmetic on top of the two
//! scheduler guarantees in `schedule.rs`: the step is never negative, and it never
//! overshoots any drone's own deadline.
//!
//! The three conditions that depend only on positions come first, because an event
//! changes headings and not positions — so for them `spec_step` and `advance` are
//! interchangeable.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::snapshot::Snapshot;
use crate::spec::model::*;
use crate::inv::*;
use crate::schedule::*;

verus! {

/// Flying moves each drone by its velocity times the elapsed time.
pub proof fn lemma_advance_pos(c: Snapshot, dt: int, i: int)
    requires 0 <= i < c.pos.len()
    ensures advance(c, dt).pos[i] == c.pos[i] + isign(c.dir[i]) * dt
{
}

/// So a gap changes by the separation rate times the elapsed time.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.gap_advance`.
pub proof fn lemma_advance_gap(c: Snapshot, dt: int, i: int)
    requires 0 <= i, i + 1 < c.n, c.wf()
    ensures gap(advance(c, dt), i) == gap(c, i) + sep_rate(c, i) * dt
{
    lemma_advance_pos(c, dt, i);
    lemma_advance_pos(c, dt, i + 1);
    // the two velocity terms collect into the separation rate
    assert((c.pos[i + 1] + isign(c.dir[i + 1]) * dt)
            - (c.pos[i] + isign(c.dir[i]) * dt)
        == (c.pos[i + 1] - c.pos[i])
            + (isign(c.dir[i + 1]) - isign(c.dir[i])) * dt)
        by (nonlinear_arith);
}

/// A step moves the drones exactly as flying does; the events only change
/// headings.
pub proof fn lemma_step_pos(c: Snapshot, i: int)
    requires 0 <= i < c.n, c.wf()
    ensures
        spec_step(c).pos[i] == advance(c, time_to_next_event(c)).pos[i],
        spec_step(c).n == c.n,
        spec_step(c).k == c.k,
{
}

pub proof fn lemma_step_gap(c: Snapshot, i: int)
    requires 0 <= i, i + 1 < c.n, c.wf()
    ensures gap(spec_step(c), i) == gap(advance(c, time_to_next_event(c)), i)
{
    lemma_step_pos(c, i);
    lemma_step_pos(c, i + 1);
}

/// **The lattice is closed under a step.**
///
/// A gap only ever changes by `sep_rate * dt`, and `sep_rate` is even. This is the
/// fact the whole integer model rests on.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.onLattice_step`.
pub proof fn lemma_on_lattice_step(c: Snapshot)
    requires inv(c)
    ensures on_lattice(spec_step(c))
{
    let dt = time_to_next_event(c);
    assert forall|i: int| 0 <= i && i + 1 < c.n implies
            #[trigger] gap(spec_step(c), i) % 2 == 0 by {
        lemma_step_gap(c, i);
        lemma_advance_gap(c, dt, i);
        crate::facts::lemma_sep_rate_even(c, i);
        assert(gap(c, i) % 2 == 0);
        assert((gap(c, i) + sep_rate(c, i) * dt) % 2 == 0) by (nonlinear_arith)
            requires
                gap(c, i) % 2 == 0,
                sep_rate(c, i) == -2 || sep_rate(c, i) == 0 || sep_rate(c, i) == 2;
    }
}

/// **A step keeps every drone on the perimeter.**
///
/// The step never runs past any drone's border deadline, so nobody overshoots the
/// edge.
///
/// `Dpss/Synchronization.lean`, `DPSS.Config.onPerimeter_step`.
pub proof fn lemma_on_perimeter_step(c: Snapshot)
    requires inv(c)
    ensures on_perimeter(spec_step(c))
{
    let dt = time_to_next_event(c);
    lemma_step_nonneg(c);
    assert forall|i: int| 0 <= i < c.n implies
            0 <= #[trigger] spec_step(c).pos[i] <= perimeter(spec_step(c)) by {
        lemma_step_pos(c, i);
        lemma_advance_pos(c, dt, i);
        lemma_step_le_drone(c, i);
        lemma_drone_le_border(c, i);
        assert(0 <= c.pos[i] <= perimeter(c));
        match c.dir[i] {
            Dir::Left => {},
            Dir::Right => {},
        }
    }
}

/// **A step preserves the ordering of the drones.**
///
/// Because the step flies for no longer than the time to the next collision,
/// nobody passes anybody. The lattice is what makes the halving exact, so
/// `2 * meet_time == gap` and the arithmetic closes.
///
/// `Dpss/Step.lean`, `DPSS.Config.adjOrdered_step`.
pub proof fn lemma_adj_ordered_step(c: Snapshot)
    requires inv(c)
    ensures adj_ordered(spec_step(c))
{
    let dt = time_to_next_event(c);
    lemma_step_nonneg(c);
    assert forall|i: int| 0 <= i && i + 1 < c.n implies
            0 <= #[trigger] gap(spec_step(c), i) by {
        lemma_step_gap(c, i);
        lemma_advance_gap(c, dt, i);
        crate::facts::lemma_sep_rate_even(c, i);
        assert(0 <= gap(c, i));
        if approaching(c, i) {
            lemma_step_le_drone(c, i);
            lemma_drone_le_meet(c, i);
            assert(sep_rate(c, i) == -2);
            assert(gap(c, i) % 2 == 0);
            assert(2 * meet_time(c, i) == gap(c, i)) by (nonlinear_arith)
                requires gap(c, i) % 2 == 0, meet_time(c, i) == gap(c, i) / 2;
        } else {
            assert(sep_rate(c, i) >= 0);
            assert(sep_rate(c, i) * dt >= 0) by (nonlinear_arith)
                requires sep_rate(c, i) >= 0, dt >= 0;
        }
    }
}

/// **The standing invariant holds in mid-step**, after the flight and before the
/// events fire. The executable step passes through that configuration, so it has
/// to hold there as well as at the ends.
pub proof fn lemma_inv_flown(c: Snapshot)
    requires inv(c)
    ensures inv(flown(c))
{
    lemma_on_perimeter_step(c);
    lemma_adj_ordered_step(c);
    lemma_on_lattice_step(c);
    crate::coherence::lemma_escorts_coherent_flown(c);
    assert forall|i: int| 0 <= i < c.n implies
            0 <= #[trigger] flown(c).pos[i] <= perimeter(flown(c)) by {
        lemma_step_pos(c, i);
    }
    assert forall|i: int| 0 <= i && i + 1 < c.n implies
            0 <= #[trigger] gap(flown(c), i) by {
        lemma_step_gap(c, i);
    }
    assert forall|i: int| 0 <= i && i + 1 < c.n implies
            #[trigger] gap(flown(c), i) % 2 == 0 by {
        lemma_step_gap(c, i);
    }
}

/// The step leaves the shape of the ensemble alone.
pub proof fn lemma_wf_step(c: Snapshot)
    requires c.wf()
    ensures spec_step(c).wf()
{
}

/// **The standing invariant is preserved by a step.**
///
/// `Dpss/Coherence.lean`, `DPSS.Config.invariant_step`, plus the lattice.
pub proof fn lemma_inv_step(c: Snapshot)
    requires inv(c)
    ensures inv(spec_step(c))
{
    lemma_wf_step(c);
    lemma_on_perimeter_step(c);
    lemma_adj_ordered_step(c);
    lemma_on_lattice_step(c);
    crate::coherence::lemma_escorts_coherent_step(c);
}

/// **And therefore by a whole run.**
///
/// `Dpss/Coherence.lean`, `DPSS.Config.invariant_run`.
pub proof fn lemma_inv_run(c: Snapshot, k: nat)
    requires inv(c)
    ensures inv(spec_run(c, k))
    decreases k
{
    if k > 0 {
        lemma_inv_run(c, (k - 1) as nat);
        lemma_inv_step(spec_run(c, (k - 1) as nat));
    }
}

} // verus!
