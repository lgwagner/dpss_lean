//! Escorts stay coherent across a step.
//!
//! The last standing condition, and the only one whose proof has to look at what
//! `new_dir` did. Mirrors `Dpss/Coherence.lean` — the workhorse first, then the
//! theorem.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::snapshot::Snapshot;
use crate::spec::model::*;
use crate::inv::*;
use crate::schedule::*;
use crate::geometry::*;
use crate::step_lemmas::*;

verus! {

/// A pair heading the same way keeps its gap: the escort is emergent, not stored.
pub proof fn lemma_gap_unchanged_of_same_dir(c: Snapshot, i: int)
    requires c.wf(), 0 <= i, i + 1 < c.n, c.dir[i] == c.dir[i + 1]
    ensures gap(flown(c), i) == gap(c, i)
{
    lemma_advance_gap(c, time_to_next_event(c), i);
    assert(sep_rate(c, i) == 0);
}

/// Flying reduces a drone's separation deadline by exactly the elapsed time.
///
/// `Dpss/Coherence.lean`, `DPSS.Config.separationTime_advance`.
pub proof fn lemma_separation_time_advance(c: Snapshot, dt: int, i: int)
    requires 0 <= i < c.n, c.wf()
    ensures separation_time(advance(c, dt), i) == separation_time(c, i) - dt
{
    lemma_advance_pos(c, dt, i);
    crate::facts::lemma_isign_mul_self(c.dir[i]);
    assert((common_end(c, i) - (c.pos[i] + isign(c.dir[i]) * dt)) * isign(c.dir[i])
        == (common_end(c, i) - c.pos[i]) * isign(c.dir[i])
            - dt * (isign(c.dir[i]) * isign(c.dir[i]))) by (nonlinear_arith);
}

/// Multiplying by a heading's velocity is a sign flip, not a multiplication. Z3
/// needs this said once; afterwards every separation-time goal is linear.
pub proof fn lemma_times_isign(x: int, d: Dir)
    ensures
        d == Dir::Right ==> x * isign(d) == x,
        d == Dir::Left ==> x * isign(d) == -x,
{
    match d {
        Dir::Left => assert(x * (-1int) == -x) by (nonlinear_arith),
        Dir::Right => assert(x * 1int == x) by (nonlinear_arith),
    }
}

/// **If a co-located pair both end up heading left, they are at or beyond the
/// boundary they share.**
///
/// Both awkward branches of the theorem below reduce to this. Every way drone
/// `i+1` could have acquired a leftward heading puts the pair there — and the last
/// of those ways is the only place the proof has to reach back to the
/// configuration the step started from.
///
/// `Dpss/Coherence.lean`, `DPSS.Config.commonEnd_le_pos_of_both_left`.
pub proof fn lemma_common_le_pos_of_both_left(c: Snapshot, i: int)
    requires
        inv(c),
        0 <= i,
        i + 1 < c.n,
        co_located(flown(c), i),
        flown(c).dir[i] == Dir::Left,
        new_dir(flown(c), i + 1) == Dir::Left,
    ensures common_end(c, i) <= flown(c).pos[i]
{
    let f = flown(c);
    let dt = time_to_next_event(c);
    lemma_step_nonneg(c);
    lemma_segment_width(c, i);
    lemma_segment_width(c, i + 1);
    lemma_common_lt_common_next(c, i);
    lemma_common_is_next_left(c, i);
    lemma_common_le_perimeter(c, i + 1);
    lemma_advance_pos(c, dt, i);
    lemma_advance_pos(c, dt, i + 1);
    // the pair occupies one point
    assert(f.pos[i + 1] == f.pos[i]);
    if !at_left_border(f, i + 1) && !at_right_border(f, i + 1)
        && !sep_right(f, i + 1) && !sep_left(f, i + 1)
        && !meet_right(f, i + 1) && !meet_left(f, i + 1)
    {
        // nothing fired for `i+1`: it was already heading left, so the pair was
        // escorting *before* the step and the old coherence carries over
        assert(c.dir[i] == Dir::Left);
        assert(c.dir[i + 1] == Dir::Left);
        lemma_gap_unchanged_of_same_dir(c, i);
        assert(escorting(c, i));
        lemma_step_le_drone(c, i);
        lemma_drone_le_separation(c, i);
        assert(0 <= separation_time(c, i));
        lemma_separation_time_advance(c, dt, i);
        assert(0 <= separation_time(f, i));
    }
}

/// **Escorts stay coherent across a step.**
///
/// Coherence concerns drone `i` alone, so the proof is a case analysis on which
/// branch of `new_dir` fired for it: a border event, a separation, or a meet with
/// the right neighbour each settle the sign immediately, and the two remaining
/// branches go through the workhorse above.
///
/// `Dpss/Coherence.lean`, `DPSS.Config.escortsCoherent_step`.
pub proof fn lemma_escorts_coherent_step(c: Snapshot)
    requires inv(c)
    ensures escorts_coherent(spec_step(c))
{
    let f = flown(c);
    let dt = time_to_next_event(c);
    lemma_step_nonneg(c);
    assert forall|i: int|
        0 <= i && i + 1 < c.n && #[trigger] escorting(spec_step(c), i)
            implies 0 <= separation_time(spec_step(c), i) by
    {
        lemma_segment_width(c, i);
        lemma_left_end_nonneg(c, i);
        lemma_common_le_perimeter(c, i);
        lemma_common_is_next_left(c, i);
        lemma_advance_pos(c, dt, i);
        lemma_advance_pos(c, dt, i + 1);
        assert(spec_step(c).pos[i] == f.pos[i]);
        assert(spec_step(c).dir[i] == new_dir(f, i));
        assert(spec_step(c).dir[i + 1] == new_dir(f, i + 1));
        assert(co_located(f, i));
        assert(spec_step(c).pos[i] == f.pos[i]);
        assert(common_end(spec_step(c), i) == common_end(c, i));
        lemma_times_isign(common_end(c, i) - f.pos[i], new_dir(f, i));
        // the goal, with the product made linear
        assert(separation_time(spec_step(c), i)
            == (common_end(c, i) - f.pos[i]) * isign(new_dir(f, i)));
        // the seven branches of `new_dir`, in its own priority order
        if at_left_border(f, i) {
            // at 0 heading right: the boundary is ahead
            assert(f.pos[i] == 0);
            assert(new_dir(f, i) == Dir::Right);
            lemma_left_end_nonneg(c, i);
        } else if at_right_border(f, i) {
            // at the far end heading left: the boundary is behind
            assert(f.pos[i] == perimeter(f));
            assert(new_dir(f, i) == Dir::Left);
        } else if sep_right(f, i) {
            // exactly on the boundary: the deadline is zero
            assert(at_separation(f, i));
            assert(f.pos[i] == common_end(f, i));
        } else if sep_left(f, i) {
            // on its own left endpoint heading right: a whole segment to go
            assert(at_separation(f, i - 1));
            assert(f.pos[i - 1] == common_end(f, i - 1));
            assert(f.pos[i] == f.pos[i - 1]);
            lemma_common_is_next_left(c, i - 1);
            assert(new_dir(f, i) == Dir::Right);
        } else if meet_right(f, i) {
            // `escort_dir` points at the boundary, whichever side it is on
            assert(new_dir(f, i) == escort_dir(f, i));
        } else if meet_left(f, i) {
            // meeting its left neighbour, so it was already heading left
            assert(f.dir[i] == Dir::Left);
            assert(new_dir(f, i) == escort_dir_left(f, i));
            if !(f.pos[i] < left_end(f, i)) {
                lemma_common_le_pos_of_both_left(c, i);
            }
        } else {
            // nothing fired, so the heading is unchanged
            assert(new_dir(f, i) == f.dir[i]);
            if f.dir[i] == Dir::Left {
                lemma_common_le_pos_of_both_left(c, i);
            } else {
                // heading right with nothing due: the pair cannot be approaching,
                // so it was already escorting and the old deadline carries over
                assert(new_dir(f, i + 1) == Dir::Right);
                assert(f.dir[i + 1] == Dir::Right) by {
                    if f.dir[i + 1] == Dir::Left {
                        assert(approaching(f, i));
                        assert(meet_right(f, i));
                    }
                }
                assert(c.dir[i] == c.dir[i + 1]);
                lemma_gap_unchanged_of_same_dir(c, i);
                assert(escorting(c, i));
                lemma_step_le_drone(c, i);
                lemma_drone_le_separation(c, i);
                lemma_separation_time_advance(c, dt, i);
                lemma_times_isign(common_end(c, i) - c.pos[i], c.dir[i]);
            }
        }
    }
}

/// **Escorts are coherent in mid-step too** — after the flight, before the events.
///
/// The executable step passes through that configuration, so it has to satisfy the
/// standing conditions as well. An escorting pair in the flown configuration was
/// escorting before it, because the headings have not changed and a pair heading
/// the same way keeps its gap; and the deadline it was given has only been
/// consumed by `dt`.
pub proof fn lemma_escorts_coherent_flown(c: Snapshot)
    requires inv(c)
    ensures escorts_coherent(flown(c))
{
    let dt = time_to_next_event(c);
    lemma_step_nonneg(c);
    assert forall|i: int|
        0 <= i && i + 1 < c.n && #[trigger] escorting(flown(c), i)
            implies 0 <= separation_time(flown(c), i) by
    {
        assert(c.dir[i] == c.dir[i + 1]);
        lemma_gap_unchanged_of_same_dir(c, i);
        assert(escorting(c, i));
        lemma_step_le_drone(c, i);
        lemma_drone_le_separation(c, i);
        lemma_separation_time_advance(c, dt, i);
    }
}

} // verus!
