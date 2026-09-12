//! The scheduler's two guarantees, and what they buy.
//!
//! Everything about a step rests on two facts: the step is never negative, and it
//! never overshoots any drone's own deadline. Those are proved here, and the
//! invariant preservation in `step_lemmas.rs` is arithmetic on top of them.
//!
//! Mirrors `Dpss/NextEvent.lean`'s `timeToNextEvent_le` and
//! `timeToNextEvent_nonneg`.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::view::View;
use crate::spec::model::*;
use crate::inv::*;

verus! {

/// **The step never overshoots a drone's own deadline.**
///
/// `Dpss/NextEvent.lean`, `DPSS.Config.timeToNextEvent_le`.
pub proof fn lemma_min_deadline_le(c: View, m: int, i: int)
    requires 0 <= i < m
    ensures min_deadline(c, m) <= drone_next_time(c, i)
    decreases m
{
    if m <= 1 {
    } else if i < m - 1 {
        lemma_min_deadline_le(c, m - 1, i);
    }
}

pub proof fn lemma_step_le_drone(c: View, i: int)
    requires 0 <= i < c.n
    ensures time_to_next_event(c) <= drone_next_time(c, i)
{
    lemma_min_deadline_le(c, c.n, i);
}

/// A drone's own deadline never exceeds its border deadline — the border is always
/// one of the candidates minimised over.
pub proof fn lemma_drone_le_border(c: View, i: int)
    ensures drone_next_time(c, i) <= border_time(c, i)
{
}

/// And for an approaching pair, its meeting time is a candidate too.
pub proof fn lemma_drone_le_meet(c: View, i: int)
    requires 0 <= i, i + 1 < c.n, approaching(c, i)
    ensures drone_next_time(c, i) <= meet_time(c, i)
{
}

/// And for an escorting pair, its separation time.
pub proof fn lemma_drone_le_separation(c: View, i: int)
    requires 0 <= i, i + 1 < c.n, escorting(c, i)
    ensures drone_next_time(c, i) <= separation_time(c, i)
{
    // an escorting pair heads the same way, so it is not approaching
    assert(!approaching(c, i));
}

/// **The step is never negative.**
///
/// Each candidate deadline is nonnegative: a border deadline because the drone is
/// on the perimeter, a meeting time because the pair is ordered, a separation time
/// because escort coherence says so.
///
/// `Dpss/NextEvent.lean`, `DPSS.Config.timeToNextEvent_nonneg`.
pub proof fn lemma_drone_next_time_nonneg(c: View, i: int)
    requires inv(c), 0 <= i < c.n
    ensures 0 <= drone_next_time(c, i)
{
    assert(0 <= c.pos[i] <= perimeter(c));
    assert(0 <= border_time(c, i)) by {
        match c.dir[i] {
            Dir::Left => {},
            Dir::Right => {},
        }
    }
    if i + 1 < c.n {
        assert(0 <= gap(c, i));
        assert(gap(c, i) % 2 == 0);
        assert(0 <= meet_time(c, i)) by (nonlinear_arith)
            requires 0 <= gap(c, i), meet_time(c, i) == gap(c, i) / 2;
        if escorting(c, i) {
            assert(0 <= separation_time(c, i));
        }
    }
}

pub proof fn lemma_min_deadline_nonneg(c: View, m: int)
    requires inv(c), 0 < m <= c.n
    ensures 0 <= min_deadline(c, m)
    decreases m
{
    if m <= 1 {
        lemma_drone_next_time_nonneg(c, 0);
    } else {
        lemma_min_deadline_nonneg(c, m - 1);
        lemma_drone_next_time_nonneg(c, m - 1);
    }
}

pub proof fn lemma_step_nonneg(c: View)
    requires inv(c)
    ensures 0 <= time_to_next_event(c)
{
    lemma_min_deadline_nonneg(c, c.n);
}

} // verus!
