//! A co-located pair heading apart sits on the boundary it shares.
//!
//! **False of arbitrary well-formed configurations** — `Dpss/Counterexample.lean`
//! exhibits four drones stacked at one point, the two middle ones each escorting
//! the *outward* neighbour — so this is a reachability invariant, carried
//! separately from `inv` and preserved by a step.
//!
//! Mirrors `Dpss/Reachable.lean`.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::snapshot::Snapshot;
use crate::spec::model::*;
use crate::inv::*;
use crate::schedule::*;
use crate::geometry::*;
use crate::step_lemmas::*;

verus! {

/// **The transfer move.** A pair heading apart separates at rate 2, so if it is
/// still co-located after flying, the step took no time and the pair was already
/// co-located. The condition then carries straight over.
///
/// `Dpss/Reachable.lean`, `DPSS.Config.apart_transfer`.
pub proof fn lemma_apart_transfer(c: Snapshot, i: int)
    requires
        inv(c),
        apart_on_boundaries(c),
        0 <= i,
        i + 1 < c.n,
        c.dir[i] == Dir::Left,
        c.dir[i + 1] == Dir::Right,
        co_located(flown(c), i),
    ensures flown(c).pos[i] == common_end(c, i)
{
    let dt = time_to_next_event(c);
    lemma_step_nonneg(c);
    lemma_advance_gap(c, dt, i);
    lemma_advance_pos(c, dt, i);
    assert(sep_rate(c, i) == 2);
    // the gap grows at rate 2, so still being together forces both to be zero
    assert(gap(c, i) + 2 * dt == 0);
    assert(gap(c, i) >= 0);
    assert(dt == 0);
    assert(co_located(c, i));
}

/// **The condition is preserved by a step.**
///
/// Either a separation fired on one side or the other, which settles it outright,
/// or the pair was already heading apart before the step and the transfer move
/// applies.
///
/// `Dpss/Reachable.lean`, `DPSS.Config.apartOnBoundary_step`.
pub proof fn lemma_apart_on_boundaries_step(c: Snapshot)
    requires inv(c), apart_on_boundaries(c)
    ensures apart_on_boundaries(spec_step(c))
{
    let f = flown(c);
    let dt = time_to_next_event(c);
    lemma_step_nonneg(c);
    lemma_on_perimeter_step(c);
    lemma_adj_ordered_step(c);
    assert forall|i: int|
        0 <= i && i + 1 < c.n && #[trigger] co_located(spec_step(c), i)
            && spec_step(c).dir[i] == Dir::Left
            && spec_step(c).dir[i + 1] == Dir::Right
        implies spec_step(c).pos[i] == common_end(spec_step(c), i) by
    {
        lemma_segment_width(c, i);
        lemma_left_end_nonneg(c, i);
        lemma_common_le_perimeter(c, i);
        lemma_common_is_next_left(c, i);
        lemma_advance_pos(c, dt, i);
        lemma_advance_pos(c, dt, i + 1);
        assert(spec_step(c).pos[i] == f.pos[i]);
        assert(common_end(spec_step(c), i) == common_end(c, i));
        assert(co_located(f, i));
        assert(f.pos[i + 1] == f.pos[i]);
        assert(new_dir(f, i) == Dir::Left);
        assert(new_dir(f, i + 1) == Dir::Right);
        if sep_right(f, i) {
            // a separation on our side puts us on the boundary outright
            assert(at_separation(f, i));
        } else if sep_left(f, i + 1) {
            // and so does one on the neighbour's side
            assert(at_separation(f, i));
        } else {
            // neither separated, so the pair was already heading apart
            assert(f.dir[i] == Dir::Left);
            assert(f.dir[i + 1] == Dir::Right);
            lemma_apart_transfer(c, i);
        }
    }
}

/// **And therefore along a whole run.**
///
/// `Dpss/InductionStep.lean`, `DPSS.Config.apartOnBoundaries_run`.
pub proof fn lemma_apart_on_boundaries_run(c: Snapshot, k: nat)
    requires inv(c), apart_on_boundaries(c)
    ensures apart_on_boundaries(spec_run(c, k)), inv(spec_run(c, k))
    decreases k
{
    if k > 0 {
        lemma_apart_on_boundaries_run(c, (k - 1) as nat);
        lemma_apart_on_boundaries_step(spec_run(c, (k - 1) as nat));
        lemma_inv_step(spec_run(c, (k - 1) as nat));
    }
}

} // verus!
