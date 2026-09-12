//! Small facts about the generated specification.
//!
//! `spec fn`s carry no proof obligations, so a crate of nothing but generated
//! specifications verifies vacuously. These are the first real obligations: they
//! make "0 errors" mean something, and each one mirrors a theorem that
//! `Dpss/IntModel.lean` proves about the same definition.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::snapshot::Snapshot;
use crate::spec::model::*;

verus! {

/// A heading's velocity squares to one.
///
/// `Dpss/IntModel.lean`, `DPSS.Dir.isign_mul_self`.
pub proof fn lemma_isign_mul_self(d: Dir)
    ensures isign(d) * isign(d) == 1
{
    match d {
        Dir::Left => {},
        Dir::Right => {},
    }
}

/// A drone never stands still.
///
/// `Dpss/IntModel.lean`, `DPSS.Dir.isign_ne_zero`.
pub proof fn lemma_isign_ne_zero(d: Dir)
    ensures isign(d) != 0
{
    match d {
        Dir::Left => {},
        Dir::Right => {},
    }
}

/// **The rate a gap changes at is always even** — it is `-2`, `0` or `+2`.
///
/// This is the fact the whole integer model rests on: it is why an even gap stays
/// even, and therefore why `meet_time`'s division by two is exact.
///
/// `Dpss/IntModel.lean`, `DPSS.IntConfig.two_dvd_sepRate`.
pub proof fn lemma_sep_rate_even(c: Snapshot, i: int)
    ensures
        sep_rate(c, i) == -2 || sep_rate(c, i) == 0 || sep_rate(c, i) == 2,
        sep_rate(c, i) % 2 == 0,
{
    match c.dir[i] {
        Dir::Left => {
            match c.dir[i + 1] {
                Dir::Left => {},
                Dir::Right => {},
            }
        },
        Dir::Right => {
            match c.dir[i + 1] {
                Dir::Left => {},
                Dir::Right => {},
            }
        },
    }
}

/// An escorting pair has a zero separation rate, so it stays together — the
/// emergent escort, in the integer model.
///
/// `Dpss/Events.lean`, `DPSS.Config.sepRate_eq_zero_of_escorting`.
pub proof fn lemma_sep_rate_zero_of_escorting(c: Snapshot, i: int)
    requires escorting(c, i)
    ensures sep_rate(c, i) == 0
{
}

/// A separating pair sits on the boundary it shares, and that boundary is the
/// right-hand drone's own left endpoint.
///
/// `Dpss/Basic.lean`, `DPSS.rightEnd_eq_leftEnd_succ`.
pub proof fn lemma_common_end_is_next_left_end(c: Snapshot, i: int)
    ensures common_end(c, i) == left_end(c, i + 1)
{
}

} // verus!
