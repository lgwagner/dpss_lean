//! The scaled geometry.
//!
//! Facts about where the segment boundaries are. In the real model these are
//! divisions by `n` and mostly trivial; here they are products `2*k*i`, so they are
//! **nonlinear** and Z3 needs them stated once rather than rediscovered at every
//! use.
//!
//! Mirrors the endpoint lemmas of `Dpss/Basic.lean`.

use vstd::prelude::*;
use crate::view::View;
use crate::spec::model::*;

verus! {

/// No segment starts before the perimeter does.
///
/// `Dpss/Basic.lean`, `DPSS.leftEnd_nonneg`.
pub proof fn lemma_left_end_nonneg(c: View, i: int)
    requires c.k > 0, 0 <= i
    ensures 0 <= left_end(c, i)
{
    assert(2 * c.k * i >= 0) by (nonlinear_arith)
        requires c.k > 0, i >= 0;
}

/// Every segment is nondegenerate: it has width `2*k`.
///
/// `Dpss/Basic.lean`, `DPSS.leftEnd_lt_rightEnd` and `rightEnd_sub_leftEnd`.
pub proof fn lemma_segment_width(c: View, i: int)
    ensures
        right_end(c, i) - left_end(c, i) == 2 * c.k,
        c.k > 0 ==> left_end(c, i) < common_end(c, i),
{
    assert(2 * c.k * (i + 1) - 2 * c.k * i == 2 * c.k) by (nonlinear_arith);
}

/// No segment ends after the perimeter does.
///
/// `Dpss/Basic.lean`, `DPSS.rightEnd_le_one`.
pub proof fn lemma_common_le_perimeter(c: View, i: int)
    requires c.k > 0, 0 <= i, i + 1 <= c.n
    ensures common_end(c, i) <= perimeter(c)
{
    assert(2 * c.k * (i + 1) <= 2 * c.k * c.n) by (nonlinear_arith)
        requires c.k > 0, i + 1 <= c.n;
}

/// Boundaries increase along the team.
pub proof fn lemma_common_lt_common_next(c: View, i: int)
    requires c.k > 0
    ensures common_end(c, i) < common_end(c, i + 1)
{
    assert(2 * c.k * (i + 1) < 2 * c.k * (i + 1 + 1)) by (nonlinear_arith)
        requires c.k > 0;
}

/// A drone's own left endpoint is the boundary it shares with the drone to its
/// left, and its right endpoint the boundary it shares with the one to its right.
///
/// `Dpss/Basic.lean`, `DPSS.rightEnd_eq_leftEnd_succ`.
pub proof fn lemma_common_is_next_left(c: View, i: int)
    ensures common_end(c, i) == left_end(c, i + 1)
{
}

} // verus!
