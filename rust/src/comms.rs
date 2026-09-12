//! S5 — safety when the network degrades.
//!
//! The Lean half is `Dpss/Comms.lean`. Same three answers, and the first is
//! visible here rather than proved: **nothing in `fence.rs` mentions another
//! drone.** `fence_control` takes one number, its own observed position. A total
//! communications failure does not weaken the fence at all.
//!
//! What follows is the second answer — the exchange rate between staleness and
//! margin.
//!
//! ## Staleness is sensing error
//!
//! A drone holding a report of its neighbour taken `a` samples ago knows that
//! neighbour's position to within `eps + a*dmax`: the error when the report was
//! taken, plus the furthest the neighbour can have moved since. Adding its own
//! sensing error gives a gap estimate good to `2*eps + a*dmax`, so
//!
//! ```text
//! margin >= 2*(dmax + turn + eps) + a*dmax
//! ```
//!
//! One sample of staleness costs exactly one `dmax`. Delay and loss are the same
//! hypothesis, because a message lost is a message not yet arrived.
//!
//! ## Why this stays in integers
//!
//! `comms_pair_vehicle` puts the whole sensing term — own error, neighbour's
//! error, and drift — into one field, `2*eps + a*dmax`. Splitting it evenly
//! across the two drones would have introduced a division by two, which is
//! exact over the reals and not over the integers. Carrying the doubled quantity
//! is the same arithmetic and needs no rounding, so the Verus and Lean
//! statements are the same statement.
//!
//! ## The third answer is not here
//!
//! *After convergence, separation is maintained by geometry* is a fact about the
//! respaced segments of `Dpss/Standoff.lean`, and this crate implements the
//! point model. `separated_of_segments` below is the arithmetic core of it, which
//! is what a controller would actually check; the run-level statement stays in
//! Lean.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::fence::*;
use crate::separation::*;

verus! {

/// The vehicle a pair faces across a link at most `a` samples stale.
///
/// `Dpss/Comms.lean`, `DPSS.Fence.Vehicle.commsPair`. With `a == 0` this is
/// `pair_vehicle`, so this module generalizes `separation.rs` rather than
/// sitting beside it.
pub open spec fn comms_pair_vehicle(v: Vehicle, a: nat) -> Vehicle {
    Vehicle { dmax: 2 * v.dmax, turn: 2 * v.turn, eps: 2 * v.eps + a * v.dmax }
}

/// A fresh link is the S3 vehicle.
pub proof fn comms_pair_vehicle_zero(v: Vehicle)
    ensures comms_pair_vehicle(v, 0) == pair_vehicle(v),
{
}

/// What the network guarantees, and what the neighbour's airframe guarantees.
///
/// `Dpss/Comms.lean`, the link fields of `DPSS.Fence.CommsPair`.
pub open spec fn link_ok(
    v: Vehicle, a: nat,
    q: spec_fn(nat) -> int, rep: spec_fn(nat) -> int, src: spec_fn(nat) -> nat,
) -> bool {
    // the report we hold was taken at an earlier sample, and not long ago
    &&& forall|k: nat| #[trigger] src(k) <= k
    &&& forall|k: nat| k - #[trigger] src(k) <= a
    // it was accurate when it was taken
    &&& forall|k: nat| -v.eps <= #[trigger] rep(k) - q(src(k)) <= v.eps
    // and the neighbour cannot have moved faster than dmax per sample since
    &&& forall|j: nat, k: nat| #![trigger q(k), q(j)] j <= k
            ==> -((k - j) * v.dmax) <= q(k) - q(j) <= (k - j) * v.dmax
}

/// **Staleness is sensing error.** A report `a` samples old localizes the
/// neighbour to `eps + a*dmax`.
///
/// `Dpss/Comms.lean`, `DPSS.Fence.CommsPair.rep_error`.
pub proof fn rep_error(
    v: Vehicle, a: nat,
    q: spec_fn(nat) -> int, rep: spec_fn(nat) -> int, src: spec_fn(nat) -> nat,
    k: nat,
)
    requires
        v.wf(),
        link_ok(v, a, q, rep, src),
    ensures
        -(v.eps + a * v.dmax) <= rep(k) - q(k) <= v.eps + a * v.dmax,
{
    assert(src(k) <= k);
    assert(k - src(k) <= a);
    assert(-((k - src(k)) * v.dmax) <= q(k) - q(src(k)) <= (k - src(k)) * v.dmax);
    assert((k - src(k)) * v.dmax <= a * v.dmax) by (nonlinear_arith)
        requires k - src(k) <= a, 0 <= v.dmax;
    assert(-v.eps <= rep(k) - q(src(k)) <= v.eps);
}

/// A pair across a link: the physical motion, what the drone knows, and what the
/// controller does with it.
///
/// The gap is `q(k) - p(k)`; it is not carried separately.
pub open spec fn comms_ok(
    v: Vehicle, a: nat, d: int, margin: int,
    p: spec_fn(nat) -> int, q: spec_fn(nat) -> int,
    low: spec_fn(nat) -> int, mode: spec_fn(nat) -> Dir, req: spec_fn(nat) -> Dir,
    phat: spec_fn(nat) -> int, rep: spec_fn(nat) -> int, src: spec_fn(nat) -> nat,
) -> bool {
    &&& link_ok(v, a, q, rep, src)
    &&& forall|k: nat| -v.eps <= #[trigger] phat(k) - p(k) <= v.eps
    &&& forall|k: nat| #[trigger] mode(k) == fence_dir(margin, rep(k) - phat(k) - d, req(k))
    &&& forall|k: nat| pair_leg_ok(v, q(k) - p(k), mode(k), #[trigger] low(k),
            q((k + 1) as nat) - p((k + 1) as nat))
}

/// **The link is a fence problem.** The same map as `pair_to_fence`, with the
/// staleness folded into the vehicle's sensing term.
///
/// `Dpss/Comms.lean`, `DPSS.Fence.CommsPair.toFence`.
pub proof fn comms_to_fence(
    v: Vehicle, a: nat, d: int, margin: int,
    p: spec_fn(nat) -> int, q: spec_fn(nat) -> int,
    low: spec_fn(nat) -> int, mode: spec_fn(nat) -> Dir, req: spec_fn(nat) -> Dir,
    phat: spec_fn(nat) -> int, rep: spec_fn(nat) -> int, src: spec_fn(nat) -> nat,
)
    requires
        v.wf(),
        comms_ok(v, a, d, margin, p, q, low, mode, req, phat, rep, src),
    ensures
        traj_ok(comms_pair_vehicle(v, a), margin,
            |k: nat| q(k) - p(k) - d, mode, |k: nat| low(k) - d,
            |k: nat| rep(k) - phat(k) - d, req),
{
    let vc = comms_pair_vehicle(v, a);
    let pp = |k: nat| q(k) - p(k) - d;
    let lw = |k: nat| low(k) - d;
    let ob = |k: nat| rep(k) - phat(k) - d;
    assert forall|k: nat| obs_ok(vc, #[trigger] ob(k), pp(k)) by {
        rep_error(v, a, q, rep, src, k);
        assert(-v.eps <= phat(k) - p(k) <= v.eps);
    }
    assert forall|k: nat| #[trigger] mode(k) == fence_dir(margin, ob(k), req(k)) by {
        assert(mode(k) == fence_dir(margin, rep(k) - phat(k) - d, req(k)));
    }
    assert forall|k: nat|
        leg_ok(vc, pp(k), mode(k), #[trigger] lw(k), pp((k + 1) as nat)) by {
        assert(pair_leg_ok(v, q(k) - p(k), mode(k), low(k),
            q((k + 1) as nat) - p((k + 1) as nat)));
    }
}

/// **Separation survives a degraded network.**
///
/// One extra sample of staleness costs exactly one `dmax` of margin, and nothing
/// else changes — no extra vehicle hypothesis, no second induction.
///
/// `Dpss/Comms.lean`, `DPSS.Fence.CommsPair.le_low` and `le_gap`.
pub proof fn comms_le_low(
    v: Vehicle, a: nat, d: int, margin: int,
    p: spec_fn(nat) -> int, q: spec_fn(nat) -> int,
    low: spec_fn(nat) -> int, mode: spec_fn(nat) -> Dir, req: spec_fn(nat) -> Dir,
    phat: spec_fn(nat) -> int, rep: spec_fn(nat) -> int, src: spec_fn(nat) -> nat,
    k: nat,
)
    requires
        v.wf(),
        2 * (v.dmax + v.turn + v.eps) + a * v.dmax <= margin,
        comms_ok(v, a, d, margin, p, q, low, mode, req, phat, rep, src),
        d + comms_pair_vehicle(v, a).clearance(mode(0)) <= q(0) - p(0),
    ensures
        d <= low(k),
        d <= q(k) - p(k),
{
    let vc = comms_pair_vehicle(v, a);
    let pp = |k: nat| q(k) - p(k) - d;
    let lw = |k: nat| low(k) - d;
    let ob = |k: nat| rep(k) - phat(k) - d;
    comms_to_fence(v, a, d, margin, p, q, low, mode, req, phat, rep, src);
    assert(vc.wf());
    assert(vc.dmax + vc.turn + vc.eps <= margin);
    assert(safe(vc, pp(0), mode(0)));
    low_nonneg_at(vc, margin, pp, mode, lw, ob, req, k);
    assert(0 <= lw(k));
    assert(0 <= pp(k));
}

/// **Two drones in their own segments are separated**, with no observation, no
/// message and no controller. The arithmetic core of the third answer: when the
/// segments are laid out with a buffer of exactly `d`, confinement *is*
/// separation.
///
/// `Dpss/Comms.lean`, `DPSS.Config.separated_of_segments`.
pub proof fn separated_of_segments(d: int, right_i: int, left_next: int, x: int, y: int)
    requires
        right_i + d == left_next,
        x <= right_i,
        left_next <= y,
    ensures
        d <= y - x,
{
}

// ---------------------------------------------------------------------------
// The link predicates, executable.
//
// `link_ok` is on the same list as `leg_ok` and `traj_ok`: it never runs, so a
// wrong clause in it would make `comms_le_low` true about a network nobody has.
// The `_ex` functions below are proved to compute its clauses, one sample and
// one pair of samples at a time, so a trace can exercise them.
// ---------------------------------------------------------------------------

/// The per-sample clauses of `link_ok`: the report we hold was taken earlier,
/// not long ago, and was accurate when taken.
pub open spec fn link_step_ok(v: Vehicle, a: nat, k: nat, src_k: nat, rep_k: int,
    q_src: int) -> bool
{
    &&& src_k <= k
    &&& k - src_k <= a
    &&& -v.eps <= rep_k - q_src <= v.eps
}

/// The two-sample clause: the neighbour cannot have moved faster than `dmax`
/// per sample.
pub open spec fn drift_ok(v: Vehicle, j: nat, k: nat, q_j: int, q_k: int) -> bool {
    j <= k ==> -((k - j) * v.dmax) <= q_k - q_j <= (k - j) * v.dmax
}

/// **`link_ok` is exactly those two, quantified.** The statement that licenses
/// reading a finite evaluation of the `_ex` functions below as a check of
/// `link_ok` on a prefix.
pub proof fn link_ok_iff_steps(
    v: Vehicle, a: nat,
    q: spec_fn(nat) -> int, rep: spec_fn(nat) -> int, src: spec_fn(nat) -> nat,
)
    ensures
        link_ok(v, a, q, rep, src) <==> (
            (forall|k: nat| link_step_ok(v, a, k, #[trigger] src(k), rep(k), q(src(k))))
            && (forall|j: nat, k: nat| #![trigger q(k), q(j)]
                    drift_ok(v, j, k, q(j), q(k)))),
{
    if link_ok(v, a, q, rep, src) {
        assert forall|k: nat|
            link_step_ok(v, a, k, #[trigger] src(k), rep(k), q(src(k))) by {
            assert(src(k) <= k);
            assert(k - src(k) <= a);
            assert(-v.eps <= rep(k) - q(src(k)) <= v.eps);
        }
    }
    if ((forall|k: nat| link_step_ok(v, a, k, #[trigger] src(k), rep(k), q(src(k))))
        && (forall|j: nat, k: nat| #![trigger q(k), q(j)] drift_ok(v, j, k, q(j), q(k)))) {
        assert forall|k: nat| #[trigger] src(k) <= k by {
            assert(link_step_ok(v, a, k, src(k), rep(k), q(src(k))));
        }
        assert forall|k: nat| k - #[trigger] src(k) <= a by {
            assert(link_step_ok(v, a, k, src(k), rep(k), q(src(k))));
        }
        assert forall|k: nat| -v.eps <= #[trigger] rep(k) - q(src(k)) <= v.eps by {
            assert(link_step_ok(v, a, k, src(k), rep(k), q(src(k))));
        }
    }
}

/// `link_step_ok`, executable.
pub fn link_step_ok_ex(v: &VehicleEx, a: u64, k: u64, src_k: u64, rep_k: i64,
    q_src: i64) -> (r: bool)
    requires
        v.bounded(),
        a <= 1_000_000,
        k <= 1_000_000,
        src_k <= 1_000_000,
        in_range(rep_k as int),
        in_range(q_src as int),
    ensures
        r == link_step_ok(v@, a as nat, k as nat, src_k as nat, rep_k as int,
            q_src as int),
{
    src_k <= k && k - src_k <= a
        && -v.eps <= rep_k - q_src && rep_k - q_src <= v.eps
}

/// `drift_ok`, executable.
pub fn drift_ok_ex(v: &VehicleEx, j: u64, k: u64, q_j: i64, q_k: i64) -> (r: bool)
    requires
        v.bounded(),
        j <= 1_000_000,
        k <= 1_000_000,
        in_range(q_j as int),
        in_range(q_k as int),
    ensures
        r == drift_ok(v@, j as nat, k as nat, q_j as int, q_k as int),
{
    if j > k {
        true
    } else {
        let span: i64 = (k - j) as i64;
        proof {
            assert(0 <= span * v.dmax) by (nonlinear_arith)
                requires 0 <= span, 0 <= v.dmax;
            assert(span * v.dmax <= 1_000_000 * 1_000_000_000) by (nonlinear_arith)
                requires 0 <= span <= 1_000_000, 0 <= v.dmax <= 1_000_000_000;
        }
        let bound: i64 = span * v.dmax;
        -bound <= q_k - q_j && q_k - q_j <= bound
    }
}

/// **One sample of `comms_ok`, in the quantities a trace carries.** A trace
/// records the gap and the gap *estimate*; the drone's own position and its
/// neighbour's are behind them. This is what `comms_ok` says about the sample
/// when it is read in those terms.
pub open spec fn comms_step_ok(
    v: Vehicle, a: nat, d: int, margin: int,
    g: int, obs: int, m: Dir, low: int, req: Dir, g_next: int,
) -> bool {
    &&& -(2 * v.eps + a * v.dmax) <= obs - g <= 2 * v.eps + a * v.dmax
    &&& m == fence_dir(margin, obs - d, req)
    &&& pair_leg_ok(v, g, m, low, g_next)
}

/// **`comms_ok` implies it, at every sample.** One direction only, and
/// deliberately: the gap and its estimate do not determine the two positions
/// behind them, so nothing recovers `link_ok` from a trace. What a trace can
/// check is that it satisfies what `comms_ok` entails, and this is that.
pub proof fn comms_ok_implies_steps(
    v: Vehicle, a: nat, d: int, margin: int,
    p: spec_fn(nat) -> int, q: spec_fn(nat) -> int,
    low: spec_fn(nat) -> int, mode: spec_fn(nat) -> Dir, req: spec_fn(nat) -> Dir,
    phat: spec_fn(nat) -> int, rep: spec_fn(nat) -> int, src: spec_fn(nat) -> nat,
    k: nat,
)
    requires
        v.wf(),
        comms_ok(v, a, d, margin, p, q, low, mode, req, phat, rep, src),
    ensures
        comms_step_ok(v, a, d, margin, q(k) - p(k), rep(k) - phat(k), mode(k), low(k),
            req(k), q((k + 1) as nat) - p((k + 1) as nat)),
{
    rep_error(v, a, q, rep, src, k);
    assert(-v.eps <= phat(k) - p(k) <= v.eps);
    assert(mode(k) == fence_dir(margin, rep(k) - phat(k) - d, req(k)));
    assert(pair_leg_ok(v, q(k) - p(k), mode(k), low(k),
        q((k + 1) as nat) - p((k + 1) as nat)));
}

/// `comms_step_ok`, executable.
pub fn comms_step_ok_ex(
    v: &VehicleEx, a: u64, d: i64, margin: i64,
    g: i64, obs: i64, m: Dir, low: i64, req: Dir, g_next: i64,
) -> (r: bool)
    requires
        v.bounded(),
        a <= 1_000_000,
        0 <= d <= 1_000_000_000,
        in_range(g as int),
        in_range(obs as int),
        in_range(obs as int - d as int),
        in_range(low as int),
        in_range(g_next as int),
    ensures
        r == comms_step_ok(v@, a as nat, d as int, margin as int, g as int, obs as int,
            m, low as int, req, g_next as int),
{
    proof {
        assert(0 <= a * v.dmax) by (nonlinear_arith)
            requires 0 <= a, 0 <= v.dmax;
        assert(a * v.dmax <= 1_000_000 * 1_000_000_000) by (nonlinear_arith)
            requires 0 <= a <= 1_000_000, 0 <= v.dmax <= 1_000_000_000;
    }
    let slack: i64 = 2 * v.eps + (a as i64) * v.dmax;
    -slack <= obs - g && obs - g <= slack
        && m == separation_control(margin, obs, d, req)
        && pair_leg_ok_ex(v, g, m, low, g_next)
}

/// **The separation margin under a stale link, computed.**
pub fn comms_margin_ex(dmax: i64, turn: i64, eps: i64, age: i64) -> (m: i64)
    requires
        0 <= dmax <= 1_000_000_000,
        0 <= turn <= 1_000_000_000,
        0 <= eps <= 1_000_000_000,
        0 <= age <= 1_000_000,
    ensures
        m as int == 2 * (dmax as int + turn as int + eps as int) + age as int * dmax as int,
        0 <= m,
{
    proof {
        assert(age * dmax <= 1_000_000 * 1_000_000_000) by (nonlinear_arith)
            requires 0 <= age <= 1_000_000, 0 <= dmax <= 1_000_000_000;
        assert(0 <= age * dmax) by (nonlinear_arith)
            requires 0 <= age, 0 <= dmax;
    }
    2 * (dmax + turn + eps) + age * dmax
}

} // verus!
