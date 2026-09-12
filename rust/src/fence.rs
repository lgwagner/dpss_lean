//! S2 — the margined fence, executable.
//!
//! The Lean half is `Dpss/Fence.lean`. This is the same theorem in Verus, plus
//! the controller that runs.
//!
//! Everything else in this crate is about the *team*. This module is about one
//! drone and one wall, which is what makes it drone-level: the guarantee needs
//! no coordination, no global scheduler, and no knowledge of where anyone else
//! is. The controller sees one number — its own observed position — and decides.
//!
//! ## Why this fits Verus without a fight
//!
//! The rest of the crate needed the scaling argument of `Dpss/IntModel.lean` to
//! get real-valued statements into integers. Here nothing needs scaling: the
//! vehicle contract is stated in *displacement per sample period*, not in speed,
//! so every quantity — `dmax`, `turn`, `eps`, `margin`, position — is a length,
//! all in the same units. There is no division anywhere in the argument and
//! therefore nothing to be inexact about.
//!
//! ## What is proved here
//!
//! | | |
//! |---|---|
//! | `fence_control` | the executable controller computes `fence_dir` |
//! | `margin_ex` | the margin is computed without overflow |
//! | `safe_step` | one sample preserves the invariant |
//! | `safe_at` | therefore it holds at every sample, by induction |
//! | `low_nonneg_at` | therefore the drone never crosses the fence, *between* samples too |
//!
//! The trajectory is an infinite sequence of samples, as in Lean — `spec_fn` over
//! `nat`, not a bounded `Seq` — so `safe_at` is the same induction as
//! `DPSS.Fence.Traj.safe_all` rather than a horizon-limited approximation of it.

use vstd::prelude::*;
use crate::dir::Dir;

verus! {

/// What the proof needs to know about the airframe. Specification-only, like
/// `Snapshot`: these are measured numbers, not program state.
///
/// `Dpss/Fence.lean`, `DPSS.Fence.Vehicle`.
pub struct Vehicle {
    /// The furthest the drone travels in one sample period.
    pub dmax: int,
    /// Overshoot allowance for a commanded reversal.
    pub turn: int,
    /// Position sensing error bound.
    pub eps: int,
}

impl Vehicle {
    pub open spec fn wf(self) -> bool {
        &&& 0 <= self.dmax
        &&& 0 <= self.turn
        &&& 0 <= self.eps
    }

    /// The clearance a drone must hold from the fence, given its heading.
    ///
    /// `Dpss/Fence.lean`, `DPSS.Fence.Vehicle.margin`.
    pub open spec fn clearance(self, d: Dir) -> int {
        if d == Dir::Left { self.dmax + self.turn } else { self.turn }
    }
}

/// The fence controller, as a specification.
///
/// `Dpss/Fence.lean`, `DPSS.Fence.fenceDir`.
pub open spec fn fence_dir(margin: int, p_hat: int, req: Dir) -> Dir {
    if p_hat <= margin { Dir::Right } else { req }
}

/// The invariant.
///
/// `Dpss/Fence.lean`, `DPSS.Fence.Traj.Safe`.
pub open spec fn safe(v: Vehicle, p: int, d: Dir) -> bool {
    v.clearance(d) <= p
}

/// The vehicle contract for one leg: `low` is the lowest position reached
/// between this sample and the next, a leftward leg travels at most `dmax`, a
/// reversal costs at most `turn`, and a reversal completes within the period.
///
/// `Dpss/Fence.lean`, the `left_leg` / `turn_leg` / `hold_leg` fields of
/// `DPSS.Fence.Traj`.
pub open spec fn leg_ok(v: Vehicle, p: int, d: Dir, low: int, p_next: int) -> bool {
    &&& low <= p
    &&& low <= p_next
    &&& (d == Dir::Left ==> p - v.dmax <= low)
    &&& (d == Dir::Right ==> p - v.turn <= low)
    &&& (d == Dir::Right ==> p <= p_next)
}

/// Sensing is accurate to `eps`.
pub open spec fn obs_ok(v: Vehicle, obs: int, p: int) -> bool {
    -v.eps <= obs - p <= v.eps
}

/// **A safe sample leaves at least the turn allowance at the next one.**
///
/// `Dpss/Fence.lean`, `DPSS.Fence.Traj.turn_le_pos_succ`.
pub proof fn turn_le_next(v: Vehicle, p: int, d: Dir, low: int, p_next: int)
    requires
        v.wf(),
        safe(v, p, d),
        leg_ok(v, p, d, low, p_next),
    ensures
        v.turn <= p_next,
{
}

/// **The drone is on the safe side of the fence for the whole leg**, not merely
/// at its endpoints.
///
/// `Dpss/Fence.lean`, the body of `DPSS.Fence.Traj.low_nonneg`.
pub proof fn low_nonneg(v: Vehicle, p: int, d: Dir, low: int, p_next: int)
    requires
        v.wf(),
        safe(v, p, d),
        leg_ok(v, p, d, low, p_next),
    ensures
        0 <= low,
{
}

/// **One sample preserves the invariant.**
///
/// `Dpss/Fence.lean`, `DPSS.Fence.Traj.safe_succ`.
pub proof fn safe_step(
    v: Vehicle, margin: int,
    p: int, d: Dir, low: int, p_next: int, obs: int, req: Dir,
)
    requires
        v.wf(),
        v.dmax + v.turn + v.eps <= margin,
        safe(v, p, d),
        leg_ok(v, p, d, low, p_next),
        obs_ok(v, obs, p_next),
    ensures
        safe(v, p_next, fence_dir(margin, obs, req)),
{
    turn_le_next(v, p, d, low, p_next);
}

/// A sampled trajectory, as five functions of the sample index. Infinite, as in
/// Lean — the fields of `DPSS.Fence.Traj`, one per argument.
pub open spec fn traj_ok(
    v: Vehicle, margin: int,
    p: spec_fn(nat) -> int, d: spec_fn(nat) -> Dir,
    low: spec_fn(nat) -> int, obs: spec_fn(nat) -> int, req: spec_fn(nat) -> Dir,
) -> bool {
    &&& forall|k: nat| obs_ok(v, #[trigger] obs(k), p(k))
    &&& forall|k: nat| #[trigger] d(k) == fence_dir(margin, obs(k), req(k))
    &&& forall|k: nat| leg_ok(v, p(k), d(k), #[trigger] low(k), p((k + 1) as nat))
}

/// **The invariant holds at every sample.**
///
/// `Dpss/Fence.lean`, `DPSS.Fence.Traj.safe_all`.
pub proof fn safe_at(
    v: Vehicle, margin: int,
    p: spec_fn(nat) -> int, d: spec_fn(nat) -> Dir,
    low: spec_fn(nat) -> int, obs: spec_fn(nat) -> int, req: spec_fn(nat) -> Dir,
    k: nat,
)
    requires
        v.wf(),
        v.dmax + v.turn + v.eps <= margin,
        traj_ok(v, margin, p, d, low, obs, req),
        safe(v, p(0), d(0)),
    ensures
        safe(v, p(k), d(k)),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        safe_at(v, margin, p, d, low, obs, req, j);
        assert(leg_ok(v, p(j), d(j), low(j), p((j + 1) as nat)));
        assert(obs_ok(v, obs(k), p(k)));
        assert(d(k) == fence_dir(margin, obs(k), req(k)));
        safe_step(v, margin, p(j), d(j), low(j), p(k), obs(k), req(k));
    }
}

/// **The drone never crosses the fence**, at any instant — `low` is the lowest
/// position of an entire leg, so this covers the time between samples.
///
/// `Dpss/Fence.lean`, `DPSS.Fence.Traj.low_nonneg`.
pub proof fn low_nonneg_at(
    v: Vehicle, margin: int,
    p: spec_fn(nat) -> int, d: spec_fn(nat) -> Dir,
    low: spec_fn(nat) -> int, obs: spec_fn(nat) -> int, req: spec_fn(nat) -> Dir,
    k: nat,
)
    requires
        v.wf(),
        v.dmax + v.turn + v.eps <= margin,
        traj_ok(v, margin, p, d, low, obs, req),
        safe(v, p(0), d(0)),
    ensures
        0 <= low(k),
        0 <= p(k),
{
    safe_at(v, margin, p, d, low, obs, req, k);
    assert(leg_ok(v, p(k), d(k), low(k), p((k + 1) as nat)));
    low_nonneg(v, p(k), d(k), low(k), p((k + 1) as nat));
}

/// **The controller.** One comparison, no arithmetic, and therefore nothing to
/// overflow. `req` is whatever heading the surveillance algorithm asked for; an
/// observation at or below the margin overrides it.
///
/// `Dpss/Fence.lean`, `DPSS.Fence.fenceDir`.
pub fn fence_control(margin: i64, p_hat: i64, req: Dir) -> (d: Dir)
    ensures
        d == fence_dir(margin as int, p_hat as int, req),
{
    if p_hat <= margin {
        Dir::Right
    } else {
        req
    }
}

/// **The margin, computed from the vehicle numbers.** This is the one place the
/// fence does arithmetic, so it is the one place overflow could bite. The bounds
/// are generous — a metre-scale vehicle would use millimetres and still have
/// room for a perimeter around the earth.
pub fn margin_ex(dmax: i64, turn: i64, eps: i64) -> (m: i64)
    requires
        0 <= dmax <= 1_000_000_000,
        0 <= turn <= 1_000_000_000,
        0 <= eps <= 1_000_000_000,
    ensures
        m as int == dmax as int + turn as int + eps as int,
        0 <= m,
{
    dmax + turn + eps
}

} // verus!
