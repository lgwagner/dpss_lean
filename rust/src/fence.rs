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
//! | `traj_ok_iff_steps` | `traj_ok` is `traj_step_ok` at every sample |
//! | `*_ex` | executable functions proved to compute `obs_ok`, `leg_ok`, `safe` and `traj_step_ok` |
//!
//! The `_ex` functions are S6b. A specification never executes, so no test can
//! exercise one, and a wrong specification supporting a flawless proof is the
//! failure mode this project has actually had (`INSIGHTS.md` §1). An `_ex`
//! function carries an `ensures` clause saying it returns exactly the spec
//! predicate's truth value, so running it on a trace runs the specification
//! itself.
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

/// **One sample's worth of `traj_ok`.** The body of the three quantifiers,
/// with no quantifier around it — so it is a statement about numbers that an
/// executable function can be proved to compute.
///
/// `Dpss/Fence.lean`, one `k` of `DPSS.FenceInt.trajOk`.
pub open spec fn traj_step_ok(
    v: Vehicle, margin: int,
    p: int, d: Dir, low: int, obs: int, req: Dir, p_next: int,
) -> bool {
    &&& obs_ok(v, obs, p)
    &&& d == fence_dir(margin, obs, req)
    &&& leg_ok(v, p, d, low, p_next)
}

/// **`traj_ok` is exactly that, at every sample.** Stated and proved rather
/// than asserted in a comment, because it is what licenses checking a finite
/// trace against `traj_step_ok_ex` below and calling the result a check of
/// `traj_ok` on that prefix.
pub proof fn traj_ok_iff_steps(
    v: Vehicle, margin: int,
    p: spec_fn(nat) -> int, d: spec_fn(nat) -> Dir,
    low: spec_fn(nat) -> int, obs: spec_fn(nat) -> int, req: spec_fn(nat) -> Dir,
)
    ensures
        traj_ok(v, margin, p, d, low, obs, req) <==> (forall|k: nat|
            traj_step_ok(v, margin, p(k), #[trigger] d(k), low(k), obs(k), req(k),
                p((k + 1) as nat))),
{
    if traj_ok(v, margin, p, d, low, obs, req) {
        assert forall|k: nat|
            traj_step_ok(v, margin, p(k), #[trigger] d(k), low(k), obs(k), req(k),
                p((k + 1) as nat)) by {
            assert(obs_ok(v, obs(k), p(k)));
            assert(d(k) == fence_dir(margin, obs(k), req(k)));
            assert(leg_ok(v, p(k), d(k), low(k), p((k + 1) as nat)));
        }
    }
    if (forall|k: nat| traj_step_ok(v, margin, p(k), #[trigger] d(k), low(k), obs(k),
            req(k), p((k + 1) as nat))) {
        assert forall|k: nat| obs_ok(v, #[trigger] obs(k), p(k)) by {
            assert(traj_step_ok(v, margin, p(k), d(k), low(k), obs(k), req(k),
                p((k + 1) as nat)));
        }
        assert forall|k: nat| #[trigger] d(k) == fence_dir(margin, obs(k), req(k)) by {
            assert(traj_step_ok(v, margin, p(k), d(k), low(k), obs(k), req(k),
                p((k + 1) as nat)));
        }
        assert forall|k: nat|
            leg_ok(v, p(k), d(k), #[trigger] low(k), p((k + 1) as nat)) by {
            assert(traj_step_ok(v, margin, p(k), d(k), low(k), obs(k), req(k),
                p((k + 1) as nat)));
        }
    }
}

// ---------------------------------------------------------------------------
// The spec predicates, executable.
//
// `leg_ok`, `obs_ok` and `traj_ok` are SPECIFICATIONS: they never run, so no
// test can ever exercise them, and a wrong one would make every theorem in this
// file true about the wrong system. That is the one failure mode this project
// has actually had (INSIGHTS.md §1), and it is the reason for what follows.
//
// Each `_ex` function below is an ordinary executable Rust function whose
// `ensures` clause says it returns exactly the truth value of the corresponding
// spec predicate. Verus proves that. So running one of them on a trace is
// running the specification -- not a hand transcription of it that might have
// drifted.
// ---------------------------------------------------------------------------

/// The airframe numbers, executable. `Vehicle` itself is `int`-valued and
/// therefore ghost; this is the same three numbers in machine integers, with
/// `@` the map between them.
pub struct VehicleEx {
    pub dmax: i64,
    pub turn: i64,
    pub eps: i64,
}

impl View for VehicleEx {
    type V = Vehicle;

    open spec fn view(&self) -> Vehicle {
        Vehicle { dmax: self.dmax as int, turn: self.turn as int, eps: self.eps as int }
    }
}

/// The range every quantity is kept inside, so that the executable arithmetic
/// cannot overflow. Generous: a metre-scale vehicle working in millimetres has
/// room for a perimeter around the earth.
pub open spec fn in_range(x: int) -> bool {
    -1_000_000_000 <= x <= 1_000_000_000
}

impl VehicleEx {
    pub open spec fn bounded(self) -> bool {
        &&& 0 <= self.dmax <= 1_000_000_000
        &&& 0 <= self.turn <= 1_000_000_000
        &&& 0 <= self.eps <= 1_000_000_000
    }

    /// `Vehicle::wf`, executable.
    pub fn wf_ex(&self) -> (r: bool)
        ensures r == self@.wf(),
    {
        0 <= self.dmax && 0 <= self.turn && 0 <= self.eps
    }

    /// `Vehicle::clearance`, executable.
    pub fn clearance_ex(&self, d: Dir) -> (c: i64)
        requires self.bounded(),
        ensures c as int == self@.clearance(d),
    {
        if d == Dir::Left { self.dmax + self.turn } else { self.turn }
    }
}

/// `obs_ok`, executable.
pub fn obs_ok_ex(v: &VehicleEx, obs: i64, p: i64) -> (r: bool)
    requires
        v.bounded(),
        in_range(obs as int),
        in_range(p as int),
    ensures
        r == obs_ok(v@, obs as int, p as int),
{
    -v.eps <= obs - p && obs - p <= v.eps
}

/// `leg_ok`, executable.
pub fn leg_ok_ex(v: &VehicleEx, p: i64, d: Dir, low: i64, p_next: i64) -> (r: bool)
    requires
        v.bounded(),
        in_range(p as int),
        in_range(low as int),
        in_range(p_next as int),
    ensures
        r == leg_ok(v@, p as int, d, low as int, p_next as int),
{
    low <= p && low <= p_next
        && (d != Dir::Left || p - v.dmax <= low)
        && (d != Dir::Right || p - v.turn <= low)
        && (d != Dir::Right || p <= p_next)
}

/// `safe`, executable.
pub fn safe_ex(v: &VehicleEx, p: i64, d: Dir) -> (r: bool)
    requires
        v.bounded(),
        in_range(p as int),
    ensures
        r == safe(v@, p as int, d),
{
    v.clearance_ex(d) <= p
}

/// **One sample of `traj_ok`, executable.** With `traj_ok_iff_steps` above,
/// running this at every sample of a trace *is* checking `traj_ok` on that
/// prefix of it.
pub fn traj_step_ok_ex(
    v: &VehicleEx, margin: i64,
    p: i64, d: Dir, low: i64, obs: i64, req: Dir, p_next: i64,
) -> (r: bool)
    requires
        v.bounded(),
        in_range(p as int),
        in_range(low as int),
        in_range(obs as int),
        in_range(p_next as int),
    ensures
        r == traj_step_ok(v@, margin as int, p as int, d, low as int, obs as int, req,
            p_next as int),
{
    obs_ok_ex(v, obs, p)
        && d == fence_control(margin, obs, req)
        && leg_ok_ex(v, p, d, low, p_next)
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
