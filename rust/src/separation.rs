//! S3 — margined separation, executable.
//!
//! The Lean half is `Dpss/Separation.lean`. Same content, same structure: the
//! separation guarantee is the fence guarantee applied to the **excess
//! separation** `g - d`, with every vehicle quantity doubled because two drones
//! contribute to the gap.
//!
//! ## Why doubled, and why nothing else changes
//!
//! | | |
//! |---|---|
//! | `2*dmax` | both drones move, so the gap can shrink twice as fast |
//! | `2*turn` | both reversals may overshoot |
//! | `2*eps`  | both positions are sensed, so the gap carries twice the error |
//!
//! Nothing else differs, so `pair_to_fence` hands the pair conditions to
//! `fence::traj_ok` and the guarantee comes out of `fence::low_nonneg_at`. There
//! is no second induction in this file.
//!
//! ## The one thing separation has that fencing does not
//!
//! At a wall the drone must never arrive. Between drones the pair is *supposed*
//! to close — in DPSS a meet is the coordination mechanism — so the guarantee is
//! `d <= gap` with equality permitted, which is the fence's `0 <= p` shifted by
//! the standoff. `Dpss/Standoff.lean` proves that shift is a change of
//! coordinates rather than an approximation.

use vstd::prelude::*;
use crate::dir::Dir;
use crate::fence::*;

// `pair_vehicle`, `pair_leg_ok`, `pair_obs_ok`, `pair_safe` and
// `pair_traj_step_ok` are GENERATED from `Dpss/SeparationInt.lean` by
// `scripts/lean_to_verus.py` (S6d). `Dir::Left` means **closing** in all of
// them, mirroring the fence where left meant approaching the wall.
pub use crate::spec::separation_model::*;

verus! {

/// A sampled trajectory of one adjacent pair holding a standoff `d`.
///
/// `Dpss/Separation.lean`, `DPSS.Fence.PairTraj`.
pub open spec fn pair_traj_ok(
    v: Vehicle, d: int, margin: int,
    gap: spec_fn(nat) -> int, mode: spec_fn(nat) -> Dir,
    low: spec_fn(nat) -> int, obs: spec_fn(nat) -> int, req: spec_fn(nat) -> Dir,
) -> bool {
    &&& forall|k: nat| pair_obs_ok(v, #[trigger] obs(k), gap(k))
    &&& forall|k: nat| #[trigger] mode(k) == fence_dir(margin, obs(k) - d, req(k))
    &&& forall|k: nat| pair_leg_ok(v, gap(k), mode(k), #[trigger] low(k), gap((k + 1) as nat))
}

/// **The separation problem is the fence problem.**
///
/// `Dpss/Separation.lean`, `DPSS.Fence.PairTraj.toFence`.
pub proof fn pair_to_fence(
    v: Vehicle, d: int, margin: int,
    gap: spec_fn(nat) -> int, mode: spec_fn(nat) -> Dir,
    low: spec_fn(nat) -> int, obs: spec_fn(nat) -> int, req: spec_fn(nat) -> Dir,
)
    requires
        wf(v),
        pair_traj_ok(v, d, margin, gap, mode, low, obs, req),
    ensures
        traj_ok(pair_vehicle(v), margin,
            |k: nat| gap(k) - d, mode, |k: nat| low(k) - d, |k: nat| obs(k) - d, req),
{
    let p = |k: nat| gap(k) - d;
    let lw = |k: nat| low(k) - d;
    let ob = |k: nat| obs(k) - d;
    assert forall|k: nat| obs_ok(pair_vehicle(v), #[trigger] ob(k), p(k)) by {
        assert(pair_obs_ok(v, obs(k), gap(k)));
    }
    assert forall|k: nat| #[trigger] mode(k) == fence_dir(margin, ob(k), req(k)) by {
        assert(mode(k) == fence_dir(margin, obs(k) - d, req(k)));
    }
    assert forall|k: nat|
        leg_ok(pair_vehicle(v), p(k), mode(k), #[trigger] lw(k), p((k + 1) as nat)) by {
        assert(pair_leg_ok(v, gap(k), mode(k), low(k), gap((k + 1) as nat)));
    }
}

/// **Separation is maintained, between samples too.**
///
/// `low(k)` is the least gap over the whole leg, so this is a statement about
/// every instant. No induction here: it is `fence::low_nonneg_at` read through
/// the correspondence.
///
/// `Dpss/Separation.lean`, `DPSS.Fence.PairTraj.le_low` and `le_gap`.
pub proof fn pair_le_low(
    v: Vehicle, d: int, margin: int,
    gap: spec_fn(nat) -> int, mode: spec_fn(nat) -> Dir,
    low: spec_fn(nat) -> int, obs: spec_fn(nat) -> int, req: spec_fn(nat) -> Dir,
    k: nat,
)
    requires
        wf(v),
        2 * (v.dmax + v.turn + v.eps) <= margin,
        pair_traj_ok(v, d, margin, gap, mode, low, obs, req),
        pair_safe(v, d, gap(0), mode(0)),
    ensures
        d <= low(k),
        d <= gap(k),
{
    let vp = pair_vehicle(v);
    let p = |k: nat| gap(k) - d;
    let lw = |k: nat| low(k) - d;
    let ob = |k: nat| obs(k) - d;
    pair_to_fence(v, d, margin, gap, mode, low, obs, req);
    assert(wf(vp));
    assert(vp.dmax + vp.turn + vp.eps <= margin);
    assert(safe(vp, p(0), mode(0)));
    low_nonneg_at(vp, margin, p, mode, lw, ob, req, k);
    assert(0 <= lw(k));
    assert(0 <= p(k));
}

/// **`pair_traj_ok` is exactly that, at every sample.** As `traj_ok_iff_steps`,
/// and for the same reason: it is what licenses calling a finite evaluation of
/// `pair_traj_step_ok_ex` a check of `pair_traj_ok` on a prefix.
pub proof fn pair_traj_ok_iff_steps(
    v: Vehicle, d: int, margin: int,
    gap: spec_fn(nat) -> int, mode: spec_fn(nat) -> Dir,
    low: spec_fn(nat) -> int, obs: spec_fn(nat) -> int, req: spec_fn(nat) -> Dir,
)
    ensures
        pair_traj_ok(v, d, margin, gap, mode, low, obs, req) <==> (forall|k: nat|
            pair_traj_step_ok(v, d, margin, gap(k), #[trigger] mode(k), low(k), obs(k),
                req(k), gap((k + 1) as nat))),
{
    if pair_traj_ok(v, d, margin, gap, mode, low, obs, req) {
        assert forall|k: nat|
            pair_traj_step_ok(v, d, margin, gap(k), #[trigger] mode(k), low(k), obs(k),
                req(k), gap((k + 1) as nat)) by {
            assert(pair_obs_ok(v, obs(k), gap(k)));
            assert(mode(k) == fence_dir(margin, obs(k) - d, req(k)));
            assert(pair_leg_ok(v, gap(k), mode(k), low(k), gap((k + 1) as nat)));
        }
    }
    if (forall|k: nat| pair_traj_step_ok(v, d, margin, gap(k), #[trigger] mode(k), low(k),
            obs(k), req(k), gap((k + 1) as nat))) {
        assert forall|k: nat| pair_obs_ok(v, #[trigger] obs(k), gap(k)) by {
            assert(pair_traj_step_ok(v, d, margin, gap(k), mode(k), low(k), obs(k),
                req(k), gap((k + 1) as nat)));
        }
        assert forall|k: nat| #[trigger] mode(k) == fence_dir(margin, obs(k) - d, req(k)) by {
            assert(pair_traj_step_ok(v, d, margin, gap(k), mode(k), low(k), obs(k),
                req(k), gap((k + 1) as nat)));
        }
        assert forall|k: nat|
            pair_leg_ok(v, gap(k), mode(k), #[trigger] low(k), gap((k + 1) as nat)) by {
            assert(pair_traj_step_ok(v, d, margin, gap(k), mode(k), low(k), obs(k),
                req(k), gap((k + 1) as nat)));
        }
    }
}

// ---------------------------------------------------------------------------
// The pair spec predicates, executable. As in `fence.rs`: a specification never
// runs, so an `_ex` function proved equal to it is the only way a trace can
// exercise one.
// ---------------------------------------------------------------------------

/// `pair_obs_ok`, executable.
pub fn pair_obs_ok_ex(v: &VehicleEx, obs: i64, g: i64) -> (r: bool)
    requires
        v.bounded(),
        in_range(obs as int),
        in_range(g as int),
    ensures
        r == pair_obs_ok(v@, obs as int, g as int),
{
    -(2 * v.eps) <= obs - g && obs - g <= 2 * v.eps
}

/// `pair_leg_ok`, executable.
pub fn pair_leg_ok_ex(v: &VehicleEx, g: i64, m: Dir, low: i64, g_next: i64) -> (r: bool)
    requires
        v.bounded(),
        in_range(g as int),
        in_range(low as int),
        in_range(g_next as int),
    ensures
        r == pair_leg_ok(v@, g as int, m, low as int, g_next as int),
{
    low <= g && low <= g_next
        && (m != Dir::Left || g - 2 * v.dmax <= low)
        && (m != Dir::Right || g - 2 * v.turn <= low)
        && (m != Dir::Right || g <= g_next)
}

/// `pair_safe`, executable.
pub fn pair_safe_ex(v: &VehicleEx, d: i64, g: i64, m: Dir) -> (r: bool)
    requires
        v.bounded(),
        0 <= d <= 1_000_000_000,
        in_range(g as int),
    ensures
        r == pair_safe(v@, d as int, g as int, m),
{
    let c = if m == Dir::Left { 2 * (v.dmax + v.turn) } else { 2 * v.turn };
    d + c <= g
}

/// **One sample of `pair_traj_ok`, executable.**
pub fn pair_traj_step_ok_ex(
    v: &VehicleEx, d: i64, margin: i64,
    g: i64, m: Dir, low: i64, obs: i64, req: Dir, g_next: i64,
) -> (r: bool)
    requires
        v.bounded(),
        0 <= d <= 1_000_000_000,
        in_range(g as int),
        in_range(low as int),
        in_range(obs as int),
        in_range(obs as int - d as int),
        in_range(g_next as int),
    ensures
        r == pair_traj_step_ok(v@, d as int, margin as int, g as int, m, low as int,
            obs as int, req, g_next as int),
{
    pair_obs_ok_ex(v, obs, g)
        && m == separation_control(margin, obs, d, req)
        && pair_leg_ok_ex(v, g, m, low, g_next)
}

/// **The separation controller.** The pair keeps closing only while the observed
/// excess separation is above the margin.
///
/// `Dpss/Separation.lean`, the `control` field of `PairTraj`.
pub fn separation_control(margin: i64, gap_hat: i64, d: i64, req: Dir) -> (m: Dir)
    requires
        -1_000_000_000 <= gap_hat <= 1_000_000_000,
        0 <= d <= 1_000_000_000,
    ensures
        m == fence_dir(margin as int, gap_hat as int - d as int, req),
{
    fence_control(margin, gap_hat - d, req)
}

/// **The separation margin, computed.** Twice the fence margin, because two
/// drones contribute to every term.
pub fn pair_margin_ex(dmax: i64, turn: i64, eps: i64) -> (m: i64)
    requires
        0 <= dmax <= 1_000_000_000,
        0 <= turn <= 1_000_000_000,
        0 <= eps <= 1_000_000_000,
    ensures
        m as int == 2 * (dmax as int + turn as int + eps as int),
        0 <= m,
{
    2 * (dmax + turn + eps)
}

} // verus!
