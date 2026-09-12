/-
# DPSS — S3: margined separation, at the controller

`Dpss/Fence.lean` guarantees one drone stays clear of a wall. This file
guarantees two drones stay clear of *each other*, under the same kind of sampled
controller and the same kind of vehicle contract.

## The thing that makes separation harder than fencing

At a wall, the drone must never arrive. Between drones it is the opposite: in
DPSS a **meet is the coordination mechanism**, and the pair is *supposed* to
close. So the guarantee cannot be "never get near"; it has to be

    d ≤ gap        with equality permitted and expected,

which is exactly the fence's `0 ≤ p` shifted by the standoff. `Dpss/Standoff.lean`
proved that shift is a change of coordinates rather than an approximation;
this file cashes it in.

## The result, and why it is not a new argument

Write `g` for the gap and `g - d` for the **excess separation**. Then:

* the pair closes at most `2·Dmax` per sample period — both drones move;
* a pair commanded apart may still close by `2·turn` before the reversals take;
* sensing the gap costs `2·eps`, since both positions are observed.

Every quantity doubles, and nothing else changes. So the separation controller
**is** the fence controller applied to the excess separation with a doubled
vehicle, and `PairTraj.toFence` says so by construction: the guarantee comes out
of `Fence.Traj.low_nonneg` rather than out of a second induction.

> **Theorem.** With `M ≥ 2·(Dmax + turn + eps)`, a pair whose controller stops
> the approach at observed excess `M` never closes below the standoff `d` — at
> any instant, not only at the samples.

And the margin is sharp, for the same reason and by the same transfer.

## What this does *not* cover

This is a **pair** under its own controller, as the fence was a **drone** under
its own controller. That a whole team running DPSS maintains the invariant is
the model-level half of S3, which needs the scheduler correspondence
`Dpss/Standoff.lean` deliberately left open.
-/

import Dpss.Fence

set_option linter.style.header false

namespace DPSS
namespace Fence

variable {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-! ## The doubled vehicle

Two drones contribute to every quantity that matters to the gap. -/

/-- The vehicle contract as the *gap* sees it: both drones move, both drones
turn, both drones are observed. -/
def Vehicle.pair (V : Vehicle α) : Vehicle α where
  Dmax := 2 * V.Dmax
  turn := 2 * V.turn
  eps := 2 * V.eps
  Dmax_nonneg := by have := V.Dmax_nonneg; linarith
  turn_nonneg := by have := V.turn_nonneg; linarith
  eps_nonneg := by have := V.eps_nonneg; linarith

@[simp] theorem Vehicle.pair_Dmax (V : Vehicle α) : V.pair.Dmax = 2 * V.Dmax := rfl
@[simp] theorem Vehicle.pair_turn (V : Vehicle α) : V.pair.turn = 2 * V.turn := rfl
@[simp] theorem Vehicle.pair_eps (V : Vehicle α) : V.pair.eps = 2 * V.eps := rfl

/-! ## A sampled pair

`Dir.left` means **closing** — the pair is approaching — mirroring the fence,
where left meant approaching the wall. `Dir.right` means holding station or
separating. -/

/-- A sampled trajectory of one adjacent pair, holding a standoff `d`. -/
structure PairTraj {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (V : Vehicle α) (d M : α) where
  /-- The true gap at each sample. -/
  gap : ℕ → α
  /-- The least gap reached on the leg from sample `k` to sample `k+1`. -/
  low : ℕ → α
  /-- The gap as observed. -/
  obs : ℕ → α
  /-- Whether the pair is closing on that leg. -/
  mode : ℕ → Dir
  /-- What the surveillance algorithm asked for. -/
  req : ℕ → Dir
  /-- Both positions are sensed, so the gap costs twice the error. -/
  obs_close : ∀ k, |obs k - gap k| ≤ 2 * V.eps
  /-- The controller stops the approach at observed excess `M`. -/
  control : ∀ k, mode k = fenceDir M (obs k - d) (req k)
  low_le_gap : ∀ k, low k ≤ gap k
  low_le_next : ∀ k, low k ≤ gap (k + 1)
  /-- **Closing rate.** Both drones move, so the gap shrinks by at most `2·Dmax`. -/
  close_leg : ∀ k, mode k = Dir.left → gap k - 2 * V.Dmax ≤ low k
  /-- **Turn allowance.** Both reversals may overshoot. -/
  turn_leg : ∀ k, mode k = Dir.right → gap k - 2 * V.turn ≤ low k
  /-- **Reversals complete within a period.** A pair no longer closing has not
  lost gap by the next sample. -/
  hold_leg : ∀ k, mode k = Dir.right → gap k ≤ gap (k + 1)

namespace PairTraj

variable {V : Vehicle α} {d M : α}

/-- **The separation problem is the fence problem.** Excess separation `g - d`
plays the part of position, and the doubled vehicle plays the part of the
vehicle. Every field is the corresponding field, shifted. -/
def toFence (P : PairTraj V d M) : Traj V.pair M where
  p := fun k => P.gap k - d
  d := P.mode
  low := fun k => P.low k - d
  obs := fun k => P.obs k - d
  req := P.req
  obs_close := by
    intro k
    have h : P.obs k - d - (P.gap k - d) = P.obs k - P.gap k := by ring
    rw [h]
    simpa using P.obs_close k
  control := P.control
  low_le_pos := by intro k; have := P.low_le_gap k; linarith
  low_le_next := by intro k; have := P.low_le_next k; linarith
  left_leg := by
    intro k hm
    have := P.close_leg k hm
    simp only [Vehicle.pair_Dmax]
    linarith
  turn_leg := by
    intro k hm
    have := P.turn_leg k hm
    simp only [Vehicle.pair_turn]
    linarith
  hold_leg := by
    intro k hm
    have := P.hold_leg k hm
    linarith

/-- The invariant: the pair holds the standoff plus the clearance its current
mode requires. -/
def Safe (P : PairTraj V d M) (k : ℕ) : Prop :=
  d + V.pair.margin (P.mode k) ≤ P.gap k

theorem safe_iff_fence (P : PairTraj V d M) (k : ℕ) :
    P.Safe k ↔ P.toFence.Safe k := by
  unfold Safe Traj.Safe toFence
  constructor <;> intro h <;> simp only at h ⊢ <;> linarith

/-- **Separation is maintained, between samples too.**

`low k` is the least gap over the whole leg, so this is a statement about every
instant. No induction is done here: it is `Fence.Traj.low_nonneg` read through
the correspondence. -/
theorem le_low (hM : 2 * (V.Dmax + V.turn + V.eps) ≤ M) {P : PairTraj V d M}
    (h0 : P.Safe 0) (k : ℕ) : d ≤ P.low k := by
  have hMp : V.pair.Dmax + V.pair.turn + V.pair.eps ≤ M := by
    simp only [Vehicle.pair_Dmax, Vehicle.pair_turn, Vehicle.pair_eps]
    linarith
  have h := Traj.low_nonneg hMp ((P.safe_iff_fence 0).mp h0) k
  have hlow : P.toFence.low k = P.low k - d := rfl
  rw [hlow] at h
  linarith

/-- And at every sample. -/
theorem le_gap (hM : 2 * (V.Dmax + V.turn + V.eps) ≤ M) {P : PairTraj V d M}
    (h0 : P.Safe 0) (k : ℕ) : d ≤ P.gap k :=
  le_trans (le_low hM h0 k) (P.low_le_gap k)

end PairTraj

/-! ## The separation margin is sharp too

The transfer runs in both directions: a fence trajectory that crosses becomes a
pair that closes inside the standoff. So none of the six terms in
`2·(Dmax + turn + eps)` is slack either. -/

/-- The correspondence, backwards. -/
def Traj.toPair (d : α) {V : Vehicle α} {M : α} (T : Traj V.pair M) :
    PairTraj V d M where
  gap := fun k => T.p k + d
  low := fun k => T.low k + d
  obs := fun k => T.obs k + d
  mode := T.d
  req := T.req
  obs_close := by
    intro k
    have h : T.obs k + d - (T.p k + d) = T.obs k - T.p k := by ring
    rw [h]
    simpa using T.obs_close k
  control := by
    intro k
    have h : T.obs k + d - d = T.obs k := by ring
    rw [h]
    exact T.control k
  low_le_gap := by intro k; have := T.low_le_pos k; linarith
  low_le_next := by intro k; have := T.low_le_next k; linarith
  close_leg := by
    intro k hm
    have := T.left_leg k hm
    simp only [Vehicle.pair_Dmax] at this
    linarith
  turn_leg := by
    intro k hm
    have := T.turn_leg k hm
    simp only [Vehicle.pair_turn] at this
    linarith
  hold_leg := by
    intro k hm
    have := T.hold_leg k hm
    linarith

/-- **The separation margin `2·(Dmax + turn + eps)` is exactly tight.** For any
smaller `M` there is a pair obeying the whole vehicle contract, starting with
the clearance the invariant asks for, that closes inside the standoff. -/
theorem pair_margin_sharp (V : Vehicle ℝ) (d M : ℝ) (hD : 0 < V.Dmax)
    (hlt : M < 2 * (V.Dmax + V.turn + V.eps)) :
    ∃ (P : PairTraj V d M) (k : ℕ), P.Safe 0 ∧ P.low k < d := by
  have hDp : 0 < V.pair.Dmax := by simp only [Vehicle.pair_Dmax]; linarith
  have hltp : M < V.pair.Dmax + V.pair.turn + V.pair.eps := by
    simp only [Vehicle.pair_Dmax, Vehicle.pair_turn, Vehicle.pair_eps]
    linarith
  obtain ⟨T, k, h0, hk⟩ := margin_sharp V.pair M hDp hltp
  refine ⟨T.toPair d, k, ?_, ?_⟩
  · change d + V.pair.margin (T.d 0) ≤ T.p 0 + d
    have : V.pair.margin (T.d 0) ≤ T.p 0 := h0
    linarith
  · change T.low k + d < d
    linarith

end Fence
end DPSS
