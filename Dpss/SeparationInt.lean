/-
# DPSS — S6d: the pair and the link at `ℤ`, in the shape the Rust has

`Dpss/FenceInt.lean` does this for the fence. This file does it for the two
things built on top of it: a pair holding a standoff (`Dpss/Separation.lean`)
and a pair across a stale link (`Dpss/Comms.lean`).

The definitions below are unbundled and `ℤ`-valued, as the Rust's are, and
`scripts/lean_to_verus.py` translates them into
`rust/src/spec/separation_model.rs`. So nothing here is typed twice, and a
change to a predicate reaches Verus by regeneration rather than by someone
remembering.

## Why the pair predicates exist at all, when the fence already covers them

They are what `rust/src/separation.rs` and `rust/src/comms.rs` are *written in*,
and in Verus that matters: a proof about a pair has to say `pair_leg_ok` before
it can say, via `pair_to_fence`, that the pair is a drone at a fence with a
doubled vehicle. The theorems in this file are the Lean side of that step —
each says the pair predicate **is** the fence predicate on the doubled vehicle,
which is the content of `PairTraj.toFence` and `CommsPair.toFence` stated about
the unbundled definitions the generator can read.

## What is deliberately not here

`linkStepOk` and `driftOk` — the two clauses of `link_ok` that mention the
sample index. Both subtract sample indices (`k - src k`, `k - j`), and in Lean
those are **ℕ**, where subtraction truncates at zero; in Verus they are `int`,
where it does not. The two agree exactly when the accompanying `src k ≤ k` or
`j ≤ k` holds, which `link_ok` does state — but a translator that mapped `ℕ`
subtraction to integer subtraction would be unsound in general, and this one
refuses rather than guesses. They stay hand-written in `rust/src/comms.rs`, with
the Lean statement beside them in `DPSS.Fence.CommsPair`.
-/

import Dpss.FenceInt
import Dpss.Comms

set_option linter.style.header false

namespace DPSS
namespace FenceInt

/-! ## The doubled vehicle

`rust/src/spec/separation_model.rs`, `pair_vehicle` and `comms_pair_vehicle`. -/

/-- The vehicle as the *gap* sees it: both drones move, both turn, both are
sensed. `Dpss/Separation.lean`, `DPSS.Fence.Vehicle.pair`. -/
def pairVehicle (v : Vehicle) : Vehicle := ⟨2 * v.dmax, 2 * v.turn, 2 * v.eps⟩

/-- And across a link at most `a` samples stale, the neighbour may have drifted
`a · dmax` since the report. `Dpss/Comms.lean`, `DPSS.Fence.Vehicle.commsPair`. -/
def commsPairVehicle (v : Vehicle) (a : ℕ) : Vehicle :=
  ⟨2 * v.dmax, 2 * v.turn, 2 * v.eps + (a : ℤ) * v.dmax⟩

@[simp] theorem pairVehicle_dmax (v : Vehicle) : (pairVehicle v).dmax = 2 * v.dmax := rfl
@[simp] theorem pairVehicle_turn (v : Vehicle) : (pairVehicle v).turn = 2 * v.turn := rfl
@[simp] theorem pairVehicle_eps (v : Vehicle) : (pairVehicle v).eps = 2 * v.eps := rfl

@[simp] theorem commsPairVehicle_dmax (v : Vehicle) (a : ℕ) :
    (commsPairVehicle v a).dmax = 2 * v.dmax := rfl
@[simp] theorem commsPairVehicle_turn (v : Vehicle) (a : ℕ) :
    (commsPairVehicle v a).turn = 2 * v.turn := rfl
@[simp] theorem commsPairVehicle_eps (v : Vehicle) (a : ℕ) :
    (commsPairVehicle v a).eps = 2 * v.eps + (a : ℤ) * v.dmax := rfl

/-- **The unbundled doubling is the bundled one.** `Vehicle.pair` of
`Dpss/Separation.lean` carries its non-negativity proofs; this says the numbers
are the same. -/
theorem pairVehicle_toFence (v : Vehicle) (h : v.wf) (h' : (pairVehicle v).wf) :
    (pairVehicle v).toFence h' = (v.toFence h).pair := rfl

theorem commsPairVehicle_toFence (v : Vehicle) (a : ℕ) (h : v.wf)
    (h' : (commsPairVehicle v a).wf) :
    (commsPairVehicle v a).toFence h' = (v.toFence h).commsPair a := rfl

theorem pairVehicle_wf {v : Vehicle} (h : v.wf) : (pairVehicle v).wf := by
  obtain ⟨hd, ht, he⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

theorem commsPairVehicle_wf {v : Vehicle} (a : ℕ) (h : v.wf) :
    (commsPairVehicle v a).wf := by
  obtain ⟨hd, ht, he⟩ := h
  have ha : (0 : ℤ) ≤ (a : ℤ) * v.dmax := mul_nonneg (Int.natCast_nonneg a) hd
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

/-! ## The pair

`rust/src/spec/separation_model.rs`, `pair_obs_ok`, `pair_leg_ok`, `pair_safe`
and `pair_traj_step_ok`. `Dir.left` means **closing**, mirroring the fence where
left meant approaching the wall. -/

/-- Both positions are sensed, so the gap carries twice the error. -/
def pairObsOk (v : Vehicle) (obs g : ℤ) : Prop :=
  -(2 * v.eps) ≤ obs - g ∧ obs - g ≤ 2 * v.eps

/-- The vehicle contract for one leg of a pair: the gap can shrink by `2·dmax`
while they close, by `2·turn` on the reversals, and a pair no longer closing has
not lost gap by the next sample. -/
def pairLegOk (v : Vehicle) (g : ℤ) (m : Dir) (low gNext : ℤ) : Prop :=
  low ≤ g ∧ low ≤ gNext ∧
    (m = Dir.left → g - 2 * v.dmax ≤ low) ∧
    (m = Dir.right → g - 2 * v.turn ≤ low) ∧
    (m = Dir.right → g ≤ gNext)

/-- The invariant: the pair holds the standoff plus the clearance its mode
requires. -/
def pairSafe (v : Vehicle) (d g : ℤ) (m : Dir) : Prop :=
  d + Vehicle.clearance (pairVehicle v) m ≤ g

/-- One sample's worth of the pair trajectory conditions. -/
def pairTrajStepOk (v : Vehicle) (d margin g : ℤ) (m : Dir) (low obs : ℤ)
    (req : Dir) (gNext : ℤ) : Prop :=
  pairObsOk v obs g ∧ m = fenceDir margin (obs - d) req ∧ pairLegOk v g m low gNext

/-! ## The link

`rust/src/spec/separation_model.rs`, `comms_step_ok` — one sample of `comms_ok`
read in the quantities a trace carries. The clauses of `link_ok` that mention
the sample index are not here; the header says why. -/

/-- One sample across a stale link. The sensing allowance is the pair's, plus
one `dmax` for every sample of age. -/
def commsStepOk (v : Vehicle) (a : ℕ) (d margin g obs : ℤ) (m : Dir) (low : ℤ)
    (req : Dir) (gNext : ℤ) : Prop :=
  -(2 * v.eps + (a : ℤ) * v.dmax) ≤ obs - g ∧
    obs - g ≤ 2 * v.eps + (a : ℤ) * v.dmax ∧
    m = fenceDir margin (obs - d) req ∧
    pairLegOk v g m low gNext

/-! ## Each pair predicate is the fence predicate on the doubled vehicle

This is `PairTraj.toFence` and `CommsPair.toFence`, stated about the unbundled
definitions. Every proof is `Iff.rfl` up to the arithmetic of doubling — which
is the point: the pair layer adds no content, only coordinates. -/

theorem pairObsOk_iff (v : Vehicle) (h : v.wf) (h' : (pairVehicle v).wf)
    (obs g : ℤ) :
    pairObsOk v obs g ↔ Fence.ObsOk ((v.toFence h).pair) obs g := by
  rw [← pairVehicle_toFence v h h']
  unfold pairObsOk Fence.ObsOk
  simp [Vehicle.toFence]

theorem pairLegOk_iff (v : Vehicle) (h : v.wf) (h' : (pairVehicle v).wf)
    (g : ℤ) (m : Dir) (low gNext : ℤ) :
    pairLegOk v g m low gNext ↔ Fence.LegOk ((v.toFence h).pair) g m low gNext := by
  rw [← pairVehicle_toFence v h h']
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩

theorem commsObsOk_iff (v : Vehicle) (a : ℕ) (h : v.wf)
    (h' : (commsPairVehicle v a).wf) (obs g : ℤ) :
    (-(2 * v.eps + (a : ℤ) * v.dmax) ≤ obs - g ∧
      obs - g ≤ 2 * v.eps + (a : ℤ) * v.dmax) ↔
      Fence.ObsOk ((v.toFence h).commsPair a) obs g := by
  rw [← commsPairVehicle_toFence v a h h']
  unfold Fence.ObsOk
  simp [Vehicle.toFence]

/-- And the pair invariant is the fence invariant on the doubled vehicle. -/
theorem pairSafe_iff (v : Vehicle) (h : v.wf) (h' : (pairVehicle v).wf)
    (d g : ℤ) (m : Dir) :
    pairSafe v d g m ↔ d + ((v.toFence h).pair).margin m ≤ g := by
  rw [← pairVehicle_toFence v h h']
  unfold pairSafe
  rw [Vehicle.clearance_eq _ h']

end FenceInt
end DPSS
