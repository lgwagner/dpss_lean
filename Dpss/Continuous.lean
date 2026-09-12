/-
# DPSS — S4: where `Dmax` comes from

`Dpss/Fence.lean` guarantees a drone stays clear of a wall, **given** three
numbers: a displacement bound `Dmax`, a turn allowance `turn`, and a sensing
error `eps`. Taking `Dmax` as a hypothesis is what made that result cheap, and
the honest statement has always been that the guarantee is conditional on a
number someone else measures.

This file stops `Dmax` being a hypothesis.

## What is derived, and what is not

Given a trajectory that is **Lipschitz with constant `V`** — a speed bound, the
one number every airframe report contains — and a sample period `Δt`:

    Dmax = V · Δt.

That is `Vehicle.ofSpeed`, and `Flight.toTraj` builds a genuine `Fence.Traj` out
of a continuous trajectory, so `flight_nonneg` concludes `0 ≤ x t` **at every
real instant `t`**, with no sampling in the statement at all.

What is *not* derived, and should not be:

* the **turn allowance** — how far a drone commanded to reverse still drifts
  the wrong way. That is a statement about control authority, not about speed: a
  fast drone with strong actuators has a small `turn`, a slow one with weak
  actuators a large one, and no speed bound distinguishes them.
* **that a reversal completes within a sample period.** Same reason, and it is
  the clause without which there is no fence at all — a drone that loses ground
  on every rightward leg walks out of any margin.

Both stay as hypotheses on `Flight`, where an engineer can see exactly what the
vehicle is being asked to do.

## The low-water mark, and why there is no analysis in the fence proof

`Flight.low k` is `sInf` of the image of the leg. The infimum exists because the
Lipschitz bound bounds the leg below; it does not need to be *attained*, so no
compactness or extreme-value argument appears. That single definition is what
lets a statement quantified over all real instants be proved by the discrete
induction in `Dpss/Fence.lean` — the continuous content of the whole result is
the two `csInf` lemmas below, plus `lipschitz_of_deriv` — the one appeal to the
mean value theorem on this whole track.
-/

import Dpss.Fence
import Mathlib.Analysis.Calculus.MeanValue

set_option linter.style.header false

namespace DPSS
namespace Fence

open Set

/-! ## The vehicle, from a speed bound -/

/-- **The displacement bound, derived.** A drone that never exceeds speed `V`
travels at most `V · Δt` between samples taken `Δt` apart. -/
noncomputable def Vehicle.ofSpeed (V dt turnA eps : ℝ) (hV : 0 ≤ V) (hdt : 0 ≤ dt)
    (ht : 0 ≤ turnA) (he : 0 ≤ eps) : Vehicle ℝ where
  Dmax := V * dt
  turn := turnA
  eps := eps
  Dmax_nonneg := mul_nonneg hV hdt
  turn_nonneg := ht
  eps_nonneg := he

@[simp] theorem Vehicle.ofSpeed_Dmax (V dt turnA eps : ℝ) (hV hdt ht he) :
    (Vehicle.ofSpeed V dt turnA eps hV hdt ht he).Dmax = V * dt := rfl

@[simp] theorem Vehicle.ofSpeed_turn (V dt turnA eps : ℝ) (hV hdt ht he) :
    (Vehicle.ofSpeed V dt turnA eps hV hdt ht he).turn = turnA := rfl

@[simp] theorem Vehicle.ofSpeed_eps (V dt turnA eps : ℝ) (hV hdt ht he) :
    (Vehicle.ofSpeed V dt turnA eps hV hdt ht he).eps = eps := rfl

/-! ## The speed bound, in the calculus sense

`Flight` asks for a Lipschitz bound, because that is the weakest hypothesis the
argument needs and it holds of trajectories that are not differentiable. A
vehicle model normally supplies a bound on the *derivative* instead. The mean
value theorem converts one to the other, and this is the only place in the
safety track where any analysis is used. -/

/-- **A bound on speed is a Lipschitz bound.** Mathlib's mean value theorem,
specialized to a real trajectory. -/
theorem lipschitz_of_deriv {x v : ℝ → ℝ} {V : ℝ}
    (hd : ∀ t, HasDerivAt x (v t) t) (hb : ∀ t, |v t| ≤ V) (s t : ℝ) :
    |x t - x s| ≤ V * |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := x) (f' := v) (s := Set.univ) (C := V)
    (fun y _ => (hd y).hasDerivWithinAt)
    (fun y _ => by simpa [Real.norm_eq_abs] using hb y)
    convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa [Real.norm_eq_abs] using h

/-! ## A continuous flight under the fence controller -/

/-- The `k`-th sample instant. -/
noncomputable def sampleTime (t₀ dt : ℝ) (k : ℕ) : ℝ := t₀ + (k : ℝ) * dt

theorem sampleTime_le_succ {t₀ dt : ℝ} (hdt : 0 ≤ dt) (k : ℕ) :
    sampleTime t₀ dt k ≤ sampleTime t₀ dt (k + 1) := by
  unfold sampleTime
  push_cast
  nlinarith

/-- A continuous trajectory of one drone, sampled every `dt`, flown under the
fence controller.

The Lipschitz bound is the kinematics; `turn_leg` and `hold_leg` are the two
control-authority assumptions that a speed bound cannot supply. -/
structure Flight (V dt turnA eps M : ℝ) where
  /-- Where the drone is, at every real instant. -/
  x : ℝ → ℝ
  /-- The first sample. -/
  t₀ : ℝ
  /-- What the sensor reported at each sample. -/
  obs : ℕ → ℝ
  /-- What the surveillance algorithm asked for at each sample. -/
  req : ℕ → Dir
  dt_nonneg : 0 ≤ dt
  /-- **The speed bound.** -/
  lip : ∀ s t : ℝ, |x t - x s| ≤ V * |t - s|
  /-- Sensing is accurate to `eps`. -/
  obs_close : ∀ k, |obs k - x (sampleTime t₀ dt k)| ≤ eps
  /-- **Turn allowance.** A drone commanded right loses at most `turnA` over the
  leg. Control authority, not kinematics. -/
  turn_leg : ∀ k, fenceDir M (obs k) (req k) = Dir.right →
    ∀ t ∈ Icc (sampleTime t₀ dt k) (sampleTime t₀ dt (k + 1)),
      x (sampleTime t₀ dt k) - turnA ≤ x t
  /-- **Reversals complete within a period.** Likewise. -/
  hold_leg : ∀ k, fenceDir M (obs k) (req k) = Dir.right →
    x (sampleTime t₀ dt k) ≤ x (sampleTime t₀ dt (k + 1))

namespace Flight

variable {V dt turnA eps M : ℝ}

/-- The positions attained on the `k`-th leg. -/
noncomputable def leg (F : Flight V dt turnA eps M) (k : ℕ) : Set ℝ :=
  F.x '' Icc (sampleTime F.t₀ dt k) (sampleTime F.t₀ dt (k + 1))

theorem leg_nonempty (F : Flight V dt turnA eps M) (k : ℕ) : (F.leg k).Nonempty :=
  ⟨F.x (sampleTime F.t₀ dt k),
    ⟨sampleTime F.t₀ dt k, ⟨le_rfl, sampleTime_le_succ F.dt_nonneg k⟩, rfl⟩⟩

/-- **The Lipschitz bound, on a leg.** Everything continuous about this file is
in this lemma and the two `csInf` facts that follow it. -/
theorem le_of_mem_leg (F : Flight V dt turnA eps M) (hV : 0 ≤ V) (k : ℕ)
    {y : ℝ} (hy : y ∈ F.leg k) :
    F.x (sampleTime F.t₀ dt k) - V * dt ≤ y := by
  obtain ⟨t, ⟨hl, hr⟩, rfl⟩ := hy
  have hb := F.lip (sampleTime F.t₀ dt k) t
  have habs : |t - sampleTime F.t₀ dt k| = t - sampleTime F.t₀ dt k :=
    abs_of_nonneg (by linarith)
  rw [habs] at hb
  have hdist : t - sampleTime F.t₀ dt k ≤ dt := by
    have := hr
    unfold sampleTime at this ⊢
    push_cast at this
    nlinarith
  have h2 : V * (t - sampleTime F.t₀ dt k) ≤ V * dt :=
    mul_le_mul_of_nonneg_left hdist hV
  have h3 : -(V * (t - sampleTime F.t₀ dt k))
      ≤ F.x t - F.x (sampleTime F.t₀ dt k) := neg_le_of_abs_le hb
  linarith

theorem leg_bddBelow (F : Flight V dt turnA eps M) (hV : 0 ≤ V) (k : ℕ) :
    BddBelow (F.leg k) :=
  ⟨F.x (sampleTime F.t₀ dt k) - V * dt, fun _ hy => F.le_of_mem_leg hV k hy⟩

/-- The least position attained on the `k`-th leg. -/
noncomputable def low (F : Flight V dt turnA eps M) (k : ℕ) : ℝ := sInf (F.leg k)

theorem low_le (F : Flight V dt turnA eps M) (hV : 0 ≤ V) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc (sampleTime F.t₀ dt k) (sampleTime F.t₀ dt (k + 1))) :
    F.low k ≤ F.x t :=
  csInf_le (F.leg_bddBelow hV k) ⟨t, ht, rfl⟩

theorem le_low (F : Flight V dt turnA eps M) (k : ℕ) {a : ℝ}
    (h : ∀ t ∈ Icc (sampleTime F.t₀ dt k) (sampleTime F.t₀ dt (k + 1)), a ≤ F.x t) :
    a ≤ F.low k :=
  le_csInf (F.leg_nonempty k) (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)

/-- **A continuous flight is a sampled trajectory.** The three vehicle clauses
of `Fence.Traj` are discharged: `left_leg` from the speed bound, the other two
from the flight's own control-authority hypotheses. -/
noncomputable def toTraj (F : Flight V dt turnA eps M) (hV : 0 ≤ V)
    (ht : 0 ≤ turnA) (he : 0 ≤ eps) :
    Traj (Vehicle.ofSpeed V dt turnA eps hV F.dt_nonneg ht he) M where
  p := fun k => F.x (sampleTime F.t₀ dt k)
  d := fun k => fenceDir M (F.obs k) (F.req k)
  low := F.low
  obs := F.obs
  req := F.req
  obs_close := by simpa using F.obs_close
  control := fun _ => rfl
  low_le_pos := fun k =>
    F.low_le hV k ⟨le_rfl, sampleTime_le_succ F.dt_nonneg k⟩
  low_le_next := fun k =>
    F.low_le hV k ⟨sampleTime_le_succ F.dt_nonneg k, le_rfl⟩
  left_leg := by
    intro k _
    simp only [Vehicle.ofSpeed_Dmax]
    exact F.le_low k (fun t htm => F.le_of_mem_leg hV k ⟨t, htm, rfl⟩)
  turn_leg := by
    intro k hd
    simp only [Vehicle.ofSpeed_turn]
    exact F.le_low k (fun t htm => F.turn_leg k hd t htm)
  hold_leg := fun k hd => F.hold_leg k hd

/-- Every instant at or after the first sample lies in some leg. -/
theorem exists_leg (F : Flight V dt turnA eps M) (hdt : 0 < dt) {t : ℝ}
    (ht : F.t₀ ≤ t) :
    ∃ k : ℕ, t ∈ Icc (sampleTime F.t₀ dt k) (sampleTime F.t₀ dt (k + 1)) := by
  refine ⟨⌊(t - F.t₀) / dt⌋₊, ?_, ?_⟩
  · have hfl : ((⌊(t - F.t₀) / dt⌋₊ : ℕ) : ℝ) ≤ (t - F.t₀) / dt :=
      Nat.floor_le (div_nonneg (by linarith) hdt.le)
    unfold sampleTime
    rw [le_div_iff₀ hdt] at hfl
    linarith
  · have hfl : (t - F.t₀) / dt < (⌊(t - F.t₀) / dt⌋₊ : ℕ) + 1 :=
      Nat.lt_floor_add_one _
    unfold sampleTime
    rw [div_lt_iff₀ hdt] at hfl
    push_cast
    linarith

/-- **The fence holds at every real instant.**

`Dmax` has been eliminated: the hypothesis is now `V · Δt + turn + eps ≤ M`,
written in quantities a vehicle report contains. And the conclusion quantifies
over real time with no sampling in it — the samples are how the *controller*
works, not part of what is guaranteed. -/
theorem flight_nonneg (F : Flight V dt turnA eps M) (hV : 0 ≤ V) (hdt : 0 < dt)
    (ht : 0 ≤ turnA) (he : 0 ≤ eps) (hM : V * dt + turnA + eps ≤ M)
    (h0 : (F.toTraj hV ht he).Safe 0) {t : ℝ} (htt : F.t₀ ≤ t) :
    0 ≤ F.x t := by
  obtain ⟨k, hk⟩ := F.exists_leg hdt htt
  have hMv : (Vehicle.ofSpeed V dt turnA eps hV F.dt_nonneg ht he).Dmax
      + (Vehicle.ofSpeed V dt turnA eps hV F.dt_nonneg ht he).turn
      + (Vehicle.ofSpeed V dt turnA eps hV F.dt_nonneg ht he).eps ≤ M := by
    simpa using hM
  have hlow : 0 ≤ (F.toTraj hV ht he).low k := Traj.low_nonneg hMv h0 k
  have hlow' : (0 : ℝ) ≤ F.low k := hlow
  exact le_trans hlow' (F.low_le hV k hk)

end Flight

end Fence
end DPSS
