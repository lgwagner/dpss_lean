/-
# DPSS — S1: bounded speed, as a change of clock

The team model normalizes speed to one. That is the last of the four
idealizations `Dpss/Fence.lean` and `Dpss/Standoff.lean` have been removing —
and the one the plan sized as the expensive one, because unit speed is not a
coordinate choice like the standoff: it is cashed in by
`Config.pos_sub_eq_of_dirConst`, *distance travelled equals elapsed time*, which
the whole non-Zeno argument, Lemma 3.5, Lemma 3.7 and the sharpness family all
consume.

## The observation

**If every drone has the same speed at the same instant, speed is a clock.**

Let the common speed be `v(t)` and put `τ(t) = ∫₀ᵗ v`. Along the trajectory,
position is a function of distance travelled, and distance travelled is `τ`. So
the bounded-speed system at real time `t` is the **unit-speed system at unit
time `τ(t)`** — same positions, same headings, same events, same order of
events. Nothing about the model changes; only the clock does.

`Clock` below is that reparameterization, axiomatized by what it has to satisfy
rather than by an integral: `vmin·(t−s) ≤ τ(t) − τ(s) ≤ V·(t−s)`. Stating it
this way avoids importing any integration theory, and it is also the honest
interface — a vehicle report gives speed bounds, not a speed function.

## What transfers, and what each bound is for

Everything, and the two bounds do different jobs:

* **Convergence needs the lower bound and only the lower bound.**
  `converges_by_real_time`: under any uniform profile with `v ≥ vmin > 0`, the
  team is synchronized by real time `(2 − 1/n) / vmin`. Going faster never
  hurts, so `V` does not appear.
* **Non-Zeno needs neither.** `nonZeno_real_time` is the unit-speed statement
  evaluated at `τ(T)`, which is a real number whatever the speeds were.

So the upper bound `V` plays no part in either. It is not idle — it is exactly
the `Dmax` of `Dpss/Fence.lean`, where it is what makes the fence margin finite
— but it earns its keep at the controller, not in the team model.

## Why `vmin > 0` is not a technicality

`vmin_zero_stalls` is the counterexample, and it is as blunt as it looks: with
`vmin = 0` the constant clock `τ ≡ 0` satisfies the whole contract, and under it
**every drone stays exactly where it started, for ever**. No real-time deadline
can exist. This is the correction to the plan's own sizing, which had proposed
bounding speed from above only: an upper bound alone makes the theorem false,
not merely weaker.

## What this does *not* cover

**Speeds that differ between drones.** That is not a change of clock, and it is
a rewrite rather than a margin. `Dpss/Events.lean` says why in as many words:
*"Because all drones move at the same speed, a co-located pair pointing the same
way stays co-located — the escort needs no special representation, it is an
emergent consequence of uniform speed."* Drop uniformity and `Escorting` stops
being an invariant, taking `EscortsCoherent`, `Dpss/Coherence.lean` and Lemmas
3.2–3.4 with it; an explicit grouped representation would be needed, as the ACL2
mechanization has. Recorded, not attempted.
-/

import Dpss.Convergence

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

/-! ## A speed profile is a clock -/

/-- A uniform speed profile, presented as the reparameterization it induces.
`τ t` is the distance a drone has travelled by real time `t`; the two
inequalities are the speed bounds, integrated.

Uniform across drones, not necessarily constant in time — a drone may accelerate
and decelerate freely inside the band. -/
structure Clock (vmin V : ℝ) where
  /-- Distance travelled by real time `t`. -/
  τ : ℝ → ℝ
  /-- The drones never go slower than `vmin`. -/
  lower : ∀ s t : ℝ, s ≤ t → vmin * (t - s) ≤ τ t - τ s
  /-- Nor faster than `V`. -/
  upper : ∀ s t : ℝ, s ≤ t → τ t - τ s ≤ V * (t - s)

namespace Clock

variable {vmin V : ℝ}

/-- Time does not run backwards, provided the drones do not either. -/
theorem mono (cl : Clock vmin V) (hv : 0 ≤ vmin) : Monotone cl.τ := by
  intro s t h
  have := cl.lower s t h
  nlinarith [mul_nonneg hv (sub_nonneg.mpr h)]

/-- **Distance accumulates at least linearly.** This is the only property of the
profile the convergence transfer uses, and it is where `vmin > 0` becomes
load-bearing. -/
theorem add_mul_le (cl : Clock vmin V) {s t : ℝ} (h : s ≤ t) :
    cl.τ s + vmin * (t - s) ≤ cl.τ t := by
  have := cl.lower s t h
  linarith

end Clock

namespace Config

/-! ## Position under a speed profile

The bounded-speed drone at real time `t` is the unit-speed drone at unit time
`τ t`. That is the whole transfer, and it is a definition rather than a
theorem. -/

/-- Where drone `i` is at real time `t`, during step `p`, under the profile. -/
noncomputable def posAtSpeed {vmin V : ℝ} (cl : Clock vmin V) (c : Config n)
    (hn : 0 < n) (p : ℕ) (i : Fin n) (t : ℝ) : ℝ :=
  c.posIn hn p i (cl.τ t)

/-- **Theorem 2.1 under a uniform bounded speed profile, at the instant.**

Read off `sync_at_of_time` at unit time `τ t`: the profile changes when the
deadline arrives, never whether it does. -/
theorem sync_at_speed {vmin V : ℝ} (cl : Clock vmin V) {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) (hab : c.ApartOnBoundaries) (i : Fin n) (p : ℕ) (t : ℝ)
    (ht : c.time + (2 - 1 / (n : ℝ)) ≤ cl.τ t) (hin : c.InStep hn p (cl.τ t)) :
    leftEnd i ≤ c.posAtSpeed cl hn p i t ∧ c.posAtSpeed cl hn p i t ≤ rightEnd i :=
  sync_at_of_time hn hi hab i p (cl.τ t) ht hin

/-- **The deadline, converted into real time.**

`vmin > 0` turns the unit-time deadline into a real-time one by division. This
is the only step of the argument in which a speed bound is used at all. -/
theorem tau_ge_of_real_time {vmin V : ℝ} (cl : Clock vmin V) (hv : 0 < vmin)
    {c : Config n} {t₀ t : ℝ} (h : t₀ ≤ t)
    (hreach : (c.time + (2 - 1 / (n : ℝ)) - cl.τ t₀) / vmin ≤ t - t₀) :
    c.time + (2 - 1 / (n : ℝ)) ≤ cl.τ t := by
  have hmul : c.time + (2 - 1 / (n : ℝ)) - cl.τ t₀ ≤ vmin * (t - t₀) := by
    rw [div_le_iff₀ hv] at hreach
    linarith
  have := cl.add_mul_le (vmin := vmin) (V := V) h
  linarith

/-- **Theorem 2.1 in real time, under bounded speed.**

From a start at time zero with the clock at zero, every drone is inside its own
assigned interval at every instant from

    (2 − 1/n) / vmin

onwards — whatever the speed profile does inside the band, and with no reference
to the upper bound `V` at all. -/
theorem converges_by_real_time {vmin V : ℝ} (cl : Clock vmin V) (hv : 0 < vmin)
    {c : Config n} (hn : 0 < n) (hi : c.Invariant) (hab : c.ApartOnBoundaries)
    (hc : c.time = 0) (h0 : cl.τ 0 = 0) (i : Fin n) (p : ℕ) (t : ℝ)
    (ht : (2 - 1 / (n : ℝ)) / vmin ≤ t) (hin : c.InStep hn p (cl.τ t)) :
    leftEnd i ≤ c.posAtSpeed cl hn p i t ∧ c.posAtSpeed cl hn p i t ≤ rightEnd i := by
  refine sync_at_speed cl hn hi hab i p t ?_ hin
  have htnn : (0 : ℝ) ≤ t := by
    have hd : (0 : ℝ) ≤ (2 - 1 / (n : ℝ)) / vmin := by
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h1 : 1 / (n : ℝ) ≤ 1 := by
        rw [div_le_one hn']
        exact_mod_cast hn
      have : (0 : ℝ) ≤ 2 - 1 / (n : ℝ) := by linarith
      exact div_nonneg this hv.le
    linarith
  refine tau_ge_of_real_time cl hv (t₀ := 0) htnn ?_
  rw [hc, h0]
  simpa using ht

/-- **Non-Zeno in real time**, and it needs no speed bound whatsoever: `τ T` is a
real number however fast the drones went, so the unit-speed statement applies to
it directly. Only finitely many events precede any real instant. -/
theorem nonZeno_real_time {vmin V : ℝ} (cl : Clock vmin V) {c : Config n}
    (hn : 0 < n) (hnz : c.NonZeno hn) (T : ℝ) :
    ∃ k : ℕ, cl.τ T < (c.run hn k).time :=
  hnz (cl.τ T)

/-! ## The lower bound is not a technicality -/

/-- The clock that never advances. It satisfies the contract with `vmin = 0` and
any `V ≥ 0`. -/
noncomputable def stalled (V : ℝ) (hV : 0 ≤ V) : Clock 0 V where
  τ := fun _ => 0
  lower := by intro s t _; simp
  upper := by
    intro s t h
    simp only [sub_self]
    exact mul_nonneg hV (sub_nonneg.mpr h)

/-- **With `vmin = 0` the whole team can be frozen.**

Under the stalled clock every drone is, at every real time, exactly where it
started. So no real-time deadline of any kind holds — not `(2 − 1/n)/vmin` with
`vmin` replaced by anything, and not any other function of the data.

This is why bounding speed from *above* alone is not enough, and it is the
correction to this track's own plan, which had proposed exactly that. -/
theorem vmin_zero_stalls {V : ℝ} (hV : 0 ≤ V) {c : Config n} (hn : 0 < n)
    (hc : c.time = 0) (i : Fin n) (t : ℝ) :
    c.posAtSpeed (stalled V hV) hn 0 i t = c.pos i := by
  unfold posAtSpeed posIn stalled
  simp [hc]

/-! ## The contract is not vacuous

`Clock` is a set of inequalities, and a set of inequalities can be unsatisfiable.
The constant-speed profile inhabits it with a strictly positive lower bound, and
hits the deadline exactly — which is also a check that the conversion
`(2 − 1/n)/v` has not lost or gained a factor. -/

/-- Flying at a constant speed `v`. -/
noncomputable def uniform (v : ℝ) : Clock v v where
  τ := fun t => v * t
  lower := by intro s t _; ring_nf; linarith
  upper := by intro s t _; ring_nf; linarith

@[simp] theorem uniform_tau (v t : ℝ) : (uniform v).τ t = v * t := rfl

/-- At constant speed the real-time deadline lands exactly on the unit-time one:
no slack has been introduced by the conversion. -/
theorem uniform_tau_deadline {v : ℝ} (hv : 0 < v) (n : ℕ) :
    (uniform v).τ ((2 - 1 / (n : ℝ)) / v) = 2 - 1 / (n : ℝ) := by
  simp only [uniform_tau]
  field_simp

end Config

end DPSS
