/-
# DPSS — S2: the margined fence

Everything else in this development describes a **team**. This file describes a
**single drone**, and proves the one guarantee that needs no coordination at
all: it does not leave the perimeter.

That makes it the first genuinely drone-level result here, and deliberately the
cheapest one: it is a discrete theorem about a sampled controller, so it needs
no continuous-time machinery, no ODEs and no invariance theory. The vehicle
enters only through three numbers that an airframe analysis supplies.

## The idealizations being removed

The team model has a drone as a point moving at exactly unit speed, reversing
instantaneously, sensed perfectly. Here all three are replaced by parameters:

* `Dmax` — the furthest the drone can travel in one sample period;
* `turn` — the *turn allowance*: how far a drone commanded to reverse may still
  drift the wrong way before the reversal takes effect;
* `eps`  — the sensing error: the drone observes `p̂` with `|p̂ - p| ≤ eps`.

**Parameterized by displacement per sample, not by speed.** Speed would force a
division; displacement per sample is what a flight-test report actually
contains, and — the reason that matters here — it keeps every margin in the
same units as position, so the Verus half stays in integer arithmetic.

## The controller

    fenceDir M p̂ req = if p̂ ≤ M then right else req

The fence *overrides*: whatever direction the surveillance algorithm requests,
an observation at or below the margin `M` commands rightward. This is the same
shape as `newDir`'s border clause in `Step.lean`, where `AtLeftBorder` takes
priority over every other event, and for the same reason — so the guarantee is
unconditional rather than a case among others.

## The theorem

> With `M ≥ Dmax + turn + eps`, the invariant
>
>     dir = left  ⟹  Dmax + turn ≤ p
>     dir = right ⟹         turn ≤ p
>
> is preserved by every sample, and therefore the drone never crosses the fence.

The invariant is self-sustaining, which is what keeps the proof to a dozen
lines. If the observation is above `M` the controller may leave the drone
heading left, but then `p > M - eps ≥ Dmax + turn`, which is exactly the margin
the leftward case asks for. If the observation is at or below `M` the drone is
commanded right, and the margin it needs is only the turn allowance — which the
previous leg left it, because a leftward leg starting with `Dmax + turn` ends
with at least `turn`.

## And the margin is sharp

`margin_sharp` constructs, for **any** `M` below `Dmax + turn + eps`, a
trajectory satisfying the entire vehicle contract and the initial condition that
nonetheless crosses the fence. One three-sample family covers all three
deficiencies — too small by displacement, by turn allowance, or by sensing
error — so none of the three terms is slack.

This is the negative control for S2: a corrupted margin fails a *proof*, not
merely a test.

## Scope

The fence is proved for one drone against one wall. `Fence.Right` mirrors it,
via an explicit reflection rather than an appeal to symmetry — `Dpss/Mirror.lean`
reflects a whole `Config`, which is not what a single-drone statement needs.
Separation between drones is S3 and is not claimed here.
-/

import Dpss.Basic

set_option linter.style.header false

namespace DPSS
namespace Fence

/-! ## The vehicle contract

Three numbers, all of them things a vehicle analysis measures. Nothing below
derives them; deriving `Dmax` from a dynamics model is S4's job, and keeping it
a hypothesis is precisely what makes this result cheap. -/

/-- What the proof needs to know about the airframe. -/
structure Vehicle where
  /-- The furthest the drone travels in one sample period. -/
  Dmax : ℝ
  /-- Overshoot allowance: how far a drone commanded to reverse may still drift
  the wrong way before the reversal takes effect. -/
  turn : ℝ
  /-- Position sensing error bound. -/
  eps : ℝ
  Dmax_nonneg : 0 ≤ Dmax
  turn_nonneg : 0 ≤ turn
  eps_nonneg : 0 ≤ eps

namespace Vehicle

/-- The clearance a drone must hold from the fence, given where it is heading.
A leftward drone needs a whole sample period's travel plus the turn allowance;
a rightward drone needs only the turn allowance, because that is all it can
still lose. -/
def margin (V : Vehicle) : Dir → ℝ
  | Dir.left => V.Dmax + V.turn
  | Dir.right => V.turn

@[simp] theorem margin_left (V : Vehicle) : V.margin Dir.left = V.Dmax + V.turn := rfl
@[simp] theorem margin_right (V : Vehicle) : V.margin Dir.right = V.turn := rfl

theorem margin_nonneg (V : Vehicle) (d : Dir) : 0 ≤ V.margin d := by
  cases d
  · have := V.Dmax_nonneg; have := V.turn_nonneg; simp; linarith
  · simpa using V.turn_nonneg

end Vehicle

/-! ## The controller -/

/-- The fence controller. `req` is whatever heading the surveillance algorithm
asked for; an observation at or below the margin overrides it. -/
noncomputable def fenceDir (M : ℝ) (phat : ℝ) (req : Dir) : Dir :=
  if phat ≤ M then Dir.right else req

@[simp] theorem fenceDir_of_le {M phat : ℝ} (h : phat ≤ M) (req : Dir) :
    fenceDir M phat req = Dir.right := by
  unfold fenceDir; rw [if_pos h]

@[simp] theorem fenceDir_of_gt {M phat : ℝ} (h : M < phat) (req : Dir) :
    fenceDir M phat req = req := by
  unfold fenceDir; rw [if_neg (not_le.mpr h)]

/-- A controller that leaves the drone heading left was not triggered, so the
observation was strictly above the margin. This one-line fact is the entire
content of the controller as far as the proof is concerned. -/
theorem lt_obs_of_dir_left {M phat : ℝ} {req : Dir}
    (h : fenceDir M phat req = Dir.left) : M < phat := by
  by_contra hc
  rw [not_lt] at hc
  rw [fenceDir_of_le hc] at h
  exact Dir.noConfusion h

/-! ## Sampled trajectories

A trajectory is a sequence of samples. At sample `k` the drone is at `p k`,
observes `obs k`, is asked for `req k`, and flies the heading `d k` until sample
`k+1`; `low k` is the *lowest position it reaches* on that leg.

Carrying `low` explicitly is what lets a discrete statement say something about
continuous time: the fields below are the only facts about the motion between
samples that the proof uses, and each is a statement an airframe analysis can
discharge. -/

/-- A sampled trajectory of one drone under the fence controller. -/
structure Traj (V : Vehicle) (M : ℝ) where
  /-- Position at each sample. -/
  p : ℕ → ℝ
  /-- Heading flown on the leg from sample `k` to sample `k+1`. -/
  d : ℕ → Dir
  /-- The lowest position reached on that leg. -/
  low : ℕ → ℝ
  /-- What the drone's sensor reported at sample `k`. -/
  obs : ℕ → ℝ
  /-- What the surveillance algorithm asked for at sample `k`. -/
  req : ℕ → Dir
  /-- Sensing is accurate to `eps`. -/
  obs_close : ∀ k, |obs k - p k| ≤ V.eps
  /-- The heading flown is the one the fence controller commands. -/
  control : ∀ k, d k = fenceDir M (obs k) (req k)
  /-- `low` really is a low-water mark for the leg. -/
  low_le_pos : ∀ k, low k ≤ p k
  low_le_next : ∀ k, low k ≤ p (k + 1)
  /-- **Displacement bound.** A leftward leg travels at most `Dmax`. -/
  left_leg : ∀ k, d k = Dir.left → p k - V.Dmax ≤ low k
  /-- **Turn allowance.** A drone commanded right may still lose `turn`. -/
  turn_leg : ∀ k, d k = Dir.right → p k - V.turn ≤ low k
  /-- **Reversals complete within a sample period.** A drone commanded right is
  no further left at the next sample than it was at this one. Without some such
  clause there is no fence at all: a drone that loses ground on every rightward
  leg walks out of any margin. -/
  hold_leg : ∀ k, d k = Dir.right → p k ≤ p (k + 1)

namespace Traj

variable {V : Vehicle} {M : ℝ}

/-- The invariant: the drone holds the clearance its current heading requires. -/
def Safe (T : Traj V M) (k : ℕ) : Prop := V.margin (T.d k) ≤ T.p k

/-- **A safe sample leaves at least the turn allowance at the next one.**

Both cases are one subtraction. Heading left, the drone starts with
`Dmax + turn` and can spend at most `Dmax`; heading right, it does not lose
ground at all. This is the half of the induction that does not mention the
controller. -/
theorem turn_le_pos_succ {T : Traj V M} {k : ℕ} (hk : T.Safe k) :
    V.turn ≤ T.p (k + 1) := by
  cases hd : T.d k with
  | left =>
    have h1 : V.Dmax + V.turn ≤ T.p k := by
      have h := hk; unfold Safe at h; rw [hd] at h; simpa using h
    have h2 : T.p k - V.Dmax ≤ T.low k := T.left_leg k hd
    have h3 : T.low k ≤ T.p (k + 1) := T.low_le_next k
    linarith
  | right =>
    have h1 : V.turn ≤ T.p k := by
      have h := hk; unfold Safe at h; rw [hd] at h; simpa using h
    have h2 : T.p k ≤ T.p (k + 1) := T.hold_leg k hd
    linarith

/-- **The invariant is preserved.** The other half: if the controller leaves the
drone heading left it must not have fired, so the observation was above `M`, so
the true position is above `M - eps`, which the margin condition makes at least
`Dmax + turn`. -/
theorem safe_succ (hM : V.Dmax + V.turn + V.eps ≤ M) {T : Traj V M} {k : ℕ}
    (hk : T.Safe k) : T.Safe (k + 1) := by
  have hturn : V.turn ≤ T.p (k + 1) := turn_le_pos_succ hk
  unfold Safe
  cases hd : T.d (k + 1) with
  | right => simpa using hturn
  | left =>
    have hc : fenceDir M (T.obs (k + 1)) (T.req (k + 1)) = Dir.left := by
      rw [← T.control (k + 1), hd]
    have hgt : M < T.obs (k + 1) := lt_obs_of_dir_left hc
    have hobs : T.obs (k + 1) - T.p (k + 1) ≤ V.eps :=
      (abs_le.mp (T.obs_close (k + 1))).2
    simp only [Vehicle.margin_left]
    linarith

/-- **The invariant holds forever**, given that it holds at the first sample. -/
theorem safe_all (hM : V.Dmax + V.turn + V.eps ≤ M) {T : Traj V M}
    (h0 : T.Safe 0) : ∀ k, T.Safe k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => exact safe_succ hM ih

/-- **The fence holds — including between samples.**

`low k` is the lowest point of the whole leg, so this is a statement about
continuous time even though the proof is entirely discrete. -/
theorem low_nonneg (hM : V.Dmax + V.turn + V.eps ≤ M) {T : Traj V M}
    (h0 : T.Safe 0) (k : ℕ) : 0 ≤ T.low k := by
  have hk : T.Safe k := safe_all hM h0 k
  unfold Safe at hk
  cases hd : T.d k with
  | left =>
    have h1 : V.Dmax + V.turn ≤ T.p k := by rw [hd] at hk; simpa using hk
    have h2 : T.p k - V.Dmax ≤ T.low k := T.left_leg k hd
    have := V.turn_nonneg
    linarith
  | right =>
    have h1 : V.turn ≤ T.p k := by rw [hd] at hk; simpa using hk
    have h2 : T.p k - V.turn ≤ T.low k := T.turn_leg k hd
    linarith

/-- And in particular at every sample. -/
theorem pos_nonneg (hM : V.Dmax + V.turn + V.eps ≤ M) {T : Traj V M}
    (h0 : T.Safe 0) (k : ℕ) : 0 ≤ T.p k :=
  le_trans (low_nonneg hM h0 k) (T.low_le_pos k)

end Traj

/-! ## The margin is sharp

For **every** `M` below `Dmax + turn + eps` there is a trajectory obeying the
entire vehicle contract, starting with the clearance the invariant asks for,
that nonetheless crosses the fence. So none of the three terms is slack: drop
any part of any one of them and the theorem above is false.

The witness is a drone that flies left for `m` sample periods and is then
commanded right. Each leg is exactly `Dmax` long, sensing is exactly `eps`
adverse — reading high while the fence is ahead, low once it has been crossed —
and the turn costs exactly `turn`. The drone survives `m` observations above the
margin and arrives on the `m`-th leg with less clearance than the turn allowance
it is about to spend.

`m` is chosen large enough that the trajectory can start with the required
clearance and still reach the fence, which is what makes the result
unconditional rather than restricted to a window of `M`. -/

namespace Sharp

variable (V : Vehicle) (p0 : ℝ) (m : ℕ)

/-- Position at sample `k`: one `Dmax` per leftward leg, then held. -/
noncomputable def pos (k : ℕ) : ℝ :=
  if k ≤ m then p0 - V.Dmax * k else p0 - V.Dmax * m

/-- Heading: left for the first `m` legs, right thereafter. -/
def dir (k : ℕ) : Dir := if k < m then Dir.left else Dir.right

/-- Sensing is exactly `eps` adverse at every sample: high while the drone is
still heading for the fence (so the controller does not fire), low once it is
past (so the controller cannot be blamed for firing late). -/
noncomputable def obs (k : ℕ) : ℝ :=
  if k < m then pos V p0 m k + V.eps else pos V p0 m k - V.eps

/-- The low-water mark: a full `Dmax` on a leftward leg, the full turn
allowance on the reversal. -/
noncomputable def low (k : ℕ) : ℝ :=
  if k < m then pos V p0 m k - V.Dmax else pos V p0 m k - V.turn

variable {V p0 m}

theorem pos_of_le {k : ℕ} (h : k ≤ m) : pos V p0 m k = p0 - V.Dmax * k := by
  unfold pos; rw [if_pos h]

theorem pos_of_ge {k : ℕ} (h : m ≤ k) : pos V p0 m k = p0 - V.Dmax * m := by
  unfold pos
  by_cases hk : k ≤ m
  · rw [if_pos hk, Nat.le_antisymm hk h]
  · rw [if_neg hk]

@[simp] theorem dir_of_lt {k : ℕ} (h : k < m) : dir m k = Dir.left := by
  unfold dir; rw [if_pos h]

@[simp] theorem dir_of_ge {k : ℕ} (h : m ≤ k) : dir m k = Dir.right := by
  unfold dir; rw [if_neg (not_lt.mpr h)]

theorem lt_of_dir_left {k : ℕ} (h : dir m k = Dir.left) : k < m := by
  by_contra hc
  rw [dir_of_ge (not_lt.mp hc)] at h
  exact Dir.noConfusion h

theorem ge_of_dir_right {k : ℕ} (h : dir m k = Dir.right) : m ≤ k := by
  by_contra hc
  rw [dir_of_lt (not_le.mp hc)] at h
  exact Dir.noConfusion h

/-- **The witness.** The four numbered hypotheses are exactly what the
construction needs, and `margin_sharp` below supplies them.

* `ha` — every observation on a leftward leg reads above the margin, so the
  controller never fires early;
* `hb` — the observation on the reversal leg reads at or below it, so the
  controller does fire;
* `hc` — the trajectory starts with the clearance the invariant demands. -/
noncomputable def traj (M : ℝ) (hm : 0 < m)
    (ha : M < p0 - V.Dmax * (m - 1 : ℕ) + V.eps)
    (hb : p0 - V.Dmax * m - V.eps ≤ M) :
    Traj V M where
  p := pos V p0 m
  d := dir m
  low := low V p0 m
  obs := obs V p0 m
  req := fun _ => Dir.left
  obs_close := by
    intro k
    unfold obs
    by_cases hk : k < m
    · rw [if_pos hk]
      simp [abs_of_nonneg V.eps_nonneg]
    · rw [if_neg hk]
      have : pos V p0 m k - V.eps - pos V p0 m k = -V.eps := by ring
      rw [this, abs_neg, abs_of_nonneg V.eps_nonneg]
  control := by
    intro k
    unfold obs
    by_cases hk : k < m
    · -- still heading for the fence: the observation reads above the margin
      rw [if_pos hk, dir_of_lt hk]
      have hkm : (k : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
        have : k ≤ m - 1 := by omega
        exact_mod_cast this
      have hle : V.Dmax * (k : ℝ) ≤ V.Dmax * ((m - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hkm V.Dmax_nonneg
      have hpos : pos V p0 m k = p0 - V.Dmax * k := pos_of_le (le_of_lt hk)
      exact (fenceDir_of_gt (by rw [hpos]; linarith) _).symm
    · -- past the fence: the observation reads at or below the margin
      rw [if_neg hk, dir_of_ge (not_lt.mp hk)]
      have hpos : pos V p0 m k = p0 - V.Dmax * m := pos_of_ge (not_lt.mp hk)
      exact (fenceDir_of_le (by rw [hpos]; linarith) _).symm
  low_le_pos := by
    intro k
    unfold low
    by_cases hk : k < m
    · rw [if_pos hk]; have := V.Dmax_nonneg; linarith
    · rw [if_neg hk]; have := V.turn_nonneg; linarith
  low_le_next := by
    intro k
    unfold low
    by_cases hk : k < m
    · rw [if_pos hk, pos_of_le (le_of_lt hk), pos_of_le (by omega : k + 1 ≤ m)]
      push_cast
      have hexp : V.Dmax * ((k : ℝ) + 1) = V.Dmax * (k : ℝ) + V.Dmax := by ring
      rw [hexp]; linarith
    · rw [if_neg hk, pos_of_ge (not_lt.mp hk), pos_of_ge (by omega : m ≤ k + 1)]
      have := V.turn_nonneg; linarith
  left_leg := by
    intro k hd
    have hk : k < m := lt_of_dir_left hd
    unfold low; rw [if_pos hk]
  turn_leg := by
    intro k hd
    have hk : m ≤ k := ge_of_dir_right hd
    unfold low; rw [if_neg (not_lt.mpr hk)]
  hold_leg := by
    intro k hd
    have hk : m ≤ k := ge_of_dir_right hd
    rw [pos_of_ge hk, pos_of_ge (by omega : m ≤ k + 1)]

end Sharp

/-- **The margin `Dmax + turn + eps` is exactly tight.**

For every smaller `M` there is a trajectory satisfying the whole vehicle
contract and starting with the required clearance that crosses the fence anyway.
Together with `Traj.low_nonneg` this pins the margin down on both sides: no
smaller number works, and that one does.

Note what the hypotheses are *not*. There is no restriction on which of the
three terms is deficient and no window of `M` in which the result is stated —
only that the drone can move at all. -/
theorem margin_sharp (V : Vehicle) (M : ℝ) (hD : 0 < V.Dmax)
    (hlt : M < V.Dmax + V.turn + V.eps) :
    ∃ (T : Traj V M) (k : ℕ), T.Safe 0 ∧ T.low k < 0 := by
  have hgpos : 0 < V.Dmax + V.turn + V.eps - M := by linarith
  -- how far the drone will be short by: strictly less than the deficiency
  set δ := min ((V.Dmax + V.turn + V.eps - M) / 2) V.Dmax with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) hD
  have hδD : δ ≤ V.Dmax := min_le_right _ _
  have hδg : δ < V.Dmax + V.turn + V.eps - M :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  -- enough leftward legs that the drone can start with the required clearance
  obtain ⟨j, hj⟩ := exists_nat_ge ((V.Dmax + V.turn + V.eps - M) / V.Dmax)
  have hjD : V.Dmax + V.turn + V.eps - M ≤ V.Dmax * (j : ℝ) := by
    rw [div_le_iff₀ hD] at hj; linarith
  set p0 : ℝ := M - V.eps + V.Dmax * (j : ℝ) + δ with hp0
  have hcast : (((j + 1) - 1 : ℕ) : ℝ) = (j : ℝ) := by simp
  have hcast' : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  refine ⟨Sharp.traj (V := V) (p0 := p0) (m := j + 1) M (by omega) ?_ ?_, j + 1, ?_, ?_⟩
  · -- every leftward observation reads above the margin
    rw [hcast]; simp only [hp0]; linarith
  · -- the observation on the reversal leg reads at or below it
    rw [hcast']
    have := V.eps_nonneg
    simp only [hp0]; nlinarith
  · -- the trajectory starts with the clearance the invariant demands
    change V.margin (Sharp.dir (j + 1) 0) ≤ Sharp.pos V p0 (j + 1) 0
    rw [Sharp.dir_of_lt (by omega), Sharp.pos_of_le (by omega)]
    simp only [Vehicle.margin_left, Nat.cast_zero, mul_zero, sub_zero, hp0]
    linarith
  · -- yet it crosses the fence on the reversal leg
    change Sharp.low V p0 (j + 1) (j + 1) < 0
    unfold Sharp.low
    rw [if_neg (lt_irrefl _), Sharp.pos_of_ge (le_refl _), hcast']
    simp only [hp0]
    nlinarith

end Fence
end DPSS
