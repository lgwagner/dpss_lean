/-
# DPSS — motion between events

`Basic.lean` gave us snapshots. This file gives us *motion*: what happens when
the whole team flies forward for `dt` units of time with nobody changing
direction.

The headline result is `Config.ordered_advance`: **advancing by no more than the
time to the next collision preserves the left-to-right ordering of the drones.**
That is the invariant which makes indexing by `Fin n` mean anything at all, and
essentially every later argument leans on it.

## Why ordering is not free

Between events every drone flies in a straight line at unit speed. Two adjacent
drones heading *towards* each other close the gap between them at rate 2. Fly
them forward too far and they pass through each other — the model would still be
perfectly well-defined, it would just no longer describe DPSS. So ordering holds
only up to the collision time, and that is exactly the content of the theorem.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2. The events themselves are in `Events.lean`.
-/

import Dpss.Basic

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Flying forward -/

/-- Advance the whole team by `dt` units of time. Every drone moves at unit
speed in its current direction; nobody turns. This is the motion *between*
events — turning is what an event is. -/
noncomputable def advance (c : Config n) (dt : ℝ) : Config n where
  time := c.time + dt
  pos := fun i => c.pos i + (c.dir i).sign * dt
  dir := c.dir

@[simp] theorem advance_time (c : Config n) (dt : ℝ) :
    (c.advance dt).time = c.time + dt := rfl

@[simp] theorem advance_pos (c : Config n) (dt : ℝ) (i : Fin n) :
    (c.advance dt).pos i = c.pos i + (c.dir i).sign * dt := rfl

@[simp] theorem advance_dir (c : Config n) (dt : ℝ) :
    (c.advance dt).dir = c.dir := rfl

/-- Flying for no time changes nothing. -/
@[simp] theorem advance_zero_pos (c : Config n) (i : Fin n) :
    (c.advance 0).pos i = c.pos i := by simp

/-- Flying for `a` then for `b` is flying for `a + b`. Directions are untouched
by `advance`, which is why this composes so cleanly. -/
theorem advance_advance_pos (c : Config n) (a b : ℝ) (i : Fin n) :
    ((c.advance a).advance b).pos i = (c.advance (a + b)).pos i := by
  simp [advance]; ring

/-! ## Adjacent drones

Almost everything in DPSS is a statement about a drone and its immediate
right-hand neighbour, so it is worth naming that neighbour and the distance to
it. -/

/-- The drone immediately to the right of `i`. -/
def nextIdx (i : Fin n) (h : i.val + 1 < n) : Fin n := ⟨i.val + 1, h⟩

@[simp] theorem nextIdx_val (i : Fin n) (h : i.val + 1 < n) :
    (nextIdx i h).val = i.val + 1 := rfl

/-- The signed distance from drone `i` to its right-hand neighbour. Ordering of
the team is exactly the statement that every gap is nonnegative. -/
def gap (c : Config n) (i : Fin n) (h : i.val + 1 < n) : ℝ :=
  c.pos (nextIdx i h) - c.pos i

/-- The rate at which the gap between `i` and `i+1` grows. Since both drones
move at unit speed this is always `-2`, `0` or `2`: they approach, they hold
station, or they separate. -/
def sepRate (c : Config n) (i : Fin n) (h : i.val + 1 < n) : ℝ :=
  (c.dir (nextIdx i h)).sign - (c.dir i).sign

@[simp] theorem sepRate_advance (c : Config n) (dt : ℝ) (i : Fin n)
    (h : i.val + 1 < n) : (c.advance dt).sepRate i h = c.sepRate i h := rfl

/-- The gap evolves linearly in time at rate `sepRate`. This single equation is
the engine of the whole file. -/
theorem gap_advance (c : Config n) (dt : ℝ) (i : Fin n) (h : i.val + 1 < n) :
    (c.advance dt).gap i h = c.gap i h + c.sepRate i h * dt := by
  unfold gap
  simp [advance, sepRate]
  ring

/-! ## Approach and collision time -/

/-- Drones `i` and `i+1` are *approaching*: `i` heads right, `i+1` heads left.
This is the one configuration in which their gap shrinks, and hence the only way
the ordering can be threatened. -/
def Approaching (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop :=
  c.dir i = Dir.right ∧ c.dir (nextIdx i h) = Dir.left

/-- Approaching drones close their gap at rate exactly 2. -/
theorem sepRate_of_approaching {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hA : c.Approaching i h) : c.sepRate i h = -2 := by
  unfold sepRate
  rw [hA.1, hA.2]
  norm_num [Dir.sign]

/-- If they are not approaching, the gap never shrinks. -/
theorem sepRate_nonneg_of_not_approaching {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hA : ¬ c.Approaching i h) : 0 ≤ c.sepRate i h := by
  unfold Approaching at hA
  rcases Dir.eq_left_or_right (c.dir i) with hi | hi <;>
    rcases Dir.eq_left_or_right (c.dir (nextIdx i h)) with hj | hj
  · unfold sepRate; rw [hi, hj]; norm_num [Dir.sign]
  · unfold sepRate; rw [hi, hj]; norm_num [Dir.sign]
  · exact absurd ⟨hi, hj⟩ hA
  · unfold sepRate; rw [hi, hj]; norm_num [Dir.sign]

/-- How long until drones `i` and `i+1` collide, assuming they are approaching.
They close at rate 2, so it is half the gap. -/
noncomputable def meetTime (c : Config n) (i : Fin n) (h : i.val + 1 < n) : ℝ :=
  c.gap i h / 2

/-- **Sanity check: `meetTime` really is the moment of collision.**

A definition can be wrong and still support pretty theorems. This pins
`meetTime` down: fly approaching drones forward by exactly that long and their
gap is exactly zero — they are co-located, which is the precondition for a meet
event. If this failed, `ordered_advance` above would be guarding the wrong
quantity. -/
theorem gap_eq_zero_at_meetTime {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hA : c.Approaching i h) : (c.advance (c.meetTime i h)).gap i h = 0 := by
  rw [gap_advance, sepRate_of_approaching hA]
  unfold meetTime
  ring

/-- And they do not collide any earlier: before `meetTime` the gap is strictly
positive. Together with the previous result this says `meetTime` is the *first*
collision, not merely *a* moment of collision.

Note this needs no assumption that the pair is currently ordered: the gap being
positive strictly before the meet time falls straight out of the linear
evolution, whatever the gap's sign. -/
theorem gap_pos_before_meetTime {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    {dt : ℝ} (hA : c.Approaching i h)
    (hdt : dt < c.meetTime i h) : 0 < (c.advance dt).gap i h := by
  rw [gap_advance, sepRate_of_approaching hA]
  unfold meetTime at hdt
  linarith

/-- Collision time is nonnegative for an ordered pair. -/
theorem meetTime_nonneg {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hgap : 0 ≤ c.gap i h) : 0 ≤ c.meetTime i h := by
  unfold meetTime; linarith

/-! ## The ordering invariant -/

/-- Every drone is at or to the left of its right-hand neighbour. -/
def AdjOrdered (c : Config n) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), 0 ≤ c.gap i h

/-- **Adjacent ordering is preserved by flight, up to the collision time.**

The hypothesis is stated as an implication so that the non-approaching case
carries no obligation at all: if the drones are not closing, any `dt` is safe. -/
theorem gap_nonneg_advance {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    {dt : ℝ} (hgap : 0 ≤ c.gap i h) (hdt : 0 ≤ dt)
    (hle : c.Approaching i h → dt ≤ c.meetTime i h) :
    0 ≤ (c.advance dt).gap i h := by
  rw [gap_advance]
  by_cases hA : c.Approaching i h
  · rw [sepRate_of_approaching hA]
    have hb := hle hA
    unfold meetTime at hb
    linarith
  · have hs := sepRate_nonneg_of_not_approaching hA
    have : 0 ≤ c.sepRate i h * dt := mul_nonneg hs hdt
    linarith

/-- Pairwise ordering upgrades to full ordering. Proved by induction on the
index distance `j - i`, walking one neighbour at a time. -/
theorem ordered_of_adjOrdered {c : Config n} (hc : c.AdjOrdered) : c.Ordered := by
  have key : ∀ (k : ℕ) (i j : Fin n), j.val = i.val + k → c.pos i ≤ c.pos j := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      have : i = j := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro i j hij
      have hj := j.isLt
      have hlt : i.val + 1 < n := by omega
      have h1 : c.pos i ≤ c.pos (nextIdx i hlt) := by
        have := hc i hlt
        unfold gap at this
        linarith
      have h2 : c.pos (nextIdx i hlt) ≤ c.pos j := by
        apply ih
        simp only [nextIdx_val]
        omega
      linarith
  intro i j hij
  have hv : i.val ≤ j.val := Fin.le_def.mp hij
  exact key (j.val - i.val) i j (by omega)

/-- **The ordering invariant, in the form the rest of the development uses.**

If the team starts ordered and flies forward by no more than the time to the
next collision, it stays ordered. -/
theorem ordered_advance {c : Config n} {dt : ℝ}
    (hc : c.AdjOrdered) (hdt : 0 ≤ dt)
    (hle : ∀ (i : Fin n) (h : i.val + 1 < n),
      c.Approaching i h → dt ≤ c.meetTime i h) :
    (c.advance dt).Ordered := by
  apply ordered_of_adjOrdered
  intro i h
  exact gap_nonneg_advance (hc i h) hdt (hle i h)

end Config

end DPSS
