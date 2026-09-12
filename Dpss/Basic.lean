/-
# DPSS — the geometric and configuration layer

This file sets up the *static* vocabulary of the Decentralized Perimeter
Surveillance System: where the drones' assigned intervals are, what a snapshot
of the whole team looks like, and the ordering invariant that makes indexing by
`Fin n` meaningful.

Nothing here is about motion yet. Events and trajectories come next; this is the
layer they will be phrased in.

## Reference

Everything follows J. Avigad and F. van Doorn, *Progress on a Perimeter
Surveillance Problem*, arXiv:2008.04262, §2. Their normalization:

* the perimeter is the unit interval `[0,1]`;
* drones move at one unit of distance per unit of time;
* with `n` drones, the `i`-th is assigned an interval of width `1/n`.

## A note on indexing

The paper numbers drones `1, …, n` and gives drone `i` the interval
`[(i-1)/n, i/n]`. Lean's `Fin n` is `0, …, n-1`, so we shift by one and give
drone `i` the interval `[i/n, (i+1)/n]`. This is the same assignment under the
renaming `i ↦ i+1`; it just removes a subtraction from every statement. When
comparing a Lean statement here against the paper, remember the shift.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- This is a standalone project, not part of Mathlib, so Mathlib's house-style
-- header linter (copyright block, import discipline) does not apply.
set_option linter.style.header false

namespace DPSS

/-! ## Directions -/

/-- A drone is, at every moment, travelling either left or right along the
perimeter. Speed is constant and identical for all drones, so the direction is
the drone's entire velocity. -/
inductive Dir where
  | left : Dir
  | right : Dir
  deriving DecidableEq, Repr

namespace Dir

/-- Reversing a direction. Every event in the algorithm either leaves a drone's
direction alone or flips it. -/
def flip : Dir → Dir
  | left => right
  | right => left

/-- The velocity, as a real number: `-1` for leftward, `+1` for rightward.
Since speed is normalized to 1, this *is* the velocity. -/
def sign : Dir → ℝ
  | left => -1
  | right => 1

@[simp] theorem flip_left : flip left = right := rfl
@[simp] theorem flip_right : flip right = left := rfl
@[simp] theorem flip_flip (d : Dir) : d.flip.flip = d := by cases d <;> rfl

@[simp] theorem sign_left : sign left = -1 := rfl
@[simp] theorem sign_right : sign right = 1 := rfl

theorem sign_ne_zero (d : Dir) : d.sign ≠ 0 := by cases d <;> norm_num [sign]

/-- A direction's velocity squares to one. This is what makes "distance to a
point, divided by speed" come out right: flying for `(target - pos) * sign`
lands exactly on `target`, because the two `sign` factors cancel. -/
@[simp] theorem sign_mul_self (d : Dir) : d.sign * d.sign = 1 := by
  cases d <;> norm_num [sign]

/-- There are only two directions. Used constantly to drive case analysis on a
drone's heading. -/
theorem eq_left_or_right (d : Dir) : d = left ∨ d = right := by cases d <;> simp

/-- Drones never stand still: the two directions have opposite velocities. -/
@[simp] theorem sign_flip (d : Dir) : d.flip.sign = -d.sign := by
  cases d <;> norm_num [flip, sign]

end Dir

/-! ## Assigned intervals

With `n` drones on `[0,1]`, drone `i` is responsible for `[i/n, (i+1)/n]`.
In the steady state each drone sweeps back and forth across exactly this
interval; the whole point of the convergence theorem is that the team reaches
that state. -/

variable {n : ℕ}

/-- The left endpoint of drone `i`'s assigned interval. -/
noncomputable def leftEnd (i : Fin n) : ℝ := (i.val : ℝ) / (n : ℝ)

/-- The right endpoint of drone `i`'s assigned interval. -/
noncomputable def rightEnd (i : Fin n) : ℝ := ((i.val : ℝ) + 1) / (n : ℝ)

/-- Every assigned interval has width `1/n`. This is the quantity that shows up
as the per-step cost in the induction of Lemma 3.7, and hence as the `1/n` in
the bound `2 - 1/n`. -/
theorem rightEnd_sub_leftEnd (i : Fin n) :
    rightEnd i - leftEnd i = 1 / (n : ℝ) := by
  unfold rightEnd leftEnd; ring

/-- Assigned intervals are nondegenerate. -/
theorem leftEnd_lt_rightEnd (hn : 0 < n) (i : Fin n) : leftEnd i < rightEnd i := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hw : rightEnd i - leftEnd i = 1 / (n : ℝ) := rightEnd_sub_leftEnd i
  have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  linarith

/-- Adjacent drones share an endpoint: the right endpoint of drone `i` is the
left endpoint of drone `i+1`. This shared point is where a meeting pair escorts
each other to, and where they separate. -/
theorem rightEnd_eq_leftEnd_succ (i : Fin n) (hi : i.val + 1 < n) :
    rightEnd i = leftEnd ⟨i.val + 1, hi⟩ := by
  unfold rightEnd leftEnd
  push_cast
  ring

/-- The *common endpoint* of drones `i` and `i+1`: the point they escort each
other to after meeting, and the point at which they separate. Defined as drone
`i`'s right endpoint; `rightEnd_eq_leftEnd_succ` says this agrees with drone
`i+1`'s left endpoint. -/
noncomputable def commonEnd (i : Fin n) : ℝ := rightEnd i

/-- The leftmost drone's interval starts at the left border of the perimeter. -/
@[simp] theorem leftEnd_zero (hn : 0 < n) : leftEnd (⟨0, hn⟩ : Fin n) = 0 := by
  unfold leftEnd; simp

/-- The rightmost drone's interval ends at the right border of the perimeter. -/
theorem rightEnd_last (hn : 0 < n) :
    rightEnd (⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ : Fin n) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  unfold rightEnd
  rw [hcast]
  have hsimp : (n : ℝ) - 1 + 1 = (n : ℝ) := by ring
  rw [hsimp, div_self hn']

/-! ## Configurations

Following the paper's own suggestion (§2): *"the arguments below can be made
rigorous by formalizing the notion of a configuration (that is, a time `t`, and
the sequence of positions, directions and estimates of all the drones at that
time), and, given a configuration, the next configuration at which one of the
events above occurs."*

Note that we carry **no estimates**. This file targets Algorithm A, where every
drone already holds correct estimates, so the estimate `((a,ℓ),(b,m))` is
redundant: each drone already knows its true interval `[leftEnd i, rightEnd i]`.
The ACL2 mechanization drops them for the same reason. Algorithm B, where the
estimates are the whole story, is out of scope. -/

/-- A snapshot of the entire team at one instant. -/
structure Config (n : ℕ) where
  /-- The instant this snapshot describes. -/
  time : ℝ
  /-- Where each drone is. -/
  pos : Fin n → ℝ
  /-- Which way each drone is heading. -/
  dir : Fin n → Dir

namespace Config

variable (c : Config n)

/-- Drones are indexed left to right and never pass each other. This is an
invariant of the dynamics, not a definition of them — it has to be *proved*
preserved by every event. Once established it is what makes `Fin n` indexing
meaningful throughout. -/
def Ordered : Prop := ∀ i j : Fin n, i ≤ j → c.pos i ≤ c.pos j

/-- Every drone is somewhere on the perimeter. -/
def OnPerimeter : Prop := ∀ i : Fin n, 0 ≤ c.pos i ∧ c.pos i ≤ 1

/-- Two drones are *together* when they occupy the same position. Because all
drones move at the same speed, two drones that are together and heading the same
way stay together — which is exactly what an escort is. -/
def Together (i j : Fin n) : Prop := c.pos i = c.pos j

theorem together_refl (i : Fin n) : c.Together i i := rfl

theorem together_symm {i j : Fin n} (h : c.Together i j) : c.Together j i := h.symm

/-- A configuration fit to reason about: drones ordered, and on the perimeter. -/
structure Valid : Prop where
  ordered : c.Ordered
  onPerimeter : c.OnPerimeter

end Config

end DPSS
