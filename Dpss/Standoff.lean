/-
# DPSS — S0: does the standoff shear hold?

Everything else in this development treats a drone as a **point**. Two drones
that meet occupy the same coordinate. That is not an edge case of the algorithm,
it is the coordination mechanism: `CoLocated` is how a pair learns to escort.

Real drones cannot do that. They must hold a standoff `d`, and the separation
requirement `d ≤ gap` flatly contradicts the ordering invariant `0 ≤ gap` that
the meet event is designed to saturate. Something has to give, and S0 exists to
test the cheapest way out before any of the structural work is committed to.

## The change of coordinates

Shear by index:

    yᵢ = xᵢ - i·d

Then `xᵢ₊₁ - xᵢ ≥ d` becomes `yᵢ₊₁ - yᵢ ≥ 0`: **separation becomes ordering**.
Speeds are untouched, because `i·d` does not depend on time. And the perimeter
shrinks: `y` ranges over `[0, 1 - (n-1)·d]`.

Rescaling `y` and the clock by that factor restores the unit perimeter and unit
speed, which is why the map below divides by

    usable n d = 1 - (n-1)·d

## The verdict

**The shear is exact.** The results here are:

* `Config.toPoint_gap` — the sheared gap is the standoff gap less `d`, scaled;
  hence `separated_iff_adjOrdered`, the whole point of the exercise;
* `Config.toPoint_advance` — **the dynamics commute**. Flying for `dt` in the
  standoff model is flying for `dt / usable n d` in the point model. This is the
  lemma that would have failed had the shear been merely an approximation;
* the event predicates correspond one for one — border, meet, separation,
  approach;
* `Config.toPoint_onPerimeter` — containment transfers, needing only that the
  outermost two drones are inside.

And the catch the plan flagged, which is real but benign: **the assigned
segments do not shear.** They have to be respaced, and `standoff_tiles` says
exactly how — each segment narrows to `usable n d / n` and consecutive segments
are separated by a buffer of exactly `d`. The buffers tile the perimeter with
the segments (`standoffLeftEnd_zero`, `standoffRightEnd_last`), so nothing is
lost, and `coverage_exact` says that if the standoff is two half-footprints —
`d = 2r`, the reading on which "co-located" means "footprints touching" — the
buffer is covered exactly by the two neighbouring drones at the ends of their
segments. No gap in coverage, no overlap.

## Consequence for S3

S3 is a change of constants, not a re-derivation. Every time in the point model
is a time in the standoff model multiplied by `usable n d`, so the convergence
bound becomes

    (2 - 1/n) · (1 - (n-1)·d)

which is *smaller* than `2 - 1/n`: standoff drones have less ground to cover.
The cost is not in the bound, it is in the coverage — each drone patrols a
shorter segment, and `1/n` of the perimeter is buffer.

## What S0 does *not* settle

The correspondence proved here is at the level of positions, motion and the
event *predicates*. The scheduler — `timeToNextEvent`, `newDir`, `step` — is
left to S3. Since every deadline is a time, and times scale by a single positive
constant, that is arithmetic rather than a new idea; but it is not done here and
is not claimed.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2, for the point model being sheared.
-/

import Dpss.Events

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

/-- The perimeter left over once each of the `n-1` adjacent pairs holds a
standoff of `d`. The whole file is conditional on this being positive — a team
whose standoffs exceed the perimeter has no configuration at all. -/
noncomputable def usable (n : ℕ) (d : ℝ) : ℝ := 1 - ((n : ℝ) - 1) * d

theorem usable_pos_iff (n : ℕ) (d : ℝ) :
    0 < usable n d ↔ ((n : ℝ) - 1) * d < 1 := by
  unfold usable; constructor <;> intro h <;> linarith

namespace Config

/-! ## The change of coordinates -/

/-- Shear out the standoff, then rescale to the unit perimeter and unit speed.
The image is a configuration of the **point** model. -/
noncomputable def toPoint (d : ℝ) (c : Config n) : Config n where
  time := c.time / usable n d
  pos := fun i => (c.pos i - (i.val : ℝ) * d) / usable n d
  dir := c.dir

@[simp] theorem toPoint_time (d : ℝ) (c : Config n) :
    (c.toPoint d).time = c.time / usable n d := rfl

@[simp] theorem toPoint_pos (d : ℝ) (c : Config n) (i : Fin n) :
    (c.toPoint d).pos i = (c.pos i - (i.val : ℝ) * d) / usable n d := rfl

@[simp] theorem toPoint_dir (d : ℝ) (c : Config n) (i : Fin n) :
    (c.toPoint d).dir i = c.dir i := rfl

/-- **Separation becomes ordering.** The sheared gap is the standoff gap less
the standoff itself, rescaled. -/
theorem toPoint_gap (d : ℝ) (c : Config n) (i : Fin n) (h : i.val + 1 < n) :
    (c.toPoint d).gap i h = (c.gap i h - d) / usable n d := by
  unfold gap
  simp only [toPoint_pos, nextIdx_val]
  push_cast
  ring

/-- **The dynamics commute.** Flying for `dt` in the standoff model is flying for
`dt / usable n d` in the point model — same headings, same straight lines.

This is the lemma S0 exists to test. Had the shear been an approximation rather
than a change of coordinates, it is here that it would have shown. -/
theorem toPoint_advance (d dt : ℝ) (c : Config n) :
    (c.advance dt).toPoint d = (c.toPoint d).advance (dt / usable n d) := by
  apply Config.ext
  · simp only [toPoint_time, advance_time]; ring
  · funext i
    simp only [toPoint_pos, advance_pos, toPoint_dir]
    ring
  · rfl

/-! ## The separation requirement -/

/-- Every adjacent pair holds at least the standoff. -/
def Separated (d : ℝ) (c : Config n) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), d ≤ c.gap i h

/-- **The point of the exercise.** Under the shear, the separation requirement
*is* the ordering invariant that the whole existing development is built on. -/
theorem separated_iff_adjOrdered {d : ℝ} (hL : 0 < usable n d) (c : Config n) :
    c.Separated d ↔ (c.toPoint d).AdjOrdered := by
  constructor
  · intro H i h
    rw [toPoint_gap]
    exact div_nonneg (by linarith [H i h]) hL.le
  · intro H i h
    have hg := H i h
    rw [toPoint_gap] at hg
    have h2 : (0 : ℝ) * usable n d ≤ c.gap i h - d := (le_div_iff₀ hL).mp hg
    rw [zero_mul] at h2
    linarith

/-! ## The events correspond

Each of the four event predicates pulls back to the standoff condition one would
have written by hand. Nothing has to be redefined; the meet event in particular
becomes *"the pair has closed to the standoff"*, which is the physically right
reading of `CoLocated`. -/

/-- A meet in the point model is the pair closing to the standoff. -/
theorem toPoint_coLocated {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (i : Fin n) (h : i.val + 1 < n) :
    (c.toPoint d).CoLocated i h ↔ c.gap i h = d := by
  unfold CoLocated
  rw [toPoint_gap, div_eq_zero_iff]
  constructor
  · rintro (hz | hz)
    · linarith
    · exact absurd hz hL.ne'
  · intro hz; left; linarith

/-- Approach is a statement about headings alone, and headings do not shear. -/
@[simp] theorem toPoint_approaching (d : ℝ) (c : Config n) (i : Fin n)
    (h : i.val + 1 < n) :
    (c.toPoint d).Approaching i h ↔ c.Approaching i h := Iff.rfl

/-- The left border, pulled back: drone `i`'s own share of the standoff is all
that separates it from the wall. For drone `0` this is `pos = 0`. -/
theorem toPoint_atLeftBorder {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (i : Fin n) :
    (c.toPoint d).AtLeftBorder i ↔ (c.pos i = (i.val : ℝ) * d ∧ c.dir i = Dir.left) := by
  unfold AtLeftBorder
  rw [toPoint_pos, toPoint_dir, div_eq_zero_iff]
  constructor
  · rintro ⟨hz | hz, hd⟩
    · exact ⟨by linarith, hd⟩
    · exact absurd hz hL.ne'
  · rintro ⟨hz, hd⟩; exact ⟨Or.inl (by linarith), hd⟩

/-- And the right border. For drone `n-1` this is `pos = 1`. -/
theorem toPoint_atRightBorder {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (i : Fin n) :
    (c.toPoint d).AtRightBorder i
      ↔ (c.pos i = (i.val : ℝ) * d + usable n d ∧ c.dir i = Dir.right) := by
  unfold AtRightBorder
  rw [toPoint_pos, toPoint_dir, div_eq_one_iff_eq hL.ne']
  constructor
  · rintro ⟨hz, hd⟩; exact ⟨by linarith, hd⟩
  · rintro ⟨hz, hd⟩; exact ⟨by linarith, hd⟩

/-! ## The segments have to be respaced

This is the one thing that does *not* transport for free: `leftEnd i = i/n` is
tied to the unit perimeter. Its preimage under the shear is the definition
below, and the three theorems after it say that the respacing is consistent —
the segments and the buffers tile the perimeter exactly. -/

/-- The left endpoint of drone `i`'s segment, in standoff coordinates. -/
noncomputable def standoffLeftEnd (d : ℝ) (i : Fin n) : ℝ :=
  usable n d * leftEnd i + (i.val : ℝ) * d

/-- The right endpoint of drone `i`'s segment, in standoff coordinates. -/
noncomputable def standoffRightEnd (d : ℝ) (i : Fin n) : ℝ :=
  usable n d * rightEnd i + (i.val : ℝ) * d

/-- The respaced endpoints are exactly the preimages of the original ones. -/
theorem toPoint_standoffLeftEnd {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (i : Fin n) :
    (c.toPoint d).pos i = leftEnd i ↔ c.pos i = standoffLeftEnd d i := by
  rw [toPoint_pos, div_eq_iff hL.ne']
  unfold standoffLeftEnd
  constructor <;> intro h <;> linarith [h]

theorem toPoint_standoffRightEnd {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (i : Fin n) :
    (c.toPoint d).pos i = rightEnd i ↔ c.pos i = standoffRightEnd d i := by
  rw [toPoint_pos, div_eq_iff hL.ne']
  unfold standoffRightEnd
  constructor <;> intro h <;> linarith [h]

/-- A separation in the point model is the pair at the standoff, sitting on the
respaced boundary. -/
theorem toPoint_atSeparation {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (i : Fin n) (h : i.val + 1 < n) :
    (c.toPoint d).AtSeparation i h
      ↔ (c.gap i h = d ∧ c.pos i = standoffRightEnd d i) := by
  unfold AtSeparation commonEnd
  rw [toPoint_coLocated hL, toPoint_standoffRightEnd hL]

/-- **Every segment narrows by the same factor.** -/
theorem standoff_width (d : ℝ) (i : Fin n) :
    standoffRightEnd d i - standoffLeftEnd d i = usable n d * (1 / (n : ℝ)) := by
  unfold standoffLeftEnd standoffRightEnd
  have h := rightEnd_sub_leftEnd i
  linear_combination (usable n d) * h

/-- **The segments tile the perimeter, separated by buffers of exactly `d`.** -/
theorem standoff_tiles (d : ℝ) (i : Fin n) (h : i.val + 1 < n) :
    standoffRightEnd d i + d = standoffLeftEnd d (nextIdx i h) := by
  unfold standoffLeftEnd standoffRightEnd
  rw [rightEnd_eq_leftEnd_succ i h]
  have hidx : (nextIdx i h) = (⟨i.val + 1, h⟩ : Fin n) := rfl
  rw [hidx]
  push_cast
  ring

/-- The leftmost segment still starts at the wall. -/
@[simp] theorem standoffLeftEnd_zero (d : ℝ) (hn : 0 < n) :
    standoffLeftEnd d (⟨0, hn⟩ : Fin n) = 0 := by
  unfold standoffLeftEnd
  rw [leftEnd_zero hn]
  simp

/-- And the rightmost still ends at the far wall: the segments and the `n-1`
buffers account for the whole perimeter, with nothing left over. -/
theorem standoffRightEnd_last (d : ℝ) (hn : 0 < n) :
    standoffRightEnd d (⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ : Fin n) = 1 := by
  unfold standoffRightEnd usable
  rw [rightEnd_last hn]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hcast]
  ring

/-- **Coverage is exact when the standoff is two half-footprints.** With
`d = 2r`, a drone at the right end of its segment and its neighbour at the left
end of theirs cover the buffer between them precisely — no gap, no overlap.
This is the reading on which "co-located" means "footprints touching", and it is
what makes the respacing lose nothing. -/
theorem coverage_exact (r : ℝ) (i : Fin n) (h : i.val + 1 < n) :
    standoffRightEnd (2 * r) i + r = standoffLeftEnd (2 * r) (nextIdx i h) - r := by
  have := standoff_tiles (2 * r) i h
  linarith

/-! ## Containment transfers

The sheared configuration is on the unit perimeter provided only that the
outermost two drones are inside the real one. Everything in between follows from
the separation requirement, which is what makes this a change of coordinates
rather than an extra hypothesis. -/

/-- Separation compounds along the team: `m` places to the right is at least
`m·d` further along. -/
theorem pos_add_le_of_separated {c : Config n} {d : ℝ} (hs : c.Separated d)
    (i : Fin n) (m : ℕ) (h : i.val + m < n) :
    c.pos i + (m : ℝ) * d ≤ c.pos ⟨i.val + m, h⟩ := by
  induction m with
  | zero =>
    have : (⟨i.val + 0, h⟩ : Fin n) = i := by apply Fin.ext; simp
    rw [this]; simp
  | succ m ih =>
    have h' : i.val + m < n := by omega
    have hih := ih h'
    have hj : (⟨i.val + m, h'⟩ : Fin n).val + 1 < n := by
      change i.val + m + 1 < n
      omega
    have hg := hs ⟨i.val + m, h'⟩ hj
    unfold gap at hg
    have hnext : nextIdx (⟨i.val + m, h'⟩ : Fin n) hj = (⟨i.val + (m + 1), h⟩ : Fin n) := by
      apply Fin.ext; simp; omega
    rw [hnext] at hg
    push_cast
    linarith

/-- **Containment transfers.** -/
theorem toPoint_onPerimeter {c : Config n} {d : ℝ} (hn : 0 < n)
    (hL : 0 < usable n d) (hs : c.Separated d)
    (h0 : 0 ≤ c.pos ⟨0, hn⟩)
    (h1 : c.pos ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ ≤ 1) :
    (c.toPoint d).OnPerimeter := by
  intro i
  have hlast : i.val + (n - 1 - i.val) = n - 1 := by have := i.isLt; omega
  have hilt : i.val ≤ n - 1 := by have := i.isLt; omega
  constructor
  · -- the drones to its left have already used `i·d` of the perimeter
    have hlow := pos_add_le_of_separated hs ⟨0, hn⟩ i.val (by simp [i.isLt])
    have hidx : (⟨(⟨0, hn⟩ : Fin n).val + i.val, (by simp [i.isLt] : 0 + i.val < n)⟩ : Fin n)
        = i := by apply Fin.ext; change 0 + i.val = i.val; omega
    rw [hidx] at hlow
    rw [toPoint_pos]
    apply div_nonneg _ hL.le
    linarith
  · -- and those to its right need `(n-1-i)·d` of what is left
    have hhigh := pos_add_le_of_separated hs i (n - 1 - i.val) (by omega)
    have hidx : (⟨i.val + (n - 1 - i.val), (by omega : i.val + (n - 1 - i.val) < n)⟩ : Fin n)
        = ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ := by apply Fin.ext; simp [hlast]
    rw [hidx] at hhigh
    have hcast : ((n - 1 - i.val : ℕ) : ℝ) = (n : ℝ) - 1 - (i.val : ℝ) := by
      rw [Nat.cast_sub hilt, Nat.cast_sub hn, Nat.cast_one]
    rw [hcast] at hhigh
    rw [toPoint_pos, div_le_one hL]
    unfold usable
    linarith

end Config

end DPSS
