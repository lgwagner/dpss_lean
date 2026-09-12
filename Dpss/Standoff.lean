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

## S3: the bound under standoff

**Proved, not predicted.** `toPoint` has an inverse (`fromPoint`), so the two
models are two coordinate systems on one thing; the standoff step is the point
step read in standoff coordinates, and `toPoint_sStep` / `toPoint_sRun` are then
immediate. The content is not the commuting square but the theorems saying the
pullback is what an engineer would have written:

* `sStep_pos` — **drones still move at unit speed in standoff coordinates.** The
  shear is by a constant per drone, so it changes where a drone is, never how
  fast it goes;
* `sTimeToNextEvent_eq` — the step's duration is the minimum over drones of
  deadlines computed in standoff coordinates: `sBorderTime`, `sMeetTime` (still
  half the *excess* gap, since a pair still closes at rate two), and
  `sSeparationTime`, measured to the respaced boundary;
* `sInvariant_toPoint` — the standing conditions correspond, so the invariant
  can be stated about the standoff system rather than about its image;
* **`sConvergesBy`** — Theorem 2.1 under standoff:

      every drone is inside its own respaced segment from
      (2 − 1/n)·(1 − (n−1)·d) onwards.

That constant is *smaller* than `2 − 1/n`. A team holding a standoff has less
ground between the walls to cover, so it converges sooner — the cost of the
standoff is paid in coverage, not in time: each drone patrols a shorter segment,
and `(n−1)·d` of the perimeter is buffer that the footprints, not the patrols,
account for.

The controller half of S3 — a **pair** under its own sampled controller
maintaining `d ≤ gap` against a real vehicle — is `Dpss/Separation.lean`.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2, for the point model being sheared.
-/

import Dpss.Convergence

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

/-! ## The map is a bijection

`toPoint` has an inverse, so the standoff model and the point model are two
coordinate systems on the same thing rather than two models with a map between
them. That is what lets the standoff *step* be **defined** as the pullback of
the point step below — and it is why the content of this section is not the
commuting square (which is then trivial) but the theorems saying that the
pullback has the standoff form an engineer would have written. -/

/-- Undo the shear and the rescaling. -/
noncomputable def fromPoint (d : ℝ) (c : Config n) : Config n where
  time := c.time * usable n d
  pos := fun i => c.pos i * usable n d + (i.val : ℝ) * d
  dir := c.dir

@[simp] theorem fromPoint_time (d : ℝ) (c : Config n) :
    (c.fromPoint d).time = c.time * usable n d := rfl

@[simp] theorem fromPoint_pos (d : ℝ) (c : Config n) (i : Fin n) :
    (c.fromPoint d).pos i = c.pos i * usable n d + (i.val : ℝ) * d := rfl

@[simp] theorem fromPoint_dir (d : ℝ) (c : Config n) (i : Fin n) :
    (c.fromPoint d).dir i = c.dir i := rfl

theorem fromPoint_toPoint {d : ℝ} (hL : usable n d ≠ 0) (c : Config n) :
    (c.toPoint d).fromPoint d = c := by
  apply Config.ext
  · simp only [fromPoint_time, toPoint_time]; field_simp
  · funext i; simp only [fromPoint_pos, toPoint_pos]; field_simp; ring
  · rfl

theorem toPoint_fromPoint {d : ℝ} (hL : usable n d ≠ 0) (c : Config n) :
    (c.fromPoint d).toPoint d = c := by
  apply Config.ext
  · simp only [fromPoint_time, toPoint_time]; field_simp
  · funext i; simp only [fromPoint_pos, toPoint_pos]; field_simp
    ring
  · rfl

/-! ## The standoff step -/

/-- One step of the standoff system: the point step, read in standoff
coordinates. -/
noncomputable def sStep (d : ℝ) (c : Config n) (hn : 0 < n) : Config n :=
  ((c.toPoint d).step hn).fromPoint d

/-- A run of the standoff system. -/
noncomputable def sRun (d : ℝ) (c : Config n) (hn : 0 < n) : ℕ → Config n
  | 0 => c
  | k + 1 => (c.sRun d hn k).sStep d hn

@[simp] theorem sRun_zero (d : ℝ) (c : Config n) (hn : 0 < n) :
    c.sRun d hn 0 = c := rfl

@[simp] theorem sRun_succ (d : ℝ) (c : Config n) (hn : 0 < n) (k : ℕ) :
    c.sRun d hn (k + 1) = (c.sRun d hn k).sStep d hn := rfl

/-- **The step commutes.** -/
theorem toPoint_sStep {d : ℝ} (hL : usable n d ≠ 0) (c : Config n) (hn : 0 < n) :
    (c.sStep d hn).toPoint d = (c.toPoint d).step hn :=
  toPoint_fromPoint hL _

/-- **And therefore so does the whole run.** -/
theorem toPoint_sRun {d : ℝ} (hL : usable n d ≠ 0) (c : Config n) (hn : 0 < n)
    (k : ℕ) : (c.sRun d hn k).toPoint d = (c.toPoint d).run hn k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sRun_succ, toPoint_sStep hL, ih, Config.run_succ]

/-! ## The deadline, in standoff terms

Everything above would be true of any bijection. This section is the content:
the step's duration, computed in the point model, is the minimum of deadlines
that are written in **standoff coordinates** — the ones a drone holding a
standoff would actually compute. -/

/-- How long the standoff system flies before the next event. -/
noncomputable def sTimeToNextEvent (d : ℝ) (c : Config n) (hn : 0 < n) : ℝ :=
  (c.toPoint d).timeToNextEvent hn * usable n d

/-- **Drones move at unit speed in standoff coordinates too.** The shear is by a
constant per drone, so it changes where a drone is, never how fast. -/
theorem sStep_pos {d : ℝ} (hL : usable n d ≠ 0) (c : Config n) (hn : 0 < n)
    (i : Fin n) :
    (c.sStep d hn).pos i = c.pos i + (c.dir i).sign * c.sTimeToNextEvent d hn := by
  unfold sStep sTimeToNextEvent
  simp only [fromPoint_pos, Config.step_pos, toPoint_pos, toPoint_dir]
  field_simp
  ring

/-- And the clock advances by that same duration. -/
theorem sStep_time {d : ℝ} (hL : usable n d ≠ 0) (c : Config n) (hn : 0 < n) :
    (c.sStep d hn).time = c.time + c.sTimeToNextEvent d hn := by
  unfold sStep sTimeToNextEvent
  simp only [fromPoint_time, Config.step_time, toPoint_time]
  field_simp

/-- Time to the wall drone `i` is heading for. Its own share of the standoff
sits between it and the left wall; the remaining `usable` sits between it and
the right one. -/
noncomputable def sBorderTime (d : ℝ) (c : Config n) (i : Fin n) : ℝ :=
  if c.dir i = Dir.left then c.pos i - (i.val : ℝ) * d
  else (i.val : ℝ) * d + usable n d - c.pos i

/-- Time until an approaching pair closes to the standoff. Still half the
excess, because they still close at rate two. -/
noncomputable def sMeetTime (d : ℝ) (c : Config n) (i : Fin n) (h : i.val + 1 < n) : ℝ :=
  (c.gap i h - d) / 2

/-- Time until an escorting pair reaches its respaced boundary. -/
noncomputable def sSeparationTime (d : ℝ) (c : Config n) (i : Fin n) : ℝ :=
  (standoffRightEnd d i - c.pos i) * (c.dir i).sign

/-- An escort, at the standoff. -/
def SEscorting (d : ℝ) (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop :=
  c.gap i h = d ∧ c.dir i = c.dir (nextIdx i h)

theorem sBorderTime_eq {d : ℝ} (hL : 0 < usable n d) (c : Config n) (i : Fin n) :
    c.sBorderTime d i = (c.toPoint d).borderTime i * usable n d := by
  unfold sBorderTime borderTime
  rw [toPoint_dir]
  split_ifs with hd
  · rw [toPoint_pos]; field_simp
  · rw [toPoint_pos]; field_simp; ring

theorem sMeetTime_eq {d : ℝ} (hL : 0 < usable n d) (c : Config n) (i : Fin n)
    (h : i.val + 1 < n) :
    c.sMeetTime d i h = (c.toPoint d).meetTime i h * usable n d := by
  unfold sMeetTime meetTime
  rw [toPoint_gap]
  field_simp

theorem sSeparationTime_eq {d : ℝ} (hL : 0 < usable n d) (c : Config n) (i : Fin n) :
    c.sSeparationTime d i = (c.toPoint d).separationTime i * usable n d := by
  unfold sSeparationTime separationTime commonEnd standoffRightEnd
  rw [toPoint_pos, toPoint_dir]
  field_simp
  ring

theorem sEscorting_iff {d : ℝ} (hL : 0 < usable n d) (c : Config n) (i : Fin n)
    (h : i.val + 1 < n) :
    c.SEscorting d i h ↔ (c.toPoint d).Escorting i h := by
  unfold SEscorting Escorting
  rw [toPoint_coLocated hL, toPoint_dir, toPoint_dir]

open Classical in
/-- The earliest deadline for one drone, in standoff terms. -/
noncomputable def sDroneNextTime (d : ℝ) (c : Config n) (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then
    if c.Approaching i h then min (c.sBorderTime d i) (c.sMeetTime d i h)
    else if c.SEscorting d i h then min (c.sBorderTime d i) (c.sSeparationTime d i)
    else c.sBorderTime d i
  else c.sBorderTime d i

theorem sDroneNextTime_eq {d : ℝ} (hL : 0 < usable n d) (c : Config n) (i : Fin n) :
    c.sDroneNextTime d i = (c.toPoint d).droneNextTime i * usable n d := by
  unfold sDroneNextTime droneNextTime
  by_cases h : i.val + 1 < n
  · rw [dif_pos h, dif_pos h]
    have hA : (c.toPoint d).Approaching i h ↔ c.Approaching i h :=
      toPoint_approaching d c i h
    by_cases hAp : c.Approaching i h
    · rw [if_pos hAp, if_pos (hA.mpr hAp), min_mul_of_nonneg _ _ hL.le,
        sBorderTime_eq hL, sMeetTime_eq hL]
    · rw [if_neg hAp, if_neg (fun hx => hAp (hA.mp hx))]
      by_cases hE : c.SEscorting d i h
      · rw [if_pos hE, if_pos ((sEscorting_iff hL c i h).mp hE),
          min_mul_of_nonneg _ _ hL.le, sBorderTime_eq hL, sSeparationTime_eq hL]
      · rw [if_neg hE, if_neg (fun hx => hE ((sEscorting_iff hL c i h).mpr hx)),
          sBorderTime_eq hL]
  · rw [dif_neg h, dif_neg h, sBorderTime_eq hL]

/-- **The standoff deadline is the minimum of the standoff deadlines.**

This is the theorem S0 left open, and with it the correspondence is complete:
every quantity the algorithm computes has a standoff form, and the standoff
forms agree with the point forms under the change of coordinates. -/
theorem sTimeToNextEvent_eq {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (hn : 0 < n) :
    c.sTimeToNextEvent d hn
      = Finset.univ.inf' (univ_fin_nonempty hn) (c.sDroneNextTime d) := by
  unfold sTimeToNextEvent timeToNextEvent
  rw [Finset.apply_inf'_eq_inf'_comp (univ_fin_nonempty hn) (fun t : ℝ => t * usable n d)
    (fun x y => min_mul_of_nonneg x y hL.le)]
  exact Finset.inf'_congr (univ_fin_nonempty hn) rfl
    (fun i _ => (sDroneNextTime_eq hL c i).symm)

/-! ## The standing conditions, in standoff terms

Each condition the point model carries has a standoff form, and the two agree.
With that, the convergence theorem can be *stated* about the standoff system
rather than about its image. -/

theorem toPoint_leftEnd_le_iff {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (i : Fin n) :
    leftEnd i ≤ (c.toPoint d).pos i ↔ standoffLeftEnd d i ≤ c.pos i := by
  rw [toPoint_pos, le_div_iff₀ hL]
  unfold standoffLeftEnd
  constructor <;> intro h <;> linarith [mul_comm (leftEnd i) (usable n d)]

theorem toPoint_le_rightEnd_iff {d : ℝ} (hL : 0 < usable n d) (c : Config n)
    (i : Fin n) :
    (c.toPoint d).pos i ≤ rightEnd i ↔ c.pos i ≤ standoffRightEnd d i := by
  rw [toPoint_pos, div_le_iff₀ hL]
  unfold standoffRightEnd
  constructor <;> intro h <;> linarith [mul_comm (rightEnd i) (usable n d)]

/-- Escorts point at the respaced boundary they are escorting to. -/
def SEscortsCoherent (d : ℝ) (c : Config n) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), c.SEscorting d i h → 0 ≤ c.sSeparationTime d i

theorem sEscortsCoherent_iff {d : ℝ} (hL : 0 < usable n d) (c : Config n) :
    c.SEscortsCoherent d ↔ (c.toPoint d).EscortsCoherent := by
  unfold SEscortsCoherent EscortsCoherent
  constructor
  · intro H i h hE
    have hS := H i h ((sEscorting_iff hL c i h).mpr hE)
    rw [sSeparationTime_eq hL] at hS
    nlinarith [hS, hL]
  · intro H i h hE
    have hS := H i h ((sEscorting_iff hL c i h).mp hE)
    rw [sSeparationTime_eq hL]
    exact mul_nonneg hS hL.le

/-- A pair at the standoff and heading apart sits on the boundary it shares. -/
def SApartOnBoundary (d : ℝ) (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop :=
  c.gap i h = d → c.dir i = Dir.left → c.dir (nextIdx i h) = Dir.right →
    c.pos i = standoffRightEnd d i

def SApartOnBoundaries (d : ℝ) (c : Config n) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), c.SApartOnBoundary d i h

theorem sApartOnBoundaries_iff {d : ℝ} (hL : 0 < usable n d) (c : Config n) :
    c.SApartOnBoundaries d ↔ (c.toPoint d).ApartOnBoundaries := by
  unfold SApartOnBoundaries ApartOnBoundaries SApartOnBoundary ApartOnBoundary commonEnd
  constructor
  · intro H i h hco hl hr
    exact (toPoint_standoffRightEnd hL c i).mpr
      (H i h ((toPoint_coLocated hL c i h).mp hco) hl hr)
  · intro H i h hco hl hr
    exact (toPoint_standoffRightEnd hL c i).mp
      (H i h ((toPoint_coLocated hL c i h).mpr hco) hl hr)

/-- The standing invariant of a standoff run: every pair holds the standoff, the
outermost drones are inside the perimeter, and escorts are coherent. -/
structure SInvariant (d : ℝ) (c : Config n) (hn : 0 < n) : Prop where
  separated : c.Separated d
  leftInside : 0 ≤ c.pos ⟨0, hn⟩
  rightInside : c.pos ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ ≤ 1
  escortsCoherent : c.SEscortsCoherent d

theorem sInvariant_toPoint {d : ℝ} (hL : 0 < usable n d) {c : Config n} {hn : 0 < n}
    (hsi : c.SInvariant d hn) : (c.toPoint d).Invariant where
  onPerimeter := toPoint_onPerimeter hn hL hsi.separated hsi.leftInside hsi.rightInside
  adjOrdered := (separated_iff_adjOrdered hL c).mp hsi.separated
  escortsCoherent := (sEscortsCoherent_iff hL c).mp hsi.escortsCoherent

/-! ## Convergence under standoff

The payoff. Time in the standoff system is time in the point system multiplied
by `usable n d`, so the bound scales by exactly that factor — and it is
*smaller* than `2 − 1/n`, because a team holding a standoff has less ground
between the walls to cover. -/

/-- **Theorem 2.1 under standoff.** From `(2 − 1/n)·(1 − (n−1)d)` on, every
drone is inside its own respaced segment. -/
def SConvergesBy (d : ℝ) (c : Config n) (hn : 0 < n) : Prop :=
  ∀ (i : Fin n) (j : ℕ),
    c.time + (2 - 1 / (n : ℝ)) * usable n d ≤ (c.sRun d hn j).time →
      standoffLeftEnd d i ≤ (c.sRun d hn j).pos i ∧
        (c.sRun d hn j).pos i ≤ standoffRightEnd d i

theorem sConvergesBy {d : ℝ} (hL : 0 < usable n d) {c : Config n} {hn : 0 < n}
    (hsi : c.SInvariant d hn) (hab : c.SApartOnBoundaries d) :
    c.SConvergesBy d hn := by
  intro i j ht
  have hrun : (c.sRun d hn j).toPoint d = (c.toPoint d).run hn j :=
    toPoint_sRun hL.ne' c hn j
  have hcv : ConvergesBy (c.toPoint d) hn :=
    convergesBy hn (sInvariant_toPoint hL hsi) ((sApartOnBoundaries_iff hL c).mp hab)
  -- the deadline, divided through by the scale
  have hnum : 0 ≤ (c.sRun d hn j).time - c.time - (2 - 1 / (n : ℝ)) * usable n d := by
    linarith
  have hquot : (0 : ℝ)
      ≤ ((c.sRun d hn j).time - c.time - (2 - 1 / (n : ℝ)) * usable n d) / usable n d :=
    div_nonneg hnum hL.le
  have hsplit : ((c.sRun d hn j).time - c.time - (2 - 1 / (n : ℝ)) * usable n d)
        / usable n d
      = (c.sRun d hn j).time / usable n d
        - (c.time / usable n d + (2 - 1 / (n : ℝ))) := by
    field_simp
    ring
  have htime : (c.toPoint d).time + (2 - 1 / (n : ℝ))
      ≤ ((c.toPoint d).run hn j).time := by
    rw [← hrun]
    simp only [toPoint_time]
    rw [hsplit] at hquot
    linarith
  obtain ⟨hl, hr⟩ := hcv i j htime
  rw [← hrun] at hl hr
  exact ⟨(toPoint_leftEnd_le_iff hL _ i).mp hl, (toPoint_le_rightEnd_iff hL _ i).mp hr⟩

end Config

end DPSS
