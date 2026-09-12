/-
# DPSS — the perimeter reflected

**B7.** Every convergence result here concerns *left* synchronization.
Avigad–van Doorn get the other half in four words — *"by symmetry"* — which on
paper is honest and in Lean is not.

The way to make it honest here is a **reflection**: flip the perimeter
end-for-end, reverse every heading, and renumber the drones backwards. The
algorithm is invariant under that, so right synchronization of a run *is* left
synchronization of the mirrored run, and every result proved on the left
transfers for free.

    position   x  ↦  1 − x
    heading    →  ↦  ←
    index      i  ↦  n−1−i

This file builds the reflection and its geometry. The step-commutation proof —
that mirroring and running commute — comes next, and is the substantial part.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §3 ("By symmetry, it suffices to show that
all the drones are left synchronized by time 2 − 1/n").
-/

import Dpss.EventuallyTurns

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

/-! ## Reflecting an index -/

/-- Drone `i` counted from the other end. -/
def mirrorIdx (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by have := i.isLt; omega⟩

@[simp] theorem mirrorIdx_val (i : Fin n) :
    (mirrorIdx i).val = n - 1 - i.val := rfl

/-- Reflecting twice is doing nothing. -/
@[simp] theorem mirrorIdx_mirrorIdx (i : Fin n) : mirrorIdx (mirrorIdx i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [mirrorIdx_val]
  omega

/-- Reflection reverses the ordering of drones. -/
theorem mirrorIdx_le_mirrorIdx {i j : Fin n} (hij : i ≤ j) :
    mirrorIdx j ≤ mirrorIdx i := by
  have hi := i.isLt
  have hj := j.isLt
  have h : i.val ≤ j.val := Fin.le_def.mp hij
  rw [Fin.le_def]
  simp only [mirrorIdx_val]
  omega

/-! ## Reflecting the geometry

The interval assigned to the reflected drone is the reflection of the interval
assigned to the original: left and right endpoints swap. -/

theorem cast_mirror (i : Fin n) : ((n - 1 - i.val : ℕ) : ℝ) = (n : ℝ) - 1 - (i.val : ℝ) := by
  have hi := i.isLt
  have h1 : (1 : ℕ) ≤ n := by omega
  have h2 : i.val ≤ n - 1 := by omega
  rw [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_one]

theorem leftEnd_mirrorIdx (i : Fin n) : leftEnd (mirrorIdx i) = 1 - rightEnd i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold leftEnd rightEnd
  rw [mirrorIdx_val, cast_mirror i]
  field_simp
  ring

theorem rightEnd_mirrorIdx (i : Fin n) : rightEnd (mirrorIdx i) = 1 - leftEnd i := by
  have h1 := rightEnd_sub_leftEnd (mirrorIdx i)
  have h2 := rightEnd_sub_leftEnd i
  have h3 := leftEnd_mirrorIdx i
  linarith

/-! ## Reflecting a configuration -/

namespace Config

/-- The configuration seen from the other end of the perimeter: positions
reflected, headings reversed, drones renumbered backwards. -/
noncomputable def mirror (c : Config n) : Config n where
  time := c.time
  pos := fun i => 1 - c.pos (mirrorIdx i)
  dir := fun i => (c.dir (mirrorIdx i)).flip

@[simp] theorem mirror_time (c : Config n) : c.mirror.time = c.time := rfl

@[simp] theorem mirror_pos (c : Config n) (i : Fin n) :
    c.mirror.pos i = 1 - c.pos (mirrorIdx i) := rfl

@[simp] theorem mirror_dir (c : Config n) (i : Fin n) :
    c.mirror.dir i = (c.dir (mirrorIdx i)).flip := rfl

/-- Reflecting twice is doing nothing. -/
theorem mirror_mirror (c : Config n) : c.mirror.mirror = c := by
  refine Config.ext rfl (funext fun i => ?_) (funext fun i => ?_)
  · simp only [mirror_pos, mirrorIdx_mirrorIdx]; ring
  · simp only [mirror_dir, mirrorIdx_mirrorIdx, Dir.flip_flip]

/-! ## The reflection respects the standing invariant -/

theorem onPerimeter_mirror {c : Config n} (hp : c.OnPerimeter) :
    c.mirror.OnPerimeter := by
  intro i
  obtain ⟨h0, h1⟩ := hp (mirrorIdx i)
  exact ⟨by simp only [mirror_pos]; linarith, by simp only [mirror_pos]; linarith⟩

theorem ordered_mirror {c : Config n} (ho : c.Ordered) : c.mirror.Ordered := by
  intro i j hij
  simp only [mirror_pos]
  have := ho (mirrorIdx j) (mirrorIdx i) (mirrorIdx_le_mirrorIdx hij)
  linarith

/-! ## What the reflection does to synchronization

The point of the whole exercise: staying at or beyond your *left* endpoint in
the mirrored world is staying at or before your *right* endpoint in this
one. -/

theorem leftEnd_le_mirror_pos_iff {c : Config n} (i : Fin n) :
    leftEnd i ≤ c.mirror.pos i ↔ c.pos (mirrorIdx i) ≤ rightEnd (mirrorIdx i) := by
  simp only [mirror_pos]
  rw [rightEnd_mirrorIdx i]
  constructor <;> intro hx <;> linarith

theorem mirror_pos_le_rightEnd_iff {c : Config n} (i : Fin n) :
    c.mirror.pos i ≤ rightEnd i ↔ leftEnd (mirrorIdx i) ≤ c.pos (mirrorIdx i) := by
  simp only [mirror_pos]
  rw [leftEnd_mirrorIdx i]
  constructor <;> intro hx <;> linarith

end Config

end DPSS
