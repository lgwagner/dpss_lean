/-
# DPSS — concrete configurations

Everything else in this development is universally quantified. Nothing forces
the definitions to be *satisfiable*, and a formalization whose hypotheses can
never be met proves a great deal about nothing at all.

This file exhibits actual configurations and proves actual facts about them.

## The bounce regression test

`bounce` below is two drones meeting exactly on the boundary they share — the
paper's **bounce**, a meet and a separation occurring at the same instant.

This example found a real bug. `AtSeparation` originally required the pair to
be *escorting*, meaning co-located **and heading the same way**. But two drones
converging on their shared boundary have *opposite* headings right up to the
instant they meet, so no separation fired, the meet branch took over, and the
right-hand drone was sent **left — out of its own interval**, permanently
breaking the property the whole development is trying to prove.

The theorems below pin down the correct behaviour: the left drone turns left,
the right drone turns right, each going back to its own side.

This is exactly what gap 4 of `STATUS.md` warned about, and it is why working a
concrete case matters more than another layer of general theory.
-/

import Dpss.Coherence

set_option linter.style.header false

namespace DPSS

namespace Examples

open Config

/-- The left-hand drone of a two-drone team. -/
def d0 : Fin 2 := ⟨0, by norm_num⟩

/-- The right-hand drone. -/
def d1 : Fin 2 := ⟨1, by norm_num⟩

theorem d0_next : nextIdx d0 (by norm_num [d0]) = d1 := by
  apply Fin.ext; rfl

theorem commonEnd_d0 : commonEnd d0 = 1 / 2 := by
  unfold commonEnd rightEnd d0; norm_num

theorem leftEnd_d1 : leftEnd d1 = 1 / 2 := by
  unfold leftEnd d1; norm_num

/-! ## A bounce -/

/-- Two drones meeting exactly on their shared boundary, heading into each
other. The left one is travelling right, the right one left. -/
noncomputable def bounce : Config 2 where
  time := 0
  pos := fun _ => 1 / 2
  dir := fun i => if i.val = 0 then Dir.right else Dir.left

@[simp] theorem bounce_pos (i : Fin 2) : bounce.pos i = 1 / 2 := rfl
@[simp] theorem bounce_dir_d0 : bounce.dir d0 = Dir.right := rfl
@[simp] theorem bounce_dir_d1 : bounce.dir d1 = Dir.left := rfl

theorem bounce_h : d0.val + 1 < 2 := by norm_num [d0]

/-- The pair really is co-located. -/
theorem bounce_coLocated : bounce.CoLocated d0 bounce_h := by
  unfold CoLocated gap
  rw [d0_next]
  simp

/-- And really is sitting on the boundary it shares. -/
theorem bounce_atSeparation : bounce.AtSeparation d0 bounce_h :=
  ⟨bounce_coLocated, by rw [commonEnd_d0]; simp⟩

/-- They are genuinely approaching each other, so this is a meet as well as a
separation — which is precisely what makes it a bounce rather than an ordinary
separation. -/
theorem bounce_approaching : bounce.Approaching d0 bounce_h := by
  refine ⟨rfl, ?_⟩
  rw [d0_next]
  rfl

/-- **Regression test, left drone.** It turns left, back into `[0, 1/2]`. -/
theorem bounce_newDir_d0 : bounce.newDir d0 = Dir.left := by
  unfold newDir
  rw [if_neg, if_neg, if_pos]
  · exact ⟨bounce_h, bounce_atSeparation⟩
  · rintro ⟨hp, -⟩; rw [bounce_pos] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [bounce_pos] at hp; norm_num at hp

/-- **Regression test, right drone.** It turns right, back into `[1/2, 1]`.

Before the fix this returned `Dir.left`: the drone was driven out of its own
interval and could never be synchronized again. -/
theorem bounce_newDir_d1 : bounce.newDir d1 = Dir.right := by
  unfold newDir
  rw [if_neg, if_neg, if_neg, if_pos]
  · exact ⟨by norm_num [d1], bounce_atSeparation⟩
  · rintro ⟨h, -⟩
    exact absurd h (by norm_num [d1])
  · rintro ⟨hp, -⟩; rw [bounce_pos] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [bounce_pos] at hp; norm_num at hp

/-- The two drones leave the bounce heading in **opposite** directions. That is
the whole point of a separation, and it is what the bug destroyed. -/
theorem bounce_separates : bounce.newDir d0 ≠ bounce.newDir d1 := by
  rw [bounce_newDir_d0, bounce_newDir_d1]
  exact fun h => Dir.noConfusion h

/-! ## The invariant is satisfiable

A cheaper but equally necessary check: the standing invariant of a run is not
vacuous. -/

/-- Two drones approaching each other from inside their own intervals. -/
noncomputable def approach : Config 2 where
  time := 0
  pos := fun i => if i.val = 0 then 1 / 4 else 3 / 4
  dir := fun i => if i.val = 0 then Dir.right else Dir.left

/-- There are exactly two drones, so every index is one of them. -/
theorem fin2_cases (i : Fin 2) : i = d0 ∨ i = d1 := by
  rcases i with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

@[simp] theorem approach_pos_d0 : approach.pos d0 = 1 / 4 := rfl
@[simp] theorem approach_pos_d1 : approach.pos d1 = 3 / 4 := rfl

/-- **The standing invariant of a run is satisfiable.** Without this, every
theorem conditioned on `Invariant` would be true for the empty reason. -/
theorem approach_invariant : approach.Invariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases fin2_cases i with hi | hi <;> subst hi
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
  · intro i h
    rcases fin2_cases i with hi | hi <;> subst hi
    · unfold gap
      norm_num [approach, nextIdx, d0]
    · exact absurd h (by norm_num [d1])
  · intro i h he
    exfalso
    rcases fin2_cases i with hi | hi <;> subst hi
    · have hg : approach.gap d0 h = 0 := he.1
      unfold gap at hg
      norm_num [approach, nextIdx, d0] at hg
    · exact absurd h (by norm_num [d1])

end Examples

end DPSS
