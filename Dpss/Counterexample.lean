/-
# DPSS — a lemma that is false, and why

While attempting the last case of Lemma 3.2 I aimed at:

> *A co-located pair that ends a step heading apart — the left one left, the
> right one right — is sitting exactly on the boundary they share.*

It reads as obviously true: heading apart is what a pair does **after
separating**, and separations happen on the shared boundary. Working the case
analysis with the branch negations carried, one combination refused to close.
This file builds the configuration and proves the statement **false**.

## The configuration

Four drones, all at the same point `3/8`, heading alternately:

    drone 0 →     drone 1 ←     drone 2 →     drone 3 ←
              all at 3/8

The middle pair is `(1, 2)`, whose shared boundary is at `1/2`.

* Drone 1 is **meeting its left neighbour** — drone 0 is closing on it — and
  `3/8` is past drone 1's own left endpoint `1/4`, so it escorts **leftward**.
* Drone 2 is **meeting its right neighbour** — drone 3 is closing on it — and
  `3/8` is short of drone 2's right endpoint `3/4`, so it escorts
  **rightward**.

Neither is separating from the other: that would need them at `1/2`, and they
are at `3/8`. So the pair `(1, 2)` leaves the step heading **apart**, at a
point that is **not** their shared boundary.

## What it means

The statement is false **for arbitrary configurations**; it needs reachability.
In a state the algorithm can actually produce, a co-located pair heading apart
has just separated, and separations do happen on the boundary — so the lemma is
presumably true where it is needed. But that has to be carried as an induction
hypothesis rather than proved pointwise, and my attempt did neither.

This is also the nondeterminism Avigad–van Doorn flag: three or more drones
converging, with a middle drone free to escort either neighbour. Here two
middle drones each pick the *outward* neighbour and the pair splits early.

Worth keeping. It is the second time in this project that reaching for a
concrete instance overturned something that read as obvious.
-/

import Dpss.PhaseInvariant

set_option linter.style.header false

namespace DPSS

namespace Counterexample

open Config

theorem hn4 : 0 < 4 := by norm_num

def f0 : Fin 4 := ⟨0, by norm_num⟩
def f1 : Fin 4 := ⟨1, by norm_num⟩
def f2 : Fin 4 := ⟨2, by norm_num⟩
def f3 : Fin 4 := ⟨3, by norm_num⟩

theorem h12 : f1.val + 1 < 4 := by norm_num [f1]

@[simp] theorem nextIdx_f1 : nextIdx f1 h12 = f2 := rfl

/-- Four drones stacked at `3/8`, heading alternately outward. -/
noncomputable def cascade : Config 4 where
  time := 0
  pos := fun _ => 3 / 8
  dir := fun i => if i.val % 2 = 1 then Dir.left else Dir.right

@[simp] theorem cascade_pos (i : Fin 4) : cascade.pos i = 3 / 8 := rfl
@[simp] theorem cascade_dir_f0 : cascade.dir f0 = Dir.right := rfl
@[simp] theorem cascade_dir_f1 : cascade.dir f1 = Dir.left := rfl
@[simp] theorem cascade_dir_f2 : cascade.dir f2 = Dir.right := rfl
@[simp] theorem cascade_dir_f3 : cascade.dir f3 = Dir.left := rfl

/-! ## The relevant geometry -/

theorem leftEnd_f1 : leftEnd f1 = 1 / 4 := by unfold leftEnd f1; norm_num
theorem commonEnd_f0 : commonEnd f0 = 1 / 4 := by
  unfold commonEnd rightEnd f0; norm_num
theorem commonEnd_f1 : commonEnd f1 = 1 / 2 := by
  unfold commonEnd rightEnd f1; norm_num
theorem commonEnd_f2 : commonEnd f2 = 3 / 4 := by
  unfold commonEnd rightEnd f2; norm_num

/-! ## The middle pair is together, and not on its boundary -/

theorem cascade_coLocated : cascade.CoLocated f1 h12 := by
  unfold CoLocated gap; rw [nextIdx_f1, cascade_pos, cascade_pos]; norm_num

theorem cascade_not_on_boundary : cascade.pos f1 ≠ commonEnd f1 := by
  rw [cascade_pos, commonEnd_f1]; norm_num

/-! ## Each middle drone escorts the *outward* neighbour -/

theorem cascade_meetLeft_f1 : cascade.MeetLeft f1 :=
  ⟨by norm_num [f1], by unfold CoLocated gap; norm_num, ⟨rfl, rfl⟩⟩

theorem cascade_meetRight_f2 : cascade.MeetRight f2 :=
  ⟨by norm_num [f2], by unfold CoLocated gap; norm_num, ⟨rfl, rfl⟩⟩

/-- Drone 1 leaves heading **left**. -/
theorem cascade_newDir_f1 : cascade.newDir f1 = Dir.left := by
  unfold newDir
  rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_pos cascade_meetLeft_f1,
    escortDirLeft, if_neg]
  · rw [cascade_pos, leftEnd_f1]; norm_num
  · -- not meeting its right neighbour: that would need it heading right
    rintro ⟨_hh, _hc, hA⟩
    have := hA.1
    rw [cascade_dir_f1] at this
    exact Dir.noConfusion this
  · -- not separating from its left neighbour: drone 0 is not on that boundary
    rintro ⟨_hh, _hc, hp⟩
    have hp' : (3 : ℝ) / 8 = commonEnd f0 := hp
    rw [commonEnd_f0] at hp'; norm_num at hp'
  · -- not separating from its right neighbour: not on *that* boundary either
    rintro ⟨_hh, _hc, hp⟩
    rw [cascade_pos, commonEnd_f1] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [cascade_pos] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [cascade_pos] at hp; norm_num at hp

/-- Drone 2 leaves heading **right**. -/
theorem cascade_newDir_f2 : cascade.newDir f2 = Dir.right := by
  unfold newDir
  rw [if_neg, if_neg, if_neg, if_neg, if_pos cascade_meetRight_f2,
    escortDir, if_pos]
  · rw [cascade_pos, commonEnd_f2]; norm_num
  · rintro ⟨_hh, _hc, hp⟩
    have hp' : (3 : ℝ) / 8 = commonEnd f1 := hp
    rw [commonEnd_f1] at hp'; norm_num at hp'
  · rintro ⟨_hh, _hc, hp⟩
    rw [cascade_pos, commonEnd_f2] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [cascade_pos] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [cascade_pos] at hp; norm_num at hp

/-! ## The refutation -/

/-- **The pair leaves the step heading apart, away from its shared boundary.**

So "a co-located pair heading apart sits on the boundary it shares" is false
for arbitrary configurations. It needs reachability, carried as an induction
hypothesis. -/
theorem apart_off_boundary :
    cascade.CoLocated f1 h12 ∧
      cascade.newDir f1 = Dir.left ∧
      cascade.newDir (nextIdx f1 h12) = Dir.right ∧
      cascade.pos f1 ≠ commonEnd f1 := by
  refine ⟨cascade_coLocated, cascade_newDir_f1, ?_, cascade_not_on_boundary⟩
  rw [nextIdx_f1]
  exact cascade_newDir_f2

/-- Stated as the refutation it is: no such pointwise lemma exists. -/
theorem not_forall_apart_implies_on_boundary :
    ¬ (∀ (c : Config 4) (i : Fin 4) (h : i.val + 1 < 4),
        c.CoLocated i h → c.newDir i = Dir.left →
          c.newDir (nextIdx i h) = Dir.right → c.pos i = commonEnd i) := by
  intro hall
  obtain ⟨hco, hL, hR, hne⟩ := apart_off_boundary
  exact hne (hall cascade f1 h12 hco hL hR)

end Counterexample

end DPSS
