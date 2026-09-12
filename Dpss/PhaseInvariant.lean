/-
# DPSS — what a heading after a step tells you

Closing Lemma 3.2's last case needs to know not just *that* a drone ends a step
heading some way, but *why*. This file extracts that: two case-analysis lemmas
turning `newDir i = left` (or `= right`) into the disjunction of events that
could have produced it, and then the consequence that matters.

## The consequence

> **A co-located pair that ends a step heading apart — the left one left, the
> right one right — is sitting exactly on the boundary they share.**

That is the post-separation configuration, and the lemma says it is the *only*
way to be in it. Every other route either fires a separation anyway (which puts
them on the boundary) or is contradictory, usually because a meeting pair
always agrees on where to go: `escortDirLeft (i+1) = escortDir i` when they are
together, so they cannot leave a meeting in opposite directions.

That pins the balance at zero whenever the pair is moving apart, which is the
invariant the remaining case of Lemma 3.2 runs on.

## Reference

Avigad–van Doorn, arXiv:2008.04262, Lemma 3.2.
-/

import Dpss.TurnPersistence

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Why a drone ends up heading left, or right -/

/-- The events that can leave a drone heading left. -/
theorem newDir_left_cases {c : Config n} {i : Fin n}
    (hnew : c.newDir i = Dir.left) :
    c.AtRightBorder i ∨ c.SepRight i
      ∨ (c.MeetRight i ∧ ¬ (c.pos i < commonEnd i))
      ∨ (c.MeetLeft i ∧ ¬ (c.pos i < leftEnd i))
      ∨ c.dir i = Dir.left := by
  unfold newDir at hnew
  split_ifs at hnew with h1 h2 h3 h4 h5 h6
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)
  · refine Or.inr (Or.inr (Or.inl ⟨h5, ?_⟩))
    unfold escortDir at hnew
    split_ifs at hnew with hlt
    exact hlt
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h6, ?_⟩)))
    unfold escortDirLeft at hnew
    split_ifs at hnew with hlt
    exact hlt
  · exact Or.inr (Or.inr (Or.inr (Or.inr hnew)))

/-- The events that can leave a drone heading right. -/
theorem newDir_right_cases {c : Config n} {i : Fin n}
    (hnew : c.newDir i = Dir.right) :
    c.AtLeftBorder i ∨ c.SepLeft i
      ∨ (c.MeetRight i ∧ c.pos i < commonEnd i)
      ∨ (c.MeetLeft i ∧ c.pos i < leftEnd i)
      ∨ c.dir i = Dir.right := by
  unfold newDir at hnew
  split_ifs at hnew with h1 h2 h3 h4 h5 h6
  · exact Or.inl h1
  · exact Or.inr (Or.inl h4)
  · refine Or.inr (Or.inr (Or.inl ⟨h5, ?_⟩))
    unfold escortDir at hnew
    split_ifs at hnew with hlt
    exact hlt
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h6, ?_⟩)))
    unfold escortDirLeft at hnew
    split_ifs at hnew with hlt
    exact hlt
  · exact Or.inr (Or.inr (Or.inr (Or.inr hnew)))

/-! ## A pair leaving a step in opposite directions

The target is:

> **A co-located pair that ends a step heading apart — the left one left, the
> right one right — is sitting exactly on the boundary they share.**

That is the post-separation configuration, and it should be the *only* way to
be in it. Pinning it down gives the invariant Lemma 3.2's last case runs on:
the balance is exactly zero while the pair moves apart.

Two of the routes are immediate, and are below. The rest is a nine-way case
analysis over `newDir_left_cases` × `newDir_right_cases`, most branches closing
because a meeting pair always agrees on where to go
(`escortDirLeft_next_eq_escortDir`) so it cannot leave a meeting in opposite
directions. **That analysis is not done**, and doing it will want the two case
lemmas above strengthened to carry the negations of the earlier branches —
which `split_ifs` supplies but the current statements discard. -/

/-- If the left drone's heading came from separating, the pair is on the
boundary. -/
theorem pos_eq_commonEnd_of_sepRight {c : Config n} {i : Fin n}
    (hs : c.SepRight i) : c.pos i = commonEnd i := hs.2.2

/-- And symmetrically if the right drone's heading came from separating. -/
theorem pos_eq_commonEnd_of_sepLeft_next {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hs : c.SepLeft (nextIdx i h)) :
    c.pos i = commonEnd i := by
  obtain ⟨_hh, _hc, hp⟩ := hs
  exact hp

/-- The identity that will close most of the remaining branches, restated
here for visibility: a co-located pair leaving a meeting agrees on its
heading, so it cannot leave one heading apart. -/
theorem meeting_pair_agrees {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hco : c.CoLocated i h) :
    c.escortDirLeft (nextIdx i h) = c.escortDir i :=
  escortDirLeft_next_eq_escortDir hco

end Config

end DPSS
