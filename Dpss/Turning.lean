/-
# DPSS — where a drone is allowed to turn

This is the structural heart of the development, and it does double duty.

**The theorem.** A drone heading right can only turn left at or beyond its own
right endpoint; a drone heading left can only turn right at or before its left
endpoint. Nothing else in the algorithm can reverse a drone.

This is exactly Lemma 3.1 of Avigad–van Doorn, and it is on the critical path
for *both* remaining goals:

* **Convergence.** Lemma 3.1 is the base of the chain 3.1 → 3.2 → 3.7 that
  proves the `2 − 1/n` bound.
* **Non-Zeno.** A drone that turns right at `≤ leftEnd i` and next turns left at
  `≥ rightEnd i` has crossed its whole interval in between — a distance of
  `1/n`, at unit speed, so `1/n` of time. **Consecutive turns of one drone are
  therefore at least `1/n` apart**, so only finitely many events fit into a
  finite stretch of time.

## A deliberate departure from the paper

Avigad–van Doorn prove non-Zeno (§2) by a different route: infinitely many
events would force some drone to turn infinitely often, which propagates to all
drones via the claim that *"if drone `i+1` makes two consecutive left turns,
then drone `i` must turn right in the interim"*, which they call not hard to
show and do not show.

I could not reconstruct that claim. Tracing the cases, a right turn by drone
`i+1` comes either from separating from drone `i` — at which instant drone `i`
turns **left**, not right — or from meeting drone `i` to the left of their
shared boundary, at which instant drone `i` does not turn at all. Neither
yields the stated conclusion at that instant, and the paper gives no argument
for why the wider interval must contain one.

It may well be true. But this is a paper whose entire subject is a
"convincing-looking" proof that stood for a decade and was false, so
formalizing an unverified sketch would be the one unforgivable move here. The
interval-crossing argument above is self-contained, avoids the disputed claim
entirely, and reuses a lemma convergence needs anyway.

## Reference

Avigad–van Doorn, arXiv:2008.04262, Lemma 3.1 and §2.
-/

import Dpss.Step

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-- Drone `i` reverses from rightward to leftward across this step. -/
def TurnsLeft (c : Config n) (i : Fin n) : Prop :=
  c.dir i = Dir.right ∧ c.newDir i = Dir.left

/-- Drone `i` reverses from leftward to rightward across this step. -/
def TurnsRight (c : Config n) (i : Fin n) : Prop :=
  c.dir i = Dir.left ∧ c.newDir i = Dir.right

/-- Meeting the left-hand neighbour requires heading left, so a rightward drone
never does it. -/
theorem not_meetLeft_of_dir_right {c : Config n} {i : Fin n}
    (hd : c.dir i = Dir.right) : ¬ c.MeetLeft i := by
  rintro ⟨hpos, _hco, hA⟩
  have : c.dir i = Dir.left := by
    have h2 := hA.2
    rwa [nextIdx_prevIdx] at h2
  rw [hd] at this
  exact Dir.noConfusion this

/-- Meeting the right-hand neighbour requires heading right, so a leftward
drone never does it. -/
theorem not_meetRight_of_dir_left {c : Config n} {i : Fin n}
    (hd : c.dir i = Dir.left) : ¬ c.MeetRight i := by
  rintro ⟨_h, _hco, hA⟩
  have := hA.1
  rw [hd] at this
  exact Dir.noConfusion this

/-- A separation with the left neighbour puts this drone exactly on its own
left endpoint: the pair is co-located, and the point they share is the boundary
between their intervals. -/
theorem pos_eq_leftEnd_of_sepLeft {c : Config n} {i : Fin n}
    (hs : c.SepLeft i) : c.pos i = leftEnd i := by
  obtain ⟨hpos, hsep⟩ := hs
  have hco : c.gap (prevIdx i hpos) (prevIdx_lt i hpos) = 0 := hsep.1
  unfold gap at hco
  rw [nextIdx_prevIdx] at hco
  have hp : c.pos (prevIdx i hpos) = commonEnd (prevIdx i hpos) := hsep.2
  have hc : commonEnd (prevIdx i hpos) = leftEnd i := by
    unfold commonEnd
    rw [rightEnd_eq_leftEnd_succ (prevIdx i hpos) (prevIdx_lt i hpos)]
    congr 1
    exact nextIdx_prevIdx i hpos
  rw [hc] at hp
  linarith

/-- A separation with the right neighbour puts this drone exactly on its own
right endpoint. -/
theorem pos_eq_rightEnd_of_sepRight {c : Config n} {i : Fin n}
    (hs : c.SepRight i) : c.pos i = rightEnd i := by
  obtain ⟨_h, hsep⟩ := hs
  exact hsep.2

/-- **A rightward drone can only turn left at or beyond its right endpoint.**

Avigad–van Doorn Lemma 3.1. Every case is forced: a border turn happens at the
perimeter edge, which is past the endpoint; a separation happens exactly on the
endpoint; a meet only reverses the drone when the pair met beyond it; and the
remaining events cannot apply to a rightward drone at all. -/
theorem rightEnd_le_pos_of_turnsLeft {c : Config n} {i : Fin n}
    (ht : c.TurnsLeft i) : rightEnd i ≤ c.pos i := by
  obtain ⟨hd, hnew⟩ := ht
  unfold newDir at hnew
  split_ifs at hnew with h1 h2 h3 h4 h5 h6
  · -- at the right border: position 1, and no interval reaches past 1
    rw [h2.1]
    exact rightEnd_le_one i
  · -- separating from the right neighbour: exactly on the endpoint
    exact le_of_eq (pos_eq_rightEnd_of_sepRight h3).symm
  · -- meeting the right neighbour: it reverses this drone only if they met
    -- at or beyond their shared boundary
    unfold escortDir at hnew
    split_ifs at hnew with hlt
    rw [not_lt] at hlt
    unfold commonEnd at hlt
    exact hlt
  · -- a rightward drone cannot be meeting its left neighbour
    exact absurd h6 (not_meetLeft_of_dir_right hd)
  · -- nothing was due, so the heading is unchanged: it did not turn at all
    rw [hd] at hnew
    exact absurd hnew (fun h => Dir.noConfusion h)

/-- **A leftward drone can only turn right at or before its left endpoint.**

The mirror image, and equally forced. -/
theorem pos_le_leftEnd_of_turnsRight {c : Config n} {i : Fin n}
    (ht : c.TurnsRight i) : c.pos i ≤ leftEnd i := by
  obtain ⟨hd, hnew⟩ := ht
  unfold newDir at hnew
  split_ifs at hnew with h1 h2 h3 h4 h5 h6
  · -- at the left border: position 0, and no interval starts before 0
    rw [h1.1]
    exact leftEnd_nonneg i
  · -- separating from the left neighbour: exactly on the endpoint
    exact le_of_eq (pos_eq_leftEnd_of_sepLeft h4)
  · -- a leftward drone cannot be meeting its right neighbour
    exact absurd h5 (not_meetRight_of_dir_left hd)
  · -- meeting the left neighbour: it reverses this drone only if they met
    -- before their shared boundary
    unfold escortDirLeft at hnew
    split_ifs at hnew with hlt
    exact le_of_lt hlt
  · -- nothing was due, so the heading is unchanged
    rw [hd] at hnew
    exact absurd hnew (fun h => Dir.noConfusion h)

/-- **The interval-crossing bound.** A drone that turns right somewhere and
later turns left somewhere has crossed its entire assigned interval in the
meantime — a distance of at least `1/n`.

This is the geometric content that makes non-Zeno work: at unit speed, that
crossing costs at least `1/n` of time, so one drone cannot turn twice in quick
succession. -/
theorem turn_separation {c c' : Config n} {i : Fin n}
    (hr : c.TurnsRight i) (hl : c'.TurnsLeft i) :
    c.pos i + 1 / (n : ℝ) ≤ c'.pos i := by
  have h1 : c.pos i ≤ leftEnd i := pos_le_leftEnd_of_turnsRight hr
  have h2 : rightEnd i ≤ c'.pos i := rightEnd_le_pos_of_turnsLeft hl
  have h3 : rightEnd i - leftEnd i = 1 / (n : ℝ) := rightEnd_sub_leftEnd i
  linarith

end Config

end DPSS
