/-
# DPSS — how much of the priority order is actually a choice

**C1**, and gap 5 of `STATUS.md`.

`newDir` resolves competing events in the order

    border  >  separation  >  meet  >  unchanged

and `Step.lean` records that order as *one resolution* of a choice
Avigad–van Doorn deliberately leave open. That statement is too pessimistic,
and this file measures the real freedom by brute force: for **every** pair of
events that can be due at the same drone at the same instant, compute both
answers and compare.

The result is sharper than expected.

## Every tie but one is not a tie

| both due | separation says | meet says | |
|---|---|---|---|
| right border + `MeetRight` | `left` | `left` | agree |
| left border + `MeetLeft` | `right` | `right` | agree |
| left border + `SepLeft` | — | — | **impossible** |
| right border + `SepRight` | — | — | **impossible** |
| `SepRight` + `MeetRight` | `left` | `left` | agree |
| `SepRight` + `MeetLeft` | `left` | `left` | agree |
| `SepLeft` + `MeetRight` | `right` | `right` | agree |
| `SepLeft` + `MeetLeft` | `right` | `left` | **differ** |

So the priority order is **forced** everywhere except one configuration: a
drone standing on its own left endpoint, co-located with its left-hand
neighbour, which is still heading right. That is the paper's **bounce** — two
drones meeting head-on exactly on the boundary they share.

And there the answer is not a free choice either: the protocol says a bounce
sends each drone back into its own interval, which is what separation
priority gives. Taking the meet instead sends the drone **left off its own left
endpoint** (`newDirMeetFirst_leaves_interval`) — which is precisely the bug the
`n = 2` trace caught and `Events.lean` documents at length.

`newDirMeetFirst` below is that alternative resolution, defined so the
comparison is a theorem rather than an argument.

## What this does *not* settle

The paper's nondeterminism is not really about the priority order. It is about
what a **meet** is. Here `MeetRight i` requires the pair to be *approaching* —
`i` heading right and `i+1` heading left — so a drone co-located with both
neighbours has at most one meet due, and which one is decided by its own
heading. The paper treats a meeting as purely positional, so when three or more
drones coincide the middle one may pair with **either** neighbour and escort to
either endpoint, whatever it was doing before.

Closing that needs `step` to become a relation and the whole development to be
re-proved over an arbitrary trajectory of it. `STATUS.md` §4 keeps it as an
open gap, now stated in these narrower terms.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2 ("the strongest upper bound will allow
for nondeterminism and allow the middle drone to go to either endpoint").
-/

import Dpss.ThreeConverge

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Two combinations that cannot arise -/

/-- A drone on the left border of the perimeter is not separating from a
left-hand neighbour: it has one only if its own left endpoint is positive. -/
theorem not_sepLeft_of_atLeftBorder {c : Config n} {i : Fin n}
    (hb : c.AtLeftBorder i) : ¬ c.SepLeft i := by
  intro hs
  have hp : c.pos i = leftEnd i := pos_eq_leftEnd_of_sepLeft hs
  obtain ⟨hpos, -⟩ := hs
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : (0 : ℝ) < leftEnd i := by
    unfold leftEnd
    have : (0 : ℝ) < (i.val : ℝ) := by exact_mod_cast hpos
    positivity
  rw [hb.1] at hp
  linarith

/-- And a drone on the right border is not separating from a right-hand
neighbour: it would have to *be* the last drone. -/
theorem not_sepRight_of_atRightBorder {c : Config n} {i : Fin n}
    (hb : c.AtRightBorder i) : ¬ c.SepRight i := by
  intro hs
  have hp : c.pos i = rightEnd i := pos_eq_rightEnd_of_sepRight hs
  obtain ⟨hlt, -⟩ := hs
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlt1 : rightEnd i < 1 := by
    unfold rightEnd
    rw [div_lt_one hnR]
    have : (i.val : ℝ) + 1 < (n : ℝ) := by exact_mod_cast hlt
    linarith
  rw [hb.1] at hp
  linarith

/-! ## The border always agrees with the meet it competes with -/

/-- A drone at the right border that is also meeting its right-hand neighbour
would escort it leftward — the same answer the border gives. -/
theorem escortDir_eq_left_of_atRightBorder {c : Config n} {i : Fin n}
    (hb : c.AtRightBorder i) : c.escortDir i = Dir.left := by
  unfold escortDir
  rw [if_neg]
  rw [hb.1]
  have h1 : commonEnd i ≤ 1 := rightEnd_le_one i
  linarith

/-- And one at the left border meeting its left-hand neighbour would escort it
rightward — again the border's answer. -/
theorem escortDirLeft_eq_right_of_atLeftBorder {c : Config n} {i : Fin n}
    (hb : c.AtLeftBorder i) (hpos : 0 < i.val) : c.escortDirLeft i = Dir.right := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : (0 : ℝ) < leftEnd i := by
    unfold leftEnd
    have : (0 : ℝ) < (i.val : ℝ) := by exact_mod_cast hpos
    positivity
  unfold escortDirLeft
  rw [if_pos]
  rw [hb.1]; exact hle

/-! ## Separation agrees with the meet it competes with — three times out of
four -/

/-- A drone separating from its right-hand neighbour is standing on the
boundary they share, so a simultaneous meet would send it left too. -/
theorem escortDir_eq_left_of_sepRight {c : Config n} {i : Fin n}
    (hs : c.SepRight i) : c.escortDir i = Dir.left := by
  have hp : c.pos i = rightEnd i := pos_eq_rightEnd_of_sepRight hs
  unfold escortDir
  rw [if_neg]
  rw [hp]
  unfold commonEnd
  linarith

/-- The same drone, meeting its *left*-hand neighbour instead: still left,
because it is at its own right endpoint, far past its left one. -/
theorem escortDirLeft_eq_left_of_sepRight {c : Config n} {i : Fin n}
    (hs : c.SepRight i) : c.escortDirLeft i = Dir.left := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hp : c.pos i = rightEnd i := pos_eq_rightEnd_of_sepRight hs
  have hw : leftEnd i < rightEnd i := leftEnd_lt_rightEnd hn i
  unfold escortDirLeft
  rw [if_neg]
  rw [hp]
  linarith

/-- A drone separating from its *left*-hand neighbour is on its own left
endpoint; a simultaneous meet with the right-hand neighbour would send it
right, which is what the separation says. -/
theorem escortDir_eq_right_of_sepLeft {c : Config n} {i : Fin n}
    (hs : c.SepLeft i) : c.escortDir i = Dir.right := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hp : c.pos i = leftEnd i := pos_eq_leftEnd_of_sepLeft hs
  have hw : leftEnd i < rightEnd i := leftEnd_lt_rightEnd hn i
  unfold escortDir
  rw [if_pos]
  rw [hp]
  unfold commonEnd
  linarith

/-- **The single disagreement.** The same drone meeting its left-hand
neighbour: the meet would send it **left**, off the endpoint it is standing on,
while the separation sends it right, back into its own interval. -/
theorem escortDirLeft_eq_left_of_sepLeft {c : Config n} {i : Fin n}
    (hs : c.SepLeft i) : c.escortDirLeft i = Dir.left := by
  have hp : c.pos i = leftEnd i := pos_eq_leftEnd_of_sepLeft hs
  unfold escortDirLeft
  rw [if_neg]
  rw [hp]
  linarith

/-! ## The alternative resolution -/

open Classical in
/-- `newDir` with the priority of **separation** and **meet** exchanged. The
border still comes first — nothing competes with it. -/
noncomputable def newDirMeetFirst (c : Config n) (i : Fin n) : Dir :=
  if c.AtLeftBorder i then Dir.right
  else if c.AtRightBorder i then Dir.left
  else if c.MeetRight i then c.escortDir i
  else if c.MeetLeft i then c.escortDirLeft i
  else if c.SepRight i then Dir.left
  else if c.SepLeft i then Dir.right
  else c.dir i

/-- **The two resolutions agree except at a bounce.** Exchanging the priority
of separation and meet changes nothing unless a drone is simultaneously
separating from its left-hand neighbour and meeting it. -/
theorem newDirMeetFirst_eq_newDir {c : Config n} {i : Fin n}
    (hb : ¬ (c.SepLeft i ∧ c.MeetLeft i)) :
    c.newDirMeetFirst i = c.newDir i := by
  classical
  by_cases h1 : c.AtLeftBorder i
  · simp [newDirMeetFirst, newDir, h1]
  by_cases h2 : c.AtRightBorder i
  · simp [newDirMeetFirst, newDir, h1, h2]
  by_cases hsr : c.SepRight i
  · by_cases hmr : c.MeetRight i
    · simp [newDirMeetFirst, newDir, h1, h2, hsr, hmr,
        escortDir_eq_left_of_sepRight hsr]
    · by_cases hml : c.MeetLeft i
      · simp [newDirMeetFirst, newDir, h1, h2, hsr, hmr, hml,
          escortDirLeft_eq_left_of_sepRight hsr]
      · simp [newDirMeetFirst, newDir, h1, h2, hsr, hmr, hml]
  by_cases hsl : c.SepLeft i
  · by_cases hmr : c.MeetRight i
    · simp [newDirMeetFirst, newDir, h1, h2, hsr, hsl, hmr,
        escortDir_eq_right_of_sepLeft hsl]
    · have hml : ¬ c.MeetLeft i := fun hx => hb ⟨hsl, hx⟩
      simp [newDirMeetFirst, newDir, h1, h2, hsr, hsl, hmr, hml]
  · by_cases hmr : c.MeetRight i
    · simp [newDirMeetFirst, newDir, h1, h2, hsr, hsl, hmr]
    · by_cases hml : c.MeetLeft i
      · simp [newDirMeetFirst, newDir, h1, h2, hsr, hsl, hmr, hml]
      · simp [newDirMeetFirst, newDir, h1, h2, hsr, hsl, hmr, hml]

/-- **And at a bounce they differ**, in the one way that matters. -/
theorem newDirMeetFirst_of_bounce {c : Config n} {i : Fin n}
    (hsl : c.SepLeft i) (hml : c.MeetLeft i) :
    c.newDirMeetFirst i = Dir.left ∧ c.newDir i = Dir.right := by
  classical
  have h1 : ¬ c.AtLeftBorder i := fun hx => not_sepLeft_of_atLeftBorder hx hsl
  have h2 : ¬ c.AtRightBorder i := by
    rintro ⟨hp1, -⟩
    have hpl : c.pos i = leftEnd i := pos_eq_leftEnd_of_sepLeft hsl
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlt : leftEnd i < 1 := by
      unfold leftEnd
      rw [div_lt_one hnR]
      exact_mod_cast i.isLt
    rw [hp1] at hpl
    linarith
  have hmr : ¬ c.MeetRight i := fun hx => not_meetLeft_of_meetRight hx hml
  constructor
  · unfold newDirMeetFirst
    rw [if_neg h1, if_neg h2, if_neg hmr, if_pos hml,
      escortDirLeft_eq_left_of_sepLeft hsl]
  · have hnsr : ¬ c.SepRight i := fun hx => not_sepLeft_of_sepRight hx hsl
    unfold newDir
    rw [if_neg h1, if_neg h2, if_neg hnsr, if_pos hsl]

/-- **Why the bounce is not a free choice.** The drone is standing on its own
left endpoint, so the meet resolution walks it out of its own interval — the
failure the `n = 2` trace caught, and the reason `AtSeparation` does not demand
that the pair be escorting. The separation resolution is the protocol's. -/
theorem newDirMeetFirst_leaves_interval {c : Config n} {i : Fin n}
    (hsl : c.SepLeft i) (hml : c.MeetLeft i) {dt : ℝ} (hdt : 0 < dt) :
    ((c.setDir i (c.newDirMeetFirst i)).advance dt).pos i < leftEnd i := by
  have hd := (newDirMeetFirst_of_bounce hsl hml).1
  have hp : c.pos i = leftEnd i := pos_eq_leftEnd_of_sepLeft hsl
  show c.pos i + ((c.setDir i (c.newDirMeetFirst i)).dir i).sign * dt < leftEnd i
  rw [setDir_dir_self, hd, Dir.sign_left, hp]
  linarith

end Config

end DPSS
