/-
# DPSS — every scheduled event turns a drone

This is the first piece of the non-Zeno argument (**A1** in the work package),
and it is independent of the convergence lemmas.

## Why it is needed

`Turning.lean` showed consecutive turns of one drone are at least `1/n` apart
in time. To convert that into "only finitely many events fit in a bounded
interval" we need the other half: **each event actually turns somebody**. Then
`k` steps force some drone to turn about `k/n` times, and the `1/n` spacing
bounds the elapsed time from below.

## The three cases

A step's length is set by whichever deadline comes first, and there are only
three kinds:

* a **border** deadline — the drone reaches the perimeter edge and reverses;
* a **meet** deadline — an approaching pair becomes co-located;
* a **separation** deadline — an escorting pair reaches its shared boundary.

Each is handled below. The meet case turns on a small identity worth naming on
its own: when a pair is co-located, the heading the *left* drone adopts on
meeting its right neighbour and the heading the *right* drone adopts on meeting
its left neighbour are **the same direction**. That is what makes an escort an
escort, and it is why a meet always reverses exactly one of the two.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2.
-/

import Dpss.PairBalance

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-- At least one drone reverses across this step. -/
def SomeDroneTurns (c : Config n) : Prop :=
  ∃ i : Fin n, c.newDir i ≠ c.dir i

/-! ## Border deadlines -/

theorem someDroneTurns_of_atLeftBorder {c : Config n} {i : Fin n}
    (h : c.AtLeftBorder i) : SomeDroneTurns c := by
  refine ⟨i, ?_⟩
  rw [newDir_atLeftBorder h, h.2]
  exact fun hc => Dir.noConfusion hc

/-- A drone cannot be at both ends of the perimeter at once. -/
theorem not_atLeftBorder_of_atRightBorder {c : Config n} {i : Fin n}
    (h : c.AtRightBorder i) : ¬ c.AtLeftBorder i := by
  rintro ⟨hp, -⟩
  rw [h.1] at hp
  norm_num at hp

theorem someDroneTurns_of_atRightBorder {c : Config n} {i : Fin n}
    (h : c.AtRightBorder i) : SomeDroneTurns c := by
  refine ⟨i, ?_⟩
  rw [newDir_atRightBorder (not_atLeftBorder_of_atRightBorder h) h, h.2]
  exact fun hc => Dir.noConfusion hc

/-! ## Separation deadlines -/

/-- **An escorting pair that separates always reverses exactly one of its two
drones.** They arrived heading the same way and leave heading opposite ways, so
precisely one of them has turned. -/
theorem someDroneTurns_of_separation {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (he : c.Escorting i h) (hs : c.AtSeparation i h)
    (hnl : ¬ c.AtLeftBorder i) (hnr : ¬ c.AtRightBorder i)
    (hnl' : ¬ c.AtLeftBorder (nextIdx i h))
    (hnr' : ¬ c.AtRightBorder (nextIdx i h))
    (hns : ¬ c.SepRight (nextIdx i h)) : SomeDroneTurns c := by
  have hi : c.newDir i = Dir.left := by
    unfold newDir
    rw [if_neg hnl, if_neg hnr, if_pos ⟨h, hs⟩]
  have hj : c.newDir (nextIdx i h) = Dir.right := by
    unfold newDir
    rw [if_neg hnl', if_neg hnr', if_neg hns,
      if_pos ⟨by simp only [nextIdx_val]; omega, hs⟩]
  rcases Dir.eq_left_or_right (c.dir i) with hL | hR
  · -- the pair was heading left, so the right-hand drone reverses
    refine ⟨nextIdx i h, ?_⟩
    rw [hj, ← he.2, hL]
    exact fun hc => Dir.noConfusion hc
  · -- the pair was heading right, so the left-hand drone reverses
    refine ⟨i, ?_⟩
    rw [hi, hR]
    exact fun hc => Dir.noConfusion hc

/-! ## Meet deadlines -/

/-- **A meeting pair agrees on where to go.** The heading the left drone adopts
on meeting its right neighbour equals the heading the right drone adopts on
meeting its left neighbour. This is what makes an escort an escort. -/
theorem escortDirLeft_next_eq_escortDir {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hco : c.CoLocated i h) :
    c.escortDirLeft (nextIdx i h) = c.escortDir i := by
  unfold CoLocated gap at hco
  have hEq : c.pos (nextIdx i h) = c.pos i := by linarith
  unfold escortDirLeft escortDir
  rw [hEq, leftEnd_next_eq_commonEnd i h]

/-- **A meet always reverses exactly one of the pair.** They arrive heading
opposite ways and leave heading the same way, so one of them must have
turned. -/
theorem someDroneTurns_of_meet {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hco : c.CoLocated i h) (hA : c.Approaching i h)
    (hnl : ¬ c.AtLeftBorder i) (hnr : ¬ c.AtRightBorder i)
    (hns : ¬ c.SepRight i) (hnsl : ¬ c.SepLeft i)
    (hnl' : ¬ c.AtLeftBorder (nextIdx i h))
    (hnr' : ¬ c.AtRightBorder (nextIdx i h))
    (hns' : ¬ c.SepRight (nextIdx i h))
    (hns'' : ¬ c.SepLeft (nextIdx i h))
    (hnm' : ¬ c.MeetRight (nextIdx i h)) : SomeDroneTurns c := by
  have hi : c.newDir i = c.escortDir i := by
    unfold newDir
    rw [if_neg hnl, if_neg hnr, if_neg hns, if_neg hnsl, if_pos ⟨h, hco, hA⟩]
  have hj : c.newDir (nextIdx i h) = c.escortDir i := by
    unfold newDir
    rw [if_neg hnl', if_neg hnr', if_neg hns', if_neg hns'', if_neg hnm',
      if_pos ⟨by simp only [nextIdx_val]; omega, hco, hA⟩]
    exact escortDirLeft_next_eq_escortDir hco
  rcases Dir.eq_left_or_right (c.escortDir i) with hL | hR
  · -- the pair heads left, so the left-hand drone (which was heading right)
    -- reverses
    refine ⟨i, ?_⟩
    rw [hi, hL, hA.1]
    exact fun hc => Dir.noConfusion hc
  · -- the pair heads right, so the right-hand drone reverses
    refine ⟨nextIdx i h, ?_⟩
    rw [hj, hR, hA.2]
    exact fun hc => Dir.noConfusion hc

/-! ## Border deadlines are never spurious

`STATUS.md` carried a worry for many commits: `timeToNextEvent` minimises over
`borderTime` for *every* drone, including interior ones where no border event
looked reachable, so the minimum might report a deadline with **no event behind
it**.

That worry was overstated, and this settles it. Flying drone `i` for exactly
`borderTime i` lands it on `0` or `1` — that is what the quantity *is*. At that
point `AtLeftBorder` or `AtRightBorder` genuinely holds and the event genuinely
fires. Ordering makes it coherent too: if an interior drone reaches `0`, every
drone to its left is already there, and they all bounce together.

So a border deadline is always real, whichever drone it belongs to. -/

/-- Flying a drone for exactly its border deadline puts it on a border. -/
theorem atBorder_of_advance_borderTime (c : Config n) (i : Fin n) :
    (c.advance (c.borderTime i)).AtLeftBorder i ∨
      (c.advance (c.borderTime i)).AtRightBorder i := by
  rcases Dir.eq_left_or_right (c.dir i) with hd | hd
  · exact Or.inl (by rw [borderTime_of_left hd]; exact atLeftBorder_at_leftBorderTime hd)
  · exact Or.inr (by rw [borderTime_of_right hd]; exact atRightBorder_at_rightBorderTime hd)

/-- **A step whose length is set by a border deadline turns a drone.**

Unconditional — no assumption about which drone, and no priority reasoning,
because a border event outranks everything else in `newDir`. -/
theorem someDroneTurns_of_border_deadline {c : Config n} (hn : 0 < n)
    (i : Fin n) (hmin : c.timeToNextEvent hn = c.borderTime i) :
    SomeDroneTurns (c.advance (c.timeToNextEvent hn)) := by
  rw [hmin]
  rcases atBorder_of_advance_borderTime c i with h | h
  · exact someDroneTurns_of_atLeftBorder h
  · exact someDroneTurns_of_atRightBorder h

/-! ## Meet deadlines really do produce meetings -/

/-- A step whose length is set by an approaching pair's meeting time really
does bring that pair together, still closing. Whether the resulting *turn*
happens to that pair or to another drone depends on which event wins the
priority order in `newDir`, which is the part still open. -/
theorem meet_due_of_meet_deadline {c : Config n} (hn : 0 < n) {i : Fin n}
    {h : i.val + 1 < n} (hA : c.Approaching i h)
    (hmin : c.timeToNextEvent hn = c.meetTime i h) :
    (c.advance (c.timeToNextEvent hn)).CoLocated i h ∧
      (c.advance (c.timeToNextEvent hn)).Approaching i h := by
  rw [hmin]
  refine ⟨coLocated_at_meetTime hA, ?_, ?_⟩
  · simpa using hA.1
  · simpa using hA.2

/-- Likewise a separation deadline really does bring an escorting pair to the
boundary it shares. -/
theorem separation_due_of_separation_deadline {c : Config n} (hn : 0 < n)
    {i : Fin n} {h : i.val + 1 < n} (he : c.Escorting i h)
    (hmin : c.timeToNextEvent hn = c.separationTime i) :
    (c.advance (c.timeToNextEvent hn)).AtSeparation i h := by
  rw [hmin]
  exact atSeparation_at_separationTime he

end Config

end DPSS
