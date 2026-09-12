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

end Config

end DPSS
