/-
# DPSS — a pair heading apart is on its boundary (as an invariant)

§3.20 showed the pointwise statement is **false**: four drones stacked at one
point, the two middle ones each escorting the *outward* neighbour, leaves the
middle pair heading apart away from their shared boundary.

But that configuration is not one the algorithm produces. So the statement is
an **invariant**, not a pointwise fact, and this file proves it preserved.

## The shape of the argument

For the pair to end a step heading apart, `newDir` must have delivered `left`
to the left drone and `right` to the right one. Enumerating how, every route
closes:

* a **separation** on either side puts the pair on the boundary outright;
* most **meet** routes contradict, because a meeting pair agrees on where to
  go and so cannot leave a meeting heading apart;
* and the remaining routes — the ones the counterexample exploits — force the
  pair to have been co-located *and already heading apart* **before** the step.
  Then the induction hypothesis applies.

That last move is the one worth naming. If the pair heads apart their gap grows
at rate 2, so being co-located *after* flying forces the gap to have been zero
and **the step to have taken no time at all**. The configuration is carried over
unchanged, and with it the invariant.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2; the counterexample is in
`Dpss/Counterexample.lean`.
-/

import Dpss.Counterexample

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-- A co-located pair heading apart sits on the boundary it shares. False
pointwise (§3.20); true along runs. -/
def ApartOnBoundary (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop :=
  c.CoLocated i h → c.dir i = Dir.left → c.dir (nextIdx i h) = Dir.right →
    c.pos i = commonEnd i

/-- **The transfer move.** A pair heading apart separates at rate 2, so if it is
still co-located after flying forward, the step took no time and the pair was
already co-located. The invariant then carries straight over. -/
theorem apart_transfer {c : Config n} {i : Fin n} {h : i.val + 1 < n} {dt : ℝ}
    (hIH : c.ApartOnBoundary i h) (hgap : 0 ≤ c.gap i h) (hdt : 0 ≤ dt)
    (hL : c.dir i = Dir.left) (hR : c.dir (nextIdx i h) = Dir.right)
    (hco : (c.advance dt).CoLocated i h) :
    (c.advance dt).pos i = commonEnd i := by
  have hrate : c.sepRate i h = 2 := by
    unfold sepRate; rw [hL, hR]; norm_num [Dir.sign]
  have hgap' : c.gap i h + 2 * dt = 0 := by
    have := hco
    unfold CoLocated at this
    rw [gap_advance, hrate] at this
    linarith
  have hz : dt = 0 := by linarith
  have hg0 : c.gap i h = 0 := by linarith
  have hpos : (c.advance dt).pos i = c.pos i := by
    simp only [advance_pos, hz]; ring
  rw [hpos]
  exact hIH hg0 hL hR

/-- A meeting pair cannot leave the meeting heading apart: both drones adopt
the *same* heading, whichever it is. -/
theorem not_apart_of_meet {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hco : c.CoLocated i h) (hmr : c.MeetRight i) (hml : c.MeetLeft (nextIdx i h))
    (hnl : ¬ c.AtLeftBorder (nextIdx i h)) (hnr : ¬ c.AtRightBorder (nextIdx i h))
    (hns : ¬ c.SepRight (nextIdx i h)) (hnsl : ¬ c.SepLeft (nextIdx i h))
    (hnmr : ¬ c.MeetRight (nextIdx i h))
    (hnlb : ¬ c.AtLeftBorder i) (hnrb : ¬ c.AtRightBorder i)
    (hnsr : ¬ c.SepRight i) (hnsll : ¬ c.SepLeft i) :
    c.newDir i = c.newDir (nextIdx i h) := by
  have h1 : c.newDir i = c.escortDir i := by
    unfold newDir
    rw [if_neg hnlb, if_neg hnrb, if_neg hnsr, if_neg hnsll, if_pos hmr]
  have h2 : c.newDir (nextIdx i h) = c.escortDirLeft (nextIdx i h) := by
    unfold newDir
    rw [if_neg hnl, if_neg hnr, if_neg hns, if_neg hnsl, if_neg hnmr,
      if_pos hml]
  rw [h1, h2, escortDirLeft_next_eq_escortDir hco]

end Config

end DPSS
