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

/-! ## The preservation theorem

Enumerating how `newDir` could deliver `left` to the left drone and `right` to
the right one. A separation on either side settles it outright; otherwise the
pair must already have been heading apart, and `apart_transfer` applies. -/

/-- Given that neither drone is separating, the left one must already have been
heading left. -/
theorem dir_left_of_newDir_apart {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hco : c.CoLocated i h) (hL : c.newDir i = Dir.left)
    (hR : c.newDir (nextIdx i h) = Dir.right)
    (hnsr : ¬ c.SepRight i) (hnsl : ¬ c.SepLeft (nextIdx i h))
    (hp : c.OnPerimeter) : c.dir i = Dir.left := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hsame : c.pos (nextIdx i h) = c.pos i := by
    unfold CoLocated gap at hco; linarith
  have hce0 : 0 < commonEnd i := by
    have h1 := leftEnd_nonneg i
    have h2 : leftEnd i < commonEnd i := by
      unfold commonEnd; exact leftEnd_lt_rightEnd hn i
    linarith
  have hce1 : commonEnd i ≤ 1 := by unfold commonEnd; exact rightEnd_le_one i
  have hlen : leftEnd (nextIdx i h) = commonEnd i := leftEnd_next_eq_commonEnd i h
  -- rule out the two routes that would leave it heading right
  rcases newDir_left_cases hL with hb | hs | ⟨hm, hge⟩ | ⟨hm, -⟩ | hd
  · -- at the right border: then its partner is there too, and nothing can
    -- turn the partner rightward
    exfalso
    have hp1 : c.pos i = 1 := hb.1
    rcases newDir_right_cases hR with hb' | hs' | ⟨hm', hlt'⟩ | ⟨hm', hlt'⟩ | hd'
    · have : c.pos (nextIdx i h) = 0 := hb'.1
      rw [hsame, hp1] at this; norm_num at this
    · exact hnsl hs'
    · have hdj : c.dir (nextIdx i h) = Dir.right := hm'.2.2.1
      have hbr : c.AtRightBorder (nextIdx i h) := ⟨by rw [hsame, hp1], hdj⟩
      have hnal : ¬ c.AtLeftBorder (nextIdx i h) := by
        rintro ⟨hz, -⟩; rw [hsame, hp1] at hz; norm_num at hz
      rw [newDir_atRightBorder hnal hbr] at hR
      exact Dir.noConfusion hR
    · rw [hsame, hlen, hp1] at hlt'; linarith
    · have hbr : c.AtRightBorder (nextIdx i h) := ⟨by rw [hsame, hp1], hd'⟩
      have hnal : ¬ c.AtLeftBorder (nextIdx i h) := by
        rintro ⟨hz, -⟩; rw [hsame, hp1] at hz; norm_num at hz
      rw [newDir_atRightBorder hnal hbr] at hR
      exact Dir.noConfusion hR
  · exact absurd hs hnsr
  · -- meeting its right neighbour beyond the boundary: the partner is then
    -- heading left and nothing can turn it rightward
    exfalso
    have hdj : c.dir (nextIdx i h) = Dir.left := hm.2.2.2
    rcases newDir_right_cases hR with hb' | hs' | ⟨hm', hlt'⟩ | ⟨hm', hlt'⟩ | hd'
    · have hz : c.pos (nextIdx i h) = 0 := hb'.1
      rw [hsame] at hz; rw [hz] at hge; exact hge hce0
    · exact hnsl hs'
    · rw [hm'.2.2.1] at hdj; exact Dir.noConfusion hdj
    · rw [hsame, hlen] at hlt'; exact hge hlt'
    · rw [hd'] at hdj; exact Dir.noConfusion hdj
  · -- meeting its *left* neighbour: that requires heading left
    obtain ⟨hz, -, hA⟩ := hm
    have := hA.2
    rwa [nextIdx_prevIdx] at this
  · exact hd

/-- And then the right drone must already have been heading right. -/
theorem dir_right_of_newDir_apart {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hco : c.CoLocated i h) (hL : c.newDir i = Dir.left)
    (hR : c.newDir (nextIdx i h) = Dir.right)
    (hnsl : ¬ c.SepLeft (nextIdx i h)) (hdi : c.dir i = Dir.left) :
    c.dir (nextIdx i h) = Dir.right := by
  have hsame : c.pos (nextIdx i h) = c.pos i := by
    unfold CoLocated gap at hco; linarith
  rcases newDir_right_cases hR with hb' | hs' | ⟨hm', -⟩ | ⟨hm', -⟩ | hd'
  · -- its partner at the left border puts *this* drone there too, and a drone
    -- at the left border heading left turns rightward
    exfalso
    have hz : c.pos (nextIdx i h) = 0 := hb'.1
    rw [hsame] at hz
    rw [newDir_atLeftBorder ⟨hz, hdi⟩] at hL
    exact Dir.noConfusion hL
  · exact absurd hs' hnsl
  · exact hm'.2.2.1
  · -- meeting *us* requires us to be heading right
    exfalso
    obtain ⟨hz, -, hA⟩ := hm'
    have hx := hA.1
    rw [prevIdx_nextIdx i h hz, hdi] at hx
    exact Dir.noConfusion hx
  · exact hd'

/-- **The invariant is preserved by a step.** -/
theorem apartOnBoundary_step {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hIH : ∀ (i : Fin n) (h : i.val + 1 < n), c.ApartOnBoundary i h)
    (i : Fin n) (h : i.val + 1 < n) : (c.step hn).ApartOnBoundary i h := by
  intro hco hL hR
  set dt := c.timeToNextEvent hn with hdtdef
  have hdt : 0 ≤ dt :=
    timeToNextEvent_nonneg hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent
  have hco' : (c.advance dt).CoLocated i h := hco
  have hL' : (c.advance dt).newDir i = Dir.left := hL
  have hR' : (c.advance dt).newDir (nextIdx i h) = Dir.right := hR
  by_cases hsr : (c.advance dt).SepRight i
  · exact pos_eq_commonEnd_of_sepRight hsr
  by_cases hsl : (c.advance dt).SepLeft (nextIdx i h)
  · exact pos_eq_commonEnd_of_sepLeft_next hsl
  have hpa : (c.advance dt).OnPerimeter := by
    have := onPerimeter_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent
    exact this
  have hdi : (c.advance dt).dir i = Dir.left :=
    dir_left_of_newDir_apart hco' hL' hR' hsr hsl hpa
  have hdj : (c.advance dt).dir (nextIdx i h) = Dir.right :=
    dir_right_of_newDir_apart hco' hL' hR' hsl hdi
  exact apart_transfer (hIH i h) (hi.adjOrdered i h) hdt hdi hdj hco'

end Config

end DPSS
