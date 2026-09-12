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
precisely one of them has turned.

Only the border hypotheses are needed: the right drone cannot simultaneously be
separating from *its* right neighbour, since that would put it on two different
boundaries at once. -/
theorem someDroneTurns_of_separation {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (he : c.Escorting i h) (hs : c.AtSeparation i h)
    (hnl : ¬ c.AtLeftBorder i) (hnr : ¬ c.AtRightBorder i)
    (hnl' : ¬ c.AtLeftBorder (nextIdx i h))
    (hnr' : ¬ c.AtRightBorder (nextIdx i h)) : SomeDroneTurns c := by
  have hsame : c.pos (nextIdx i h) = c.pos i := by
    have hco : c.gap i h = 0 := he.1
    unfold gap at hco; linarith
  have hnext : 0 < (nextIdx i h).val := by simp only [nextIdx_val]; omega
  have hlt2 : commonEnd i < commonEnd (nextIdx i h) := commonEnd_lt_commonEnd_next i h
  -- the right drone is on *our* boundary, so not on its own
  have hns : ¬ c.SepRight (nextIdx i h) := by
    rintro ⟨_hh, _hc2, hp⟩
    rw [hsame, hs.2] at hp
    linarith
  have hi : c.newDir i = Dir.left := by
    unfold newDir
    rw [if_neg hnl, if_neg hnr, if_pos ⟨h, hs⟩]
  have hj : c.newDir (nextIdx i h) = Dir.right := by
    unfold newDir
    rw [if_neg hnl', if_neg hnr', if_neg hns, if_pos ⟨hnext, hs⟩]
  rcases Dir.eq_left_or_right (c.dir i) with hL | hR
  · refine ⟨nextIdx i h, ?_⟩
    rw [hj, ← he.2, hL]
    exact fun hc => Dir.noConfusion hc
  · refine ⟨i, ?_⟩
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

/-! ## Cascades

The theorems above exclude higher-priority events by hypothesis. This section
removes those hypotheses for the meet case, which is where cascades actually
bite: three or more drones arriving together, so that a drone meeting its right
neighbour may simultaneously be *separating* from its left one.

The argument is a case split on which branch of `newDir` claims each of the
two drones, and every branch is settled by arithmetic on the interval
endpoints. The recurring move: a drone cannot sit on two different boundaries
at once, and `leftEnd i < commonEnd i < commonEnd (i+1)`. -/

/-- The drone to the left of `i+1` is `i`. -/
theorem prevIdx_nextIdx (i : Fin n) (h : i.val + 1 < n)
    (h' : 0 < (nextIdx i h).val) : prevIdx (nextIdx i h) h' = i := by
  apply Fin.ext
  simp only [prevIdx_val, nextIdx_val]
  omega

/-- **Every meeting turns one of the pair, cascade or not.**

The only hypotheses are that the pair is genuinely meeting and that neither is
at a perimeter border — and a border would reverse that drone anyway, by
`someDroneTurns_of_atLeftBorder`. -/
theorem someDroneTurns_of_meet_due {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hco : c.CoLocated i h) (hA : c.Approaching i h)
    (hnl : ¬ c.AtLeftBorder i) (hnr : ¬ c.AtRightBorder i)
    (hnl' : ¬ c.AtLeftBorder (nextIdx i h))
    (hnr' : ¬ c.AtRightBorder (nextIdx i h)) : SomeDroneTurns c := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hsame : c.pos (nextIdx i h) = c.pos i := by
    unfold CoLocated gap at hco; linarith
  have hnext : 0 < (nextIdx i h).val := by simp only [nextIdx_val]; omega
  have hlt1 : leftEnd i < commonEnd i := by
    unfold commonEnd; exact leftEnd_lt_rightEnd hn i
  have hlt2 : commonEnd i < commonEnd (nextIdx i h) := commonEnd_lt_commonEnd_next i h
  -- the right drone's own pair events are impossible whenever the meeting
  -- point lies strictly before the shared boundary
  have right_turns : c.pos i < commonEnd i → SomeDroneTurns c := by
    intro hlt
    refine ⟨nextIdx i h, ?_⟩
    have hnsr' : ¬ c.SepRight (nextIdx i h) := by
      rintro ⟨_hh, _hc2, hp⟩
      rw [hsame] at hp
      linarith
    have hnsl' : ¬ c.SepLeft (nextIdx i h) := by
      rintro ⟨_hh, _hc2, hp⟩
      have hp' : c.pos i = commonEnd i := hp
      linarith
    have hnmr' : ¬ c.MeetRight (nextIdx i h) := by
      rintro ⟨_hh, _hc2, hAp⟩
      have hx := hAp.1
      rw [hA.2] at hx
      exact Dir.noConfusion hx
    have hml' : c.MeetLeft (nextIdx i h) := ⟨hnext, hco, hA⟩
    have hd : c.newDir (nextIdx i h) = Dir.right := by
      unfold newDir
      rw [if_neg hnl', if_neg hnr', if_neg hnsr', if_neg hnsl', if_neg hnmr',
        if_pos hml', escortDirLeft, if_pos]
      rw [hsame, leftEnd_next_eq_commonEnd i h]
      exact hlt
    rw [hd, hA.2]
    exact fun hc => Dir.noConfusion hc
  by_cases hsr : c.SepRight i
  · -- separating from us outright reverses the left drone
    refine ⟨i, ?_⟩
    have hd : c.newDir i = Dir.left := by
      unfold newDir; rw [if_neg hnl, if_neg hnr, if_pos hsr]
    rw [hd, hA.1]
    exact fun hc => Dir.noConfusion hc
  · by_cases hsl : c.SepLeft i
    · -- the left drone is pinned to its own left endpoint, strictly before the
      -- shared boundary, so the right drone reverses
      have hp := pos_eq_leftEnd_of_sepLeft hsl
      exact right_turns (by rw [hp]; exact hlt1)
    · rcases lt_or_ge (c.pos i) (commonEnd i) with hlt | hge
      · exact right_turns hlt
      · -- meeting at or beyond the boundary: the pair heads left, so the left
        -- drone (which was heading right) reverses
        refine ⟨i, ?_⟩
        have hd : c.newDir i = Dir.left := by
          unfold newDir
          rw [if_neg hnl, if_neg hnr, if_neg hsr, if_neg hsl,
            if_pos ⟨h, hco, hA⟩, escortDir, if_neg (by linarith)]
        rw [hd, hA.1]
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

/-! ## A1, assembled

Every step of the system reverses at least one drone. No hypotheses at all.

The proof picks the drone whose deadline attained the minimum, splits on which
of its three deadlines that was, and discharges each with the results above.
Borders are handled first and unconditionally, so the meet and separation cases
may assume no drone is at a border — which is exactly what they need. -/

/-- **Every step turns a drone.**

With `turn_separation` (consecutive turns of one drone are at least `1/n`
apart) this is the other half of non-Zeno: `k` steps force turns, turns are
spaced, so time cannot stand still. -/
theorem someDroneTurns_step {c : Config n} (hn : 0 < n) :
    SomeDroneTurns (c.advance (c.timeToNextEvent hn)) := by
  by_cases hb : ∃ j : Fin n,
      (c.advance (c.timeToNextEvent hn)).AtLeftBorder j ∨
        (c.advance (c.timeToNextEvent hn)).AtRightBorder j
  · obtain ⟨j, hj | hj⟩ := hb
    · exact someDroneTurns_of_atLeftBorder hj
    · exact someDroneTurns_of_atRightBorder hj
  · simp only [not_exists, not_or] at hb
    obtain ⟨k, -, hk⟩ :=
      Finset.exists_mem_eq_inf' (univ_fin_nonempty hn) c.droneNextTime
    have hmin : c.timeToNextEvent hn = c.droneNextTime k := hk
    unfold droneNextTime at hmin
    split_ifs at hmin with hh hAp hEp
    · rcases min_cases (c.borderTime k) (c.meetTime k hh) with ⟨he, -⟩ | ⟨he, -⟩
      · exact someDroneTurns_of_border_deadline hn k (by rw [hmin, he])
      · have hmeet := meet_due_of_meet_deadline hn hAp (by rw [hmin, he])
        exact someDroneTurns_of_meet_due hmeet.1 hmeet.2 (hb k).1 (hb k).2
          (hb (nextIdx k hh)).1 (hb (nextIdx k hh)).2
    · rcases min_cases (c.borderTime k) (c.separationTime k) with ⟨he, -⟩ | ⟨he, -⟩
      · exact someDroneTurns_of_border_deadline hn k (by rw [hmin, he])
      · have hsep := separation_due_of_separation_deadline hn hEp (by rw [hmin, he])
        have he' : (c.advance (c.timeToNextEvent hn)).Escorting k hh :=
          ⟨coLocated_advance_of_escorting hEp _, by simpa using hEp.2⟩
        exact someDroneTurns_of_separation he' hsep (hb k).1 (hb k).2
          (hb (nextIdx k hh)).1 (hb (nextIdx k hh)).2
    · exact someDroneTurns_of_border_deadline hn k hmin
    · exact someDroneTurns_of_border_deadline hn k hmin

/-- Restated on the run: every step from any configuration turns a drone. -/
theorem someDroneTurns_run {c : Config n} (hn : 0 < n) (k : ℕ) :
    ∃ i : Fin n, (c.run hn (k + 1)).dir i ≠ (c.run hn k).dir i := by
  obtain ⟨i, hi⟩ := someDroneTurns_step (c := c.run hn k) hn
  exact ⟨i, hi⟩

end Config

end DPSS
