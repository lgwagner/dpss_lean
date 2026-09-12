/-
# DPSS — an approaching pair meets

Towards **Lemma 3.5** (*every adjacent pair has met by time 1*).

This file establishes the part that does not need the paper's phase
bookkeeping: **once the left drone heads right and the right drone heads left,
they meet, and within half their gap.**

The reason it is clean is a fact that falls out of work done for Lemma 3.2:

> a drone heading right can only reverse by becoming **co-located with its
> right-hand neighbour** (`coLocated_of_turnsLeft`), and a drone heading left
> can only reverse by becoming co-located with its **left-hand** neighbour
> (`coLocated_of_turnsRight`).

So while an approaching pair stays apart, *neither drone can turn*. Their gap
therefore shrinks at a steady rate 2 until it reaches zero, and non-Zeno
guarantees the clock gets there.

## Reference

Avigad–van Doorn, arXiv:2008.04262, Lemma 3.5.
-/

import Dpss.BalanceInvariant

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Headings persist while a pair stays apart -/

/-- A drone heading right keeps heading right for as long as it does not turn
leftward. (A rightward drone cannot turn *rightward*, so nothing else can
change it.) -/
theorem dir_right_of_no_turnsLeft {c : Config n} (hn : 0 < n) {i : Fin n}
    {a b : ℕ} (hab : a ≤ b)
    (hno : ∀ p, a ≤ p → p < b → ¬ TurnsLeftAt c hn i p)
    (ha : (c.run hn a).dir i = Dir.right) :
    ∀ p, a ≤ p → p ≤ b → (c.run hn p).dir i = Dir.right := by
  have key : ∀ q : ℕ, a + q ≤ b → (c.run hn (a + q)).dir i = Dir.right := by
    intro q
    induction q with
    | zero => intro _; simpa using ha
    | succ q ih =>
      intro hq
      have hprev := ih (by omega)
      by_contra hne
      have hL : (c.run hn (a + (q + 1))).dir i = Dir.left := by
        rcases Dir.eq_left_or_right ((c.run hn (a + (q + 1))).dir i) with hx | hx
        · exact hx
        · exact absurd hx hne
      exact hno (a + q) (by omega) (by omega) ⟨hprev, by
        rw [show a + q + 1 = a + (q + 1) from rfl]; exact hL⟩
  intro p hp1 hp2
  have hk := key (p - a) (by omega)
  rwa [show a + (p - a) = p from by omega] at hk

/-- Symmetrically, a drone heading left keeps heading left while it does not
turn rightward. -/
theorem dir_left_of_no_turnsRight {c : Config n} (hn : 0 < n) {i : Fin n}
    {a b : ℕ} (hab : a ≤ b)
    (hno : ∀ p, a ≤ p → p < b → ¬ TurnsRightAt c hn i p)
    (ha : (c.run hn a).dir i = Dir.left) :
    ∀ p, a ≤ p → p ≤ b → (c.run hn p).dir i = Dir.left := by
  have key : ∀ q : ℕ, a + q ≤ b → (c.run hn (a + q)).dir i = Dir.left := by
    intro q
    induction q with
    | zero => intro _; simpa using ha
    | succ q ih =>
      intro hq
      have hprev := ih (by omega)
      by_contra hne
      have hR : (c.run hn (a + (q + 1))).dir i = Dir.right := by
        rcases Dir.eq_left_or_right ((c.run hn (a + (q + 1))).dir i) with hx | hx
        · exact absurd hx hne
        · exact hx
      exact hno (a + q) (by omega) (by omega) ⟨hprev, by
        rw [show a + q + 1 = a + (q + 1) from rfl]; exact hR⟩
  intro p hp1 hp2
  have hk := key (p - a) (by omega)
  rwa [show a + (p - a) = p from by omega] at hk

/-- **The right drone of a pair cannot turn rightward while the pair is
apart** — turning rightward would put it on top of its left-hand neighbour,
which is the left drone of this very pair. -/
theorem not_turnsRightAt_of_never_coLocated {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {h : i.val + 1 < n} {a b : ℕ}
    (hnc : ∀ p, a < p → p ≤ b → ¬ (c.run hn p).CoLocated i h) :
    ∀ p, a ≤ p → p < b → ¬ TurnsRightAt c hn (nextIdx i h) p := by
  intro p hp1 hp2 ht
  have hinv := invariant_run hn hi (p + 1)
  have hpos : 0 < (nextIdx i h).val := by simp only [nextIdx_val]; omega
  have hco : (c.run hn (p + 1)).CoLocated (prevIdx (nextIdx i h) hpos)
      (prevIdx_lt (nextIdx i h) hpos) :=
    coLocated_of_turnsRight (c := (c.run hn p).advance
        ((c.run hn p).timeToNextEvent hn))
      hinv.onPerimeter (ordered_of_adjOrdered hinv.adjOrdered) hpos ⟨ht.1, ht.2⟩
  refine hnc (p + 1) (by omega) (by omega) ?_
  exact (coLocated_congr (c.run hn (p + 1)) _ h (prevIdx_nextIdx i h hpos)).mp hco

/-! ## The gap of an approaching pair shrinks at a steady rate -/

/-- While the pair stays apart and approaching, the gap closes at rate 2. -/
theorem gap_of_approaching {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} {a m : ℕ}
    (hR : (c.run hn a).dir i = Dir.right)
    (hL : (c.run hn a).dir (nextIdx i h) = Dir.left)
    (hnc : ∀ p, a < p → p < a + m → ¬ (c.run hn p).CoLocated i h) :
    (c.run hn (a + m)).gap i h
      = (c.run hn a).gap i h
        - 2 * ((c.run hn (a + m)).time - (c.run hn a).time) := by
  -- the hypothesis is open at the top: co-location *at* `a + m` is allowed,
  -- which is exactly the case we want to apply this to
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0; simp
  -- neither drone turns strictly before the end, so both positions track
  -- elapsed time across the whole stretch
  have hnc' : ∀ p, a < p → p ≤ a + m - 1 → ¬ (c.run hn p).CoLocated i h :=
    fun p hp1 hp2 => hnc p hp1 (by omega)
  have hnoL : ∀ p, a ≤ p → p < a + m - 1 → ¬ TurnsLeftAt c hn i p :=
    not_turnsLeftAt_of_never_coLocated hn hi hnc'
  have hnoR : ∀ p, a ≤ p → p < a + m - 1 →
      ¬ TurnsRightAt c hn (nextIdx i h) p :=
    not_turnsRightAt_of_never_coLocated hn hi hnc'
  have hdirL : ∀ p, a ≤ p → p ≤ a + m - 1 → (c.run hn p).dir i = Dir.right :=
    dir_right_of_no_turnsLeft hn (by omega) hnoL hR
  have hdirR : ∀ p, a ≤ p → p ≤ a + m - 1 →
      (c.run hn p).dir (nextIdx i h) = Dir.left :=
    dir_left_of_no_turnsRight hn (by omega) hnoR hL
  have h1 := pos_sub_eq_of_dirConst hn i a m
    (fun p hp1 hp2 => by rw [hdirL p hp1 (by omega), hR])
  have h2 := pos_sub_eq_of_dirConst hn (nextIdx i h) a m
    (fun p hp1 hp2 => by rw [hdirR p hp1 (by omega), hL])
  rw [hR, Dir.sign_right, one_mul] at h1
  rw [hL, Dir.sign_left] at h2
  unfold gap
  linarith

/-! ## An approaching pair meets, within half its gap

The clock cannot stall (`nonZeno`), the gap closes at a steady rate 2, and the
gap cannot go negative — so the meeting happens, and at exactly the moment the
gap would reach zero. -/

/-- **An approaching pair becomes co-located, within half its gap.** -/
theorem exists_coLocated_of_approaching {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {h : i.val + 1 < n} {a : ℕ}
    (hR : (c.run hn a).dir i = Dir.right)
    (hL : (c.run hn a).dir (nextIdx i h) = Dir.left) :
    ∃ m, a ≤ m ∧ (c.run hn m).CoLocated i h ∧
      (c.run hn m).time ≤ (c.run hn a).time + (c.run hn a).gap i h / 2 := by
  classical
  have hg0 : 0 ≤ (c.run hn a).gap i h := (invariant_run hn hi a).adjOrdered i h
  -- somewhere past the moment the gap would reach zero
  obtain ⟨q, hq⟩ := nonZeno hn hi ((c.run hn a).time + (c.run hn a).gap i h / 2)
  have hqa : a ≤ q := by
    by_contra hlt
    have := time_mono_run' hn hi (k := q) (j := a) (by omega)
    linarith
  -- the pair must become co-located somewhere in between
  have hex : ∃ m : ℕ, a + m ≤ q ∧ (c.run hn (a + m)).CoLocated i h := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hnc : ∀ p, a < p → p < q → ¬ (c.run hn p).CoLocated i h := by
      intro p hp1 hp2
      have := hcon (p - a) (by omega)
      rwa [show a + (p - a) = p from by omega] at this
    have hkey := gap_of_approaching hn hi hR hL
      (m := q - a) (by intro p hp1 hp2; exact hnc p hp1 (by omega))
    rw [show a + (q - a) = q from by omega] at hkey
    have hgq : 0 ≤ (c.run hn q).gap i h := (invariant_run hn hi q).adjOrdered i h
    linarith
  -- take the first such moment
  let P : ℕ → Prop := fun m => a + m ≤ q ∧ (c.run hn (a + m)).CoLocated i h
  have hP : ∃ m, P m := hex
  refine ⟨a + Nat.find hP, by omega, (Nat.find_spec hP).2, ?_⟩
  have hfq : a + Nat.find hP ≤ q := (Nat.find_spec hP).1
  have hmin : ∀ p, a < p → p < a + Nat.find hP → ¬ (c.run hn p).CoLocated i h := by
    intro p hp1 hp2 hco
    exact (Nat.find_min hP (m := p - a) (by omega))
      ⟨by omega, by rwa [show a + (p - a) = p from by omega]⟩
  have hkey := gap_of_approaching hn hi hR hL (m := Nat.find hP) hmin
  have hzero : (c.run hn (a + Nat.find hP)).gap i h = 0 := (Nat.find_spec hP).2
  rw [hzero] at hkey
  linarith

/-! ## The first turn, and exactly when it happens

Lemma 3.5's arithmetic needs not a bound on when each drone first reverses but
the **exact** elapsed time: a drone travelling in one direction covers distance
equal to time, so the moment it turns is pinned by *where* it turns. That is
the paper's `w` and `z`. -/

/-- **The first moment a drone heads right**, together with where it was
heading until then and exactly how long that took. -/
theorem exists_firstRight {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (i : Fin n) (a : ℕ) :
    ∃ b, a ≤ b ∧ (c.run hn b).dir i = Dir.right ∧
      (∀ p, a ≤ p → p < b → (c.run hn p).dir i = Dir.left) ∧
      (c.run hn b).time - (c.run hn a).time
        = (c.run hn a).pos i - (c.run hn b).pos i := by
  classical
  rcases Dir.eq_left_or_right ((c.run hn a).dir i) with hL | hR
  · -- heading left: it must turn eventually, and the first such moment is the
    -- one we want
    have hex : ∃ m : ℕ, (c.run hn (a + m)).dir i = Dir.right := by
      obtain ⟨q, hq, hd⟩ := exists_dir_right_of_dir_left hn hi hL
      exact ⟨q - a, by rwa [show a + (q - a) = q from by omega]⟩
    refine ⟨a + Nat.find hex, by omega, Nat.find_spec hex, ?_, ?_⟩
    · intro p hp1 hp2
      rcases Dir.eq_left_or_right ((c.run hn p).dir i) with hx | hx
      · exact hx
      · exact absurd (by rwa [show a + (p - a) = p from by omega])
          (Nat.find_min hex (m := p - a) (by omega))
    · have hconst : ∀ p, a ≤ p → p < a + Nat.find hex →
          (c.run hn p).dir i = (c.run hn a).dir i := by
        intro p hp1 hp2
        rw [hL]
        rcases Dir.eq_left_or_right ((c.run hn p).dir i) with hx | hx
        · exact hx
        · exact absurd (by rwa [show a + (p - a) = p from by omega])
            (Nat.find_min hex (m := p - a) (by omega))
      have hk := pos_sub_eq_of_dirConst hn i a (Nat.find hex) hconst
      rw [hL, Dir.sign_left] at hk
      linarith
  · -- already heading right: nothing to wait for
    exact ⟨a, le_rfl, hR, by intro p hp1 hp2; omega, by ring⟩

/-- **The first moment a drone heads left**, likewise. -/
theorem exists_firstLeft {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (i : Fin n) (a : ℕ) :
    ∃ b, a ≤ b ∧ (c.run hn b).dir i = Dir.left ∧
      (∀ p, a ≤ p → p < b → (c.run hn p).dir i = Dir.right) ∧
      (c.run hn b).time - (c.run hn a).time
        = (c.run hn b).pos i - (c.run hn a).pos i := by
  classical
  rcases Dir.eq_left_or_right ((c.run hn a).dir i) with hL | hR
  · exact ⟨a, le_rfl, hL, by intro p hp1 hp2; omega, by ring⟩
  · have hex : ∃ m : ℕ, (c.run hn (a + m)).dir i = Dir.left := by
      obtain ⟨q, hq, hd⟩ := exists_dir_left_of_dir_right hn hi hR
      exact ⟨q - a, by rwa [show a + (q - a) = q from by omega]⟩
    refine ⟨a + Nat.find hex, by omega, Nat.find_spec hex, ?_, ?_⟩
    · intro p hp1 hp2
      rcases Dir.eq_left_or_right ((c.run hn p).dir i) with hx | hx
      · exact absurd (by rwa [show a + (p - a) = p from by omega])
          (Nat.find_min hex (m := p - a) (by omega))
      · exact hx
    · have hconst : ∀ p, a ≤ p → p < a + Nat.find hex →
          (c.run hn p).dir i = (c.run hn a).dir i := by
        intro p hp1 hp2
        rw [hR]
        rcases Dir.eq_left_or_right ((c.run hn p).dir i) with hx | hx
        · exact absurd (by rwa [show a + (p - a) = p from by omega])
            (Nat.find_min hex (m := p - a) (by omega))
        · exact hx
      have hk := pos_sub_eq_of_dirConst hn i a (Nat.find hex) hconst
      rw [hR, Dir.sign_right, one_mul] at hk
      linarith

end Config

end DPSS


