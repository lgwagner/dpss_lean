/-
# DPSS — the phase invariant of a pair (B1)

The last obstruction to **Lemma 3.2**, and through it to 3.3 and 3.4.

`STATUS.md` §8a derives the invariant; this file states and proves it. Three
clauses:

1. `0 ≤ balance` — what `leftSync_of_balanceNonneg` consumes;
2. heading `(left, right)` ⟹ `balance = 0` — the engine;
3. `BothLeftApart` ⟹ the left drone sits on its left endpoint — the only
   configuration that can drive the balance down.

Clause 2 works because the balance rate is the **sum** of the two headings
(unlike the gap, which uses the difference): a pair heading apart holds its
balance *constant* while its gap grows at rate 2. So it is enough that the pair
can only ever *enter* that state with the balance at zero.

## Why a pair that is apart cannot change phase

The pleasant part. If the two drones are **not** co-located, then every event
that could deliver `left` to one and `right` to the other is impossible:
`SepRight`, `MeetRight`, `SepLeft` on the right drone and `MeetLeft` on it all
require *this* pair to be co-located, and either border event forces
co-location by ordering. So the pair was already heading apart, and the balance
carries over untouched.
-/

import Dpss.Mirror

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## A pair that is apart cannot have just changed phase -/

theorem le_nextIdx (i : Fin n) (h : i.val + 1 < n) : i ≤ nextIdx i h := by
  rw [Fin.le_def, nextIdx_val]; omega

/-- With the pair apart, only an unchanged heading or a meet with the *other*
neighbour can leave the left drone heading left. -/
theorem dir_left_of_apart {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hp : c.OnPerimeter) (ho : c.Ordered) (hnc : ¬ c.CoLocated i h)
    (hL : c.newDir i = Dir.left) : c.dir i = Dir.left := by
  rcases newDir_left_cases hL with hb | hs | ⟨hm, -⟩ | ⟨hm, -⟩ | hd
  · exfalso
    refine hnc ?_
    unfold CoLocated gap
    rw [pos_eq_one_of_ge ho hp (le_nextIdx i h) hb.1, hb.1]
    ring
  · exact absurd hs.2.1 hnc
  · exact absurd hm.2.1 hnc
  · obtain ⟨_hz, -, hA⟩ := hm
    have hx := hA.2
    rwa [nextIdx_prevIdx] at hx
  · exact hd

/-- Symmetrically for the right drone. -/
theorem dir_right_of_apart {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hp : c.OnPerimeter) (ho : c.Ordered) (hnc : ¬ c.CoLocated i h)
    (hR : c.newDir (nextIdx i h) = Dir.right) :
    c.dir (nextIdx i h) = Dir.right := by
  rcases newDir_right_cases hR with hb | hs | ⟨hm, -⟩ | ⟨hm, -⟩ | hd
  · exfalso
    refine hnc ?_
    unfold CoLocated gap
    rw [hb.1, pos_eq_zero_of_le ho hp (le_nextIdx i h) hb.1]
    ring
  · exfalso
    obtain ⟨hz, hco2, -⟩ := hs
    exact hnc ((coLocated_congr c _ h (prevIdx_nextIdx i h hz)).mp hco2)
  · exact hm.2.2.1
  · exfalso
    obtain ⟨hz, hco2, -⟩ := hm
    exact hnc ((coLocated_congr c _ h (prevIdx_nextIdx i h hz)).mp hco2)
  · exact hd

/-! ## The invariant -/

/-- The phase invariant of a pair. See `STATUS.md` §8a for the derivation. -/
structure PairPhase (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop where
  /-- What Lemma 3.2 ultimately consumes. -/
  balance_nonneg : 0 ≤ c.pairBalance i h
  /-- The engine: a pair heading apart has settled its balance at zero. -/
  apart_zero : c.dir i = Dir.left → c.dir (nextIdx i h) = Dir.right →
    c.pairBalance i h = 0
  /-- The only configuration that can drive the balance down, pinned. -/
  bothLeft_pinned : c.BothLeftApart i h → c.pos i = leftEnd i

/-! ## Preservation, clause by clause

Throughout, `hle` is what left synchronization of the left drone supplies: it
does not end the step to the left of its own left endpoint. -/

/-- **Clause 2.** A pair can only enter the heading-apart phase with its
balance at zero. -/
theorem apart_zero_step {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} (hph : c.PairPhase i h)
    (hL : (c.step hn).dir i = Dir.left)
    (hR : (c.step hn).dir (nextIdx i h) = Dir.right) :
    (c.step hn).pairBalance i h = 0 := by
  set dt := c.timeToNextEvent hn with hdtdef
  have hpa : (c.advance dt).OnPerimeter :=
    onPerimeter_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent
  have hoa : (c.advance dt).Ordered :=
    ordered_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent
  by_cases hco : (c.advance dt).CoLocated i h
  · -- co-located: either a separation fired, or the pair already headed apart
    by_cases hsr : (c.advance dt).SepRight i
    · have hpos : (c.advance dt).pos i = commonEnd i :=
        pos_eq_commonEnd_of_sepRight hsr
      have hsame : (c.advance dt).pos (nextIdx i h) = (c.advance dt).pos i := by
        unfold CoLocated gap at hco; linarith
      show (c.advance dt).pairBalance i h = 0
      unfold pairBalance
      rw [hsame, hpos]; ring
    by_cases hsl : (c.advance dt).SepLeft (nextIdx i h)
    · have hpos : (c.advance dt).pos i = commonEnd i :=
        pos_eq_commonEnd_of_sepLeft_next hsl
      have hsame : (c.advance dt).pos (nextIdx i h) = (c.advance dt).pos i := by
        unfold CoLocated gap at hco; linarith
      show (c.advance dt).pairBalance i h = 0
      unfold pairBalance
      rw [hsame, hpos]; ring
    · have hdi : (c.advance dt).dir i = Dir.left :=
        dir_left_of_newDir_apart hco hL hR hsr hsl hpa
      have hdj : (c.advance dt).dir (nextIdx i h) = Dir.right :=
        dir_right_of_newDir_apart hco hL hR hsl hdi
      have hdi' : c.dir i = Dir.left := hdi
      have hdj' : c.dir (nextIdx i h) = Dir.right := hdj
      show (c.advance dt).pairBalance i h = 0
      rw [pairBalance_advance, hdi', hdj', Dir.sign_left, Dir.sign_right,
        hph.apart_zero hdi' hdj']
      ring
  · -- apart: the pair cannot have changed phase at all
    have hdi : (c.advance dt).dir i = Dir.left :=
      dir_left_of_apart hpa hoa hco hL
    have hdj : (c.advance dt).dir (nextIdx i h) = Dir.right :=
      dir_right_of_apart hpa hoa hco hR
    have hdi' : c.dir i = Dir.left := hdi
    have hdj' : c.dir (nextIdx i h) = Dir.right := hdj
    show (c.advance dt).pairBalance i h = 0
    rw [pairBalance_advance, hdi', hdj', Dir.sign_left, Dir.sign_right,
      hph.apart_zero hdi' hdj']
    ring

/-- **A pinned drone freezes the clock.** If the left drone sits on its own left
endpoint heading left, any positive step would carry it past — so left
synchronization forces the step to have no length at all. -/
theorem dt_eq_zero_of_pinned {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} (hpos : c.pos i = leftEnd i) (hdir : c.dir i = Dir.left)
    (hle : leftEnd i ≤ (c.step hn).pos i) : c.timeToNextEvent hn = 0 := by
  have hdt : 0 ≤ c.timeToNextEvent hn :=
    timeToNextEvent_nonneg hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent
  have hx : (c.step hn).pos i
      = c.pos i + (c.dir i).sign * c.timeToNextEvent hn := rfl
  rw [hpos, hdir, Dir.sign_left] at hx
  rw [hx] at hle
  linarith

/-- **Clause 3.** The one configuration that can drive the balance down leaves
the left drone pinned to its own left endpoint. -/
theorem bothLeft_pinned_step {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} (hph : c.PairPhase i h)
    (hle : leftEnd i ≤ (c.step hn).pos i)
    (hbl : (c.step hn).BothLeftApart i h) : (c.step hn).pos i = leftEnd i := by
  obtain ⟨hL, hL2, hnc⟩ := hbl
  set dt := c.timeToNextEvent hn with hdtdef
  have hpa : (c.advance dt).OnPerimeter :=
    onPerimeter_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent
  have hoa : (c.advance dt).Ordered :=
    ordered_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent
  have hnc' : ¬ (c.advance dt).CoLocated i h := hnc
  rcases Dir.eq_left_or_right ((c.advance dt).dir i) with hdi | hdi
  · rcases Dir.eq_left_or_right ((c.advance dt).dir (nextIdx i h)) with hdj | hdj
    · -- both were already heading left, so the pair was pinned before the step
      have hdi' : c.dir i = Dir.left := hdi
      have hdj' : c.dir (nextIdx i h) = Dir.left := hdj
      have hgapc : ¬ c.CoLocated i h := by
        intro hx
        refine hnc' ?_
        unfold CoLocated at hx ⊢
        rw [gap_advance, hx]
        unfold sepRate
        rw [hdi', hdj']
        ring
      have hpin := hph.bothLeft_pinned ⟨hdi', hdj', hgapc⟩
      have hz := dt_eq_zero_of_pinned hn hi hpin hdi' hle
      have hx : (c.step hn).pos i = c.pos i + (c.dir i).sign * dt := rfl
      rw [hx, hpin, hdtdef, hz]; ring
    · -- the right drone reversed: the pair was heading apart, so the balance
      -- was zero, and the positional core pins both
      have hdi' : c.dir i = Dir.left := hdi
      have hdj' : c.dir (nextIdx i h) = Dir.right := hdj
      have hbal : (c.advance dt).pairBalance i h = 0 := by
        rw [pairBalance_advance, hdi', hdj', Dir.sign_left, Dir.sign_right,
          hph.apart_zero hdi' hdj']
        ring
      have hturn : rightEnd (nextIdx i h) ≤ (c.advance dt).pos (nextIdx i h) :=
        rightEnd_le_pos_of_turnsLeft ⟨hdj, hL2⟩
      exact (pinned_of_balance_zero hbal hle hturn).2
  · -- the left drone reversed to leftward, so it is co-located after all
    exact absurd (coLocated_of_turnsLeft hpa hoa h ⟨hdi, hL⟩) hnc'

/-- **Clause 1.** The balance never goes negative. -/
theorem balance_nonneg_step {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} (hph : c.PairPhase i h)
    (hle : leftEnd i ≤ (c.step hn).pos i) :
    0 ≤ (c.step hn).pairBalance i h := by
  by_cases hbl : c.BothLeftApart i h
  · -- pinned before the step, so the clock did not move and neither did the
    -- balance
    have hz := dt_eq_zero_of_pinned hn hi (hph.bothLeft_pinned hbl) hbl.1 hle
    rw [pairBalance_step_of_time_zero hn hz]
    exact hph.balance_nonneg
  · exact pairBalance_nonneg_step hn hi hph.balance_nonneg hbl

/-- **The phase invariant is preserved by a step.** -/
theorem pairPhase_step {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} (hph : c.PairPhase i h)
    (hle : leftEnd i ≤ (c.step hn).pos i) : (c.step hn).PairPhase i h where
  balance_nonneg := balance_nonneg_step hn hi hph hle
  apart_zero := fun hL hR => apart_zero_step hn hi hph hL hR
  bothLeft_pinned := bothLeft_pinned_step hn hi hph hle

/-! ## Along a run -/

/-- **The phase invariant holds for ever**, given that the left drone is left
synchronized — which is exactly Lemma 3.2's hypothesis. -/
theorem pairPhase_run {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (hph : (c.run hn k).PairPhase i h) (hsync : LeftSync c hn i k) :
    ∀ m, (c.run hn (k + m)).PairPhase i h := by
  intro m
  induction m with
  | zero => exact hph
  | succ m ih =>
    have hstep : c.run hn (k + (m + 1)) = (c.run hn (k + m)).step hn := rfl
    rw [hstep]
    exact pairPhase_step hn (invariant_run hn hi (k + m)) ih
      (hsync (k + m + 1) (by omega))

/-- **`BalanceNonneg`, and with it Lemma 3.2.** -/
theorem balanceNonneg_of_pairPhase {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (hph : (c.run hn k).PairPhase i h) (hsync : LeftSync c hn i k) :
    BalanceNonneg c hn i h k := by
  intro j hj
  obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
  exact (pairPhase_run hn hi hph hsync m).balance_nonneg

/-! ## Lemmas 3.2 and 3.3, unconditional

Two starting configurations supply the phase invariant outright, so the lemmas
that begin there need nothing beyond left synchronization of the left drone —
which is their own hypothesis. -/

/-- A pair that has just separated satisfies the invariant: the balance is zero,
so the second clause is immediate, and the pair is co-located, so the third is
vacuous. -/
theorem pairPhase_of_atSeparation {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hs : c.AtSeparation i h) : c.PairPhase i h where
  balance_nonneg := le_of_eq (pairBalance_eq_zero_of_atSeparation hs).symm
  apart_zero := fun _ _ => pairBalance_eq_zero_of_atSeparation hs
  bothLeft_pinned := fun hbl => absurd hs.1 hbl.2.2

/-- An escorting pair heading left satisfies it too: the scheduler supplies the
balance, and both remaining clauses are vacuous — a pair heading the same way
is not heading apart, and a co-located pair is not apart. -/
theorem pairPhase_of_escorting_left {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hec : c.EscortsCoherent) (he : c.Escorting i h)
    (hL : c.dir i = Dir.left) : c.PairPhase i h where
  balance_nonneg := pairBalance_nonneg_of_escorting_left hec he hL
  apart_zero := fun _ hR => by
    have hx := he.2
    rw [hL, hR] at hx
    exact absurd hx (fun hc => Dir.noConfusion hc)
  bothLeft_pinned := fun hbl => absurd he.1 hbl.2.2

/-- **Lemma 3.2, unconditional.** If drone `i` is left synchronized and the
pair separates at their shared boundary, then `i+1` is left synchronized. -/
theorem leftSync_of_separation {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (hs : (c.run hn k).AtSeparation i h) (hsync : LeftSync c hn i k) :
    LeftSync c hn (nextIdx i h) k :=
  leftSync_of_balanceNonneg hn hi
    (balanceNonneg_of_pairPhase hn hi (pairPhase_of_atSeparation hs) hsync)

/-- **Lemma 3.3, unconditional.** A pair escorting leftward, with the left
drone left synchronized, has its right drone left synchronized too. -/
theorem leftSync_of_escorting {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (he : (c.run hn k).Escorting i h)
    (hL : (c.run hn k).dir i = Dir.left) (hsync : LeftSync c hn i k) :
    LeftSync c hn (nextIdx i h) k :=
  leftSync_of_balanceNonneg hn hi
    (balanceNonneg_of_pairPhase hn hi
      (pairPhase_of_escorting_left (invariant_run hn hi k).escortsCoherent he hL)
      hsync)

/-- **Lemma 3.4**, in the strongest form the invariant supports. Its own
hypothesis — the left drone having reached the shared boundary — gives a
nonnegative balance but *not* the second clause, since a pair heading apart
from there may have a strictly positive balance. So it takes the phase
invariant as a hypothesis, which a caller inside a run can supply because
`pairPhase_run` proves it is preserved. -/
theorem leftSync_of_reached_boundary {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (hph : (c.run hn k).PairPhase i h) (hsync : LeftSync c hn i k) :
    LeftSync c hn (nextIdx i h) k :=
  leftSync_of_balanceNonneg hn hi (balanceNonneg_of_pairPhase hn hi hph hsync)

end Config

end DPSS


