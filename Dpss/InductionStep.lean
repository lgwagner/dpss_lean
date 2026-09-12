/-
# DPSS — Lemma 3.7, the `+1/n` inductive step

**B5**, and the last lemma before the assembly of Theorem 2.1.

> **Lemma 3.7.** Suppose `j < n` and at time `t` drones `1, …, j` are left
> synchronized and drones `j` and `j+1` have met. Then at time `t + 1/n`,
> drone `j+1` is left synchronized as well.

The paper's proof is a trichotomy on what drone `j` is doing *at the instant
`t`*, and each branch is discharged by a lemma already proved here:

* `j` heading **right** — within `1/n` it is at or beyond its right endpoint,
  which is the boundary it shares with `j+1`; ordering then carries `j+1` past
  its own left endpoint. (Lemma 3.4.)
* `j` heading **left** — then look back to the last moment the pair was
  together. Lemma 3.6 says `j` has been heading left ever since, so it was at
  least as far right then as it is now, hence already left synchronized there;
  and at that moment the pair was either escorting leftward (Lemma 3.3) or
  separating (Lemma 3.2).

## The two cases merge more than the paper's do

The paper splits the leftward case by whether the pair is *currently* together.
Here both halves are the same argument: take the **last index at or before `t`
at which the pair was co-located** — which exists precisely because they have
met — and run Lemmas 3.6, 3.3 and 3.2 from there. When they are together now,
that index is the current one and Lemma 3.6 has an empty range to cover.

## Why a pair co-located and heading apart is on its boundary

Both leftward branches end at a co-located pair whose left drone heads left. If
the right drone heads left too they are escorting; if it heads **right** they
are separating, and Lemma 3.2 applies — but only once we know they are on the
boundary they share. That is `ApartOnBoundary`, which §3.20 shows is *false*
pointwise and `Reachable.lean` proves is preserved by a step. So it enters here
as a hypothesis on the **starting** configuration, propagated along the run.
It is a mild condition: any configuration with no two adjacent drones on the
same point satisfies it, as does any configuration in which all drones head the
same way.

## Reference

Avigad–van Doorn, arXiv:2008.04262, `lemma:induction:step`.
-/

import Dpss.RealTime

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## The greatest index below a bound satisfying a predicate -/

/-- If a predicate holds somewhere at or below `k`, it holds at a **greatest**
such place. Used to name the pair's last meeting before a given instant. -/
theorem exists_greatest_le {P : ℕ → Prop} {m : ℕ} :
    ∀ {k : ℕ}, m ≤ k → P m → ∃ b, b ≤ k ∧ P b ∧ ∀ p, b < p → p ≤ k → ¬ P p := by
  classical
  intro k
  induction k with
  | zero =>
    intro hmk hm
    exact ⟨m, hmk, hm, fun p _ hp2 => absurd hp2 (by omega)⟩
  | succ k ih =>
    intro hmk hm
    by_cases hk : P (k + 1)
    · exact ⟨k + 1, le_rfl, hk, fun p hp1 hp2 => absurd hp2 (by omega)⟩
    · have hmk' : m ≤ k := by
        by_contra hcon
        have hme : m = k + 1 := by omega
        exact hk (hme ▸ hm)
      obtain ⟨b, hb1, hb2, hb3⟩ := ih hmk' hm
      refine ⟨b, by omega, hb2, ?_⟩
      intro p hp1 hp2
      rcases Nat.lt_or_ge p (k + 1) with hlt | hge
      · exact hb3 p hp1 (by omega)
      · have hpe : p = k + 1 := by omega
        rw [hpe]; exact hk

/-! ## `ApartOnBoundary` along a run -/

/-- Every pair of a configuration satisfies `ApartOnBoundary`: a co-located
pair heading apart sits on the boundary it shares. -/
def ApartOnBoundaries (c : Config n) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), c.ApartOnBoundary i h

/-- **It is preserved along a run** — `Reachable.lean` proved the step. -/
theorem apartOnBoundaries_run {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) (k : ℕ) : (c.run hn k).ApartOnBoundaries := by
  induction k with
  | zero => exact hab
  | succ k ih => exact fun i h => apartOnBoundary_step hn (invariant_run hn hi k) ih i h

/-- A configuration with no two adjacent drones on the same point satisfies it
vacuously. -/
theorem apartOnBoundaries_of_not_coLocated {c : Config n}
    (hnc : ∀ (i : Fin n) (h : i.val + 1 < n), ¬ c.CoLocated i h) :
    c.ApartOnBoundaries := fun i h hco _ _ => absurd hco (hnc i h)

/-- So does one in which every drone heads the same way — no pair heads apart
at all. -/
theorem apartOnBoundaries_of_dir_const {c : Config n} {d : Dir}
    (hd : ∀ i : Fin n, c.dir i = d) : c.ApartOnBoundaries := by
  intro i h _ hL hR
  rw [hd i] at hL
  rw [hd (nextIdx i h)] at hR
  rw [hL] at hR
  exact Dir.noConfusion hR

/-! ## The pivot: a meeting hands left synchronization on

Both branches of Lemma 3.7 end at the same configuration — the pair co-located
with the left drone heading left — and this is what that configuration gives.
It is Lemma 3.3 or Lemma 3.2 according to what the right drone is doing. -/

/-- **A co-located pair whose left drone heads left passes left synchronization
to the right drone.** -/
theorem leftSync_next_of_coLocated_left {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) (hab : c.ApartOnBoundaries) {i : Fin n}
    {h : i.val + 1 < n} {m : ℕ}
    (hco : (c.run hn m).CoLocated i h)
    (hdL : (c.run hn m).dir i = Dir.left)
    (hsync : LeftSync c hn i m) : LeftSync c hn (nextIdx i h) m := by
  rcases Dir.eq_left_or_right ((c.run hn m).dir (nextIdx i h)) with hd | hd
  · -- escorting leftward: Lemma 3.3
    exact leftSync_of_escorting hn hi ⟨hco, by rw [hdL, hd]⟩ hdL hsync
  · -- heading apart, hence on their shared boundary: Lemma 3.2
    have hpos : (c.run hn m).pos i = commonEnd i :=
      apartOnBoundaries_run hn hi hab m i h hco hdL hd
    exact leftSync_of_separation hn hi ⟨hco, hpos⟩ hsync

/-! ## Lemma 3.7 -/

/-- **Lemma 3.7.** If drone `i` is left synchronized from time `T` and the pair
`(i, i+1)` has met by then, drone `i+1` is left synchronized from `T + 1/n`. -/
theorem leftSyncAt_next {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) {i : Fin n} {h : i.val + 1 < n} {T : ℝ}
    (hT : c.time ≤ T) (hsync : LeftSyncAt c hn i T)
    (hmet : HaveMetBy c hn i h T) :
    LeftSyncAt c hn (nextIdx i h) (T + 1 / (n : ℝ)) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hninv : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  obtain ⟨j0, hj0le, hj0lt⟩ := exists_lastBefore hn hi hT
  have hinT : c.InStep hn j0 T := ⟨hj0le, le_of_lt hj0lt⟩
  have hxT : leftEnd i ≤ c.posIn hn j0 i T := hsync j0 T le_rfl hinT
  rcases Dir.eq_left_or_right ((c.run hn j0).dir i) with hdL | hdR
  · -- ## drone `i` is heading left at `T`
    -- it was at least as far right at the opening event of the step
    have hpos_j0 : leftEnd i ≤ (c.run hn j0).pos i := by
      have hle : c.posIn hn j0 i T ≤ (c.run hn j0).pos i := by
        unfold posIn; rw [hdL, Dir.sign_left]; linarith
      linarith
    have hLSj0 : LeftSync c hn i j0 := by
      intro p hp
      rcases eq_or_lt_of_le hp with rfl | hlt
      · exact hpos_j0
      · have hTp : T ≤ (c.run hn p).time :=
          le_of_lt (lt_of_lt_of_le hj0lt (time_mono_run' hn hi (by omega)))
        exact leftSync_of_leftSyncAt hn hi hsync hTp p le_rfl
    -- the pair met at some index at or before `j0`
    obtain ⟨m, hmT, hmco⟩ := hmet
    have hmj0 : m ≤ j0 := by
      by_contra hlt
      have hge : (c.run hn (j0 + 1)).time ≤ (c.run hn m).time :=
        time_mono_run' hn hi (by omega)
      linarith
    -- take the last such index
    obtain ⟨ms, hmsle, hmsco, hgreat⟩ :=
      exists_greatest_le (P := fun k => (c.run hn k).CoLocated i h) hmj0 hmco
    -- Lemma 3.6: drone `i` has been heading left ever since
    have hdirs : ∀ p, ms ≤ p → p ≤ j0 → (c.run hn p).dir i = Dir.left :=
      dir_left_since_of_never_coLocated hn hi hmsle hgreat hdL
    -- heading left, it only ever got closer to its left endpoint, so it was
    -- already left synchronized at `ms`
    have hLSms : LeftSync c hn i ms := by
      intro p hp
      rcases le_or_gt j0 p with hj | hj
      · exact hLSj0 p hj
      · have hconst : ∀ q, p ≤ q → q < p + (j0 - p) →
            (c.run hn q).dir i = (c.run hn p).dir i := by
          intro q hq1 hq2
          rw [hdirs q (by omega) (by omega), hdirs p hp (by omega)]
        have hkey := pos_sub_eq_of_dirConst hn i p (j0 - p) hconst
        rw [show p + (j0 - p) = j0 from by omega, hdirs p hp (by omega),
          Dir.sign_left] at hkey
        have ht : (c.run hn p).time ≤ (c.run hn j0).time :=
          time_mono_run' hn hi (by omega)
        have hj0pos := hLSj0 j0 le_rfl
        linarith
    have hfinal : LeftSync c hn (nextIdx i h) ms :=
      leftSync_next_of_coLocated_left hn hi hab hmsco (hdirs ms le_rfl hmsle) hLSms
    refine leftSyncAt_mono ?_ (leftSyncAt_of_leftSync hn hi hfinal)
    have hms : (c.run hn ms).time ≤ (c.run hn j0).time := time_mono_run' hn hi hmsle
    linarith
  · -- ## drone `i` is heading right at `T`
    obtain ⟨b, hb0, hbL, hbR, -⟩ := exists_firstLeft hn hi i j0
    have hbj0 : j0 < b := by
      rcases eq_or_lt_of_le hb0 with rfl | hlt
      · rw [hdR] at hbL; exact Dir.noConfusion hbL
      · exact hlt
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    -- the drone's position tracks elapsed time until it turns
    have hposp : ∀ p, j0 ≤ p → p ≤ b' + 1 →
        (c.run hn p).pos i
          = (c.run hn j0).pos i + ((c.run hn p).time - (c.run hn j0).time) := by
      intro p hp1 hp2
      have hconst : ∀ q, j0 ≤ q → q < j0 + (p - j0) →
          (c.run hn q).dir i = (c.run hn j0).dir i := by
        intro q hq1 hq2
        rw [hbR q hq1 (by omega), hdR]
      have hkey := pos_sub_eq_of_dirConst hn i j0 (p - j0) hconst
      rw [show j0 + (p - j0) = p from by omega, hdR, Dir.sign_right,
        one_mul] at hkey
      linarith
    have hxT' : c.posIn hn j0 i T
        = (c.run hn j0).pos i + (T - (c.run hn j0).time) := by
      unfold posIn; rw [hdR, Dir.sign_right]; ring
    rw [hxT'] at hxT
    -- at the turn, the pair is co-located and Lemma 3.3 or 3.2 applies
    have hturn : TurnsLeftAt c hn i b' := ⟨hbR b' (by omega) (by omega), hbL⟩
    have hinvb := invariant_run hn hi (b' + 1)
    have hcob : (c.run hn (b' + 1)).CoLocated i h :=
      coLocated_of_turnsLeft (c := (c.run hn b').advance
          ((c.run hn b').timeToNextEvent hn))
        hinvb.onPerimeter (ordered_of_adjOrdered hinvb.adjOrdered) h
        ⟨hturn.1, hturn.2⟩
    have hLSb : LeftSync c hn i (b' + 1) := by
      refine leftSync_of_leftSyncAt hn hi hsync ?_
      have := time_mono_run' hn hi (show j0 + 1 ≤ b' + 1 by omega)
      linarith
    have hfinal : LeftSync c hn (nextIdx i h) (b' + 1) :=
      leftSync_next_of_coLocated_left hn hi hab hcob hbL hLSb
    -- assemble
    intro p s hsT hin
    rcases le_or_gt (b' + 1) p with hpb | hpb
    · exact le_posIn hn hin (hfinal p hpb) (hfinal (p + 1) (by omega))
    · -- before the turn: drone `i` is already past the shared boundary
      have hpj0 : j0 ≤ p := by
        by_contra hlt
        have h1 : (c.run hn (p + 1)).time ≤ (c.run hn j0).time :=
          time_mono_run' hn hi (by omega)
        linarith [hin.2]
      have hpospi : c.posIn hn p i s
          = (c.run hn j0).pos i + (s - (c.run hn j0).time) := by
        unfold posIn
        rw [hbR p hpj0 (by omega), Dir.sign_right, one_mul,
          hposp p hpj0 (by omega)]
        ring
      have hge : commonEnd i ≤ c.posIn hn p i s := by
        rw [hpospi]
        have hle := leftEnd_eq i
        linarith
      have hord := posIn_le_posIn_next hn hi (i := i) (h := h) hin
      rw [leftEnd_next_eq_commonEnd i h]
      linarith

end Config

end DPSS
