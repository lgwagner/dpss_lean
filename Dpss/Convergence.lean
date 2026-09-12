/-
# DPSS — Theorem 2.1, assembled

**B6.** Everything is in place; this file puts it together.

> **Theorem 2.1.** Assuming all the drones have the correct estimates, they are
> all synchronized at time `2 − 1/n`.

The argument the paper gives in three lines:

> Since drone 1 is always left synchronized and all the drones have met by time
> 1, by induction on `i < n` we have that drones `1, …, i` are left
> synchronized at time `1 + (i−1)/n`. Taking `i = n` yields the theorem.

and here those three lines are, with the pieces named:

* **Base.** Drone `0`'s left endpoint is the left border of the perimeter,
  which `onPerimeter_run` says nobody crosses — `leftSyncAt_zero`.
* **Meeting.** Every adjacent pair is co-located within one unit of time —
  `haveMetBy_one`, which is Lemma 3.5 (**B3**).
* **Step.** Each drone hands left synchronization to its right-hand neighbour
  at a cost of `1/n` — `leftSyncAt_next`, which is Lemma 3.7 (**B5**).
* **The other half.** Right synchronization is left synchronization of the
  reflected run — `rightSyncAt_iff_leftSyncAt_mirror`, built on **B7**.

The bound comes out **exactly** `2 − 1/n`: drone `i` is left synchronized at
`1 + i/n` in this development's 0-based indexing, and `i = n − 1` gives
`1 + (n−1)/n = 2 − 1/n`. Not an ε is lost anywhere, which matters because the
paper exhibits a configuration attaining the bound.

## The one hypothesis beyond the standing invariant

`ApartOnBoundaries` — a co-located pair heading apart sits on the boundary it
shares. §3.20 shows this is *false* as a pointwise fact, and `Reachable.lean`
proves it is preserved by a step, so it is a condition on the **starting**
configuration and nothing more. `apartOnBoundaries_of_not_coLocated` and
`apartOnBoundaries_of_dir_const` discharge it for the configurations anyone
would actually start from.

## Reference

Avigad–van Doorn, arXiv:2008.04262, Theorem 2.1.
-/

import Dpss.InductionStep

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## The reflected world, in real time

`Mirror.lean` transferred the step-indexed notions. These transfer the
real-time ones, which is all that is needed to get the right half for free. -/

/-- A reflected drone's position at an instant is the reflection of the
original's. -/
theorem posIn_mirror (c : Config n) (hn : 0 < n) (p : ℕ) (i : Fin n) (s : ℝ) :
    c.mirror.posIn hn p (mirrorIdx i) s = 1 - c.posIn hn p i s := by
  unfold posIn
  rw [run_mirror]
  simp only [mirror_pos, mirror_dir, mirror_time, mirrorIdx_mirrorIdx,
    Dir.sign_flip]
  ring

/-- Reflection does not touch the clock, so the steps are the same steps. -/
theorem inStep_mirror (c : Config n) (hn : 0 < n) (p : ℕ) (s : ℝ) :
    c.mirror.InStep hn p s ↔ c.InStep hn p s := by
  unfold InStep
  rw [run_mirror, run_mirror]
  simp only [mirror_time]

/-- **The real-time transfer principle.** Right synchronization here *is* left
synchronization there. -/
theorem rightSyncAt_iff_leftSyncAt_mirror (c : Config n) (hn : 0 < n)
    (i : Fin n) (T : ℝ) :
    RightSyncAt c hn i T ↔ LeftSyncAt c.mirror hn (mirrorIdx i) T := by
  constructor
  · intro hs p s hsT hin
    have hin' : c.InStep hn p s := (inStep_mirror c hn p s).mp hin
    rw [posIn_mirror, leftEnd_mirrorIdx]
    have := hs p s hsT hin'
    linarith
  · intro hs p s hsT hin
    have hin' : c.mirror.InStep hn p s := (inStep_mirror c hn p s).mpr hin
    have hx := hs p s hsT hin'
    rw [posIn_mirror, leftEnd_mirrorIdx] at hx
    linarith

/-- **And the extra hypothesis reflects too.** "A co-located pair heading apart
sits on the boundary it shares" is a statement invariant under reading the
perimeter backwards — as it must be, though in Lean that is a proof rather than
an observation. -/
theorem apartOnBoundaries_mirror {c : Config n} (hab : c.ApartOnBoundaries) :
    c.mirror.ApartOnBoundaries := by
  intro i h hco hL hR
  have hjlt : (mirrorIdx (nextIdx i h)).val + 1 < n := mirror_next_lt i h
  have hnext : nextIdx (mirrorIdx (nextIdx i h)) hjlt = mirrorIdx i :=
    nextIdx_mirrorIdx_next i h
  have hco' : c.CoLocated (mirrorIdx (nextIdx i h)) hjlt :=
    (coLocated_mirror c i h).mp hco
  have hdj : c.dir (mirrorIdx (nextIdx i h)) = Dir.left := by
    have hx : (c.dir (mirrorIdx (nextIdx i h))).flip = Dir.right := hR
    exact (flip_eq_right_iff _).mp hx
  have hdnext : c.dir (nextIdx (mirrorIdx (nextIdx i h)) hjlt) = Dir.right := by
    rw [hnext]
    have hx : (c.dir (mirrorIdx i)).flip = Dir.left := hL
    exact (flip_eq_left_iff _).mp hx
  have hpos := hab (mirrorIdx (nextIdx i h)) hjlt hco' hdj hdnext
  have hsame : c.pos (mirrorIdx i) = c.pos (mirrorIdx (nextIdx i h)) := by
    have hg : c.gap (mirrorIdx (nextIdx i h)) hjlt = 0 := hco'
    unfold gap at hg
    rw [hnext] at hg
    linarith
  have hgoal : c.mirror.pos i = 1 - c.pos (mirrorIdx i) := rfl
  rw [hgoal, hsame, hpos]
  have h1 : commonEnd (mirrorIdx (nextIdx i h)) = 1 - leftEnd (nextIdx i h) := by
    unfold commonEnd; exact rightEnd_mirrorIdx _
  have h2 : leftEnd (nextIdx i h) = commonEnd i := leftEnd_next_eq_commonEnd i h
  rw [h1, h2]; ring

/-! ## The induction

Drone `i` is left synchronized at time `1 + i/n`. The paper's `1 + (i−1)/n`,
shifted by the 0-based indexing. -/

/-- **Drones are left synchronized in turn, `1/n` apart.** -/
theorem leftSyncAt_index {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) :
    ∀ (k : ℕ) (i : Fin n), i.val = k →
      LeftSyncAt c hn i (c.time + 1 + (k : ℝ) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  intro k
  induction k with
  | zero =>
    intro i hval
    have hi0 : i = (⟨0, hn⟩ : Fin n) := Fin.ext hval
    rw [hi0]
    exact leftSyncAt_zero hn hi _
  | succ k ih =>
    intro i hval
    have hkn : k + 1 < n := by rw [← hval]; exact i.isLt
    have hk' : k < n := by omega
    have hprevlt : (⟨k, hk'⟩ : Fin n).val + 1 < n := hkn
    have hnexteq : nextIdx (⟨k, hk'⟩ : Fin n) hprevlt = i :=
      Fin.ext (by simp only [nextIdx_val]; omega)
    have hknn : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
    have hT : c.time ≤ c.time + 1 + (k : ℝ) / (n : ℝ) := by linarith
    have hmet : HaveMetBy c hn (⟨k, hk'⟩ : Fin n) hprevlt
        (c.time + 1 + (k : ℝ) / (n : ℝ)) :=
      haveMetBy_mono (by linarith) (haveMetBy_one hn hi _ _)
    have hres := leftSyncAt_next hn hi hab hT (ih ⟨k, hk'⟩ rfl) hmet
    rw [hnexteq] at hres
    refine leftSyncAt_mono (le_of_eq ?_) hres
    push_cast
    ring

/-! ## Theorem 2.1 -/

/-- **Every drone is left synchronized by `2 − 1/n`.** -/
theorem leftSyncAt_all {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) (i : Fin n) :
    LeftSyncAt c hn i (c.time + (2 - 1 / (n : ℝ))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine leftSyncAt_mono ?_ (leftSyncAt_index hn hi hab i.val i rfl)
  have hle : (i.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast i.isLt
  have hsum : ((i.val : ℝ) + 1) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hnR]; exact hle
  have heq : (i.val : ℝ) / (n : ℝ) + 1 / (n : ℝ) = ((i.val : ℝ) + 1) / (n : ℝ) := by
    ring
  linarith

/-- **And right synchronized by `2 − 1/n`**, by reflection. -/
theorem rightSyncAt_all {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) (i : Fin n) :
    RightSyncAt c hn i (c.time + (2 - 1 / (n : ℝ))) := by
  rw [rightSyncAt_iff_leftSyncAt_mirror]
  have hm := leftSyncAt_all (c := c.mirror) hn (invariant_mirror hn hi)
    (apartOnBoundaries_mirror hab) (mirrorIdx i)
  simpa using hm

/-- **Theorem 2.1, in real time.** Every drone is inside its own assigned
interval at *every instant* from `2 − 1/n` onwards — not merely at the events.

This is the form the paper states, and the form `LeftSyncAt` was introduced to
make expressible. -/
theorem sync_at_of_time {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) (i : Fin n) (p : ℕ) (s : ℝ)
    (hs : c.time + (2 - 1 / (n : ℝ)) ≤ s) (hin : c.InStep hn p s) :
    leftEnd i ≤ c.posIn hn p i s ∧ c.posIn hn p i s ≤ rightEnd i :=
  ⟨leftSyncAt_all hn hi hab i p s hs hin, rightSyncAt_all hn hi hab i p s hs hin⟩

/-- **Theorem 2.1**, discharging the statement `Synchronization.lean` recorded
as the goal of the whole development. -/
theorem convergesBy {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) : ConvergesBy c hn := by
  intro i j hj
  exact ⟨leftSync_of_leftSyncAt hn hi (leftSyncAt_all hn hi hab i) hj j le_rfl,
    rightSync_of_rightSyncAt hn hi (rightSyncAt_all hn hi hab i) hj j le_rfl⟩

/-- The same conclusion in the `AllSync` vocabulary: from any event at or after
`2 − 1/n`, the whole team is confined to its own segments for ever. -/
theorem allSync_of_time {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) {k : ℕ}
    (hk : c.time + (2 - 1 / (n : ℝ)) ≤ (c.run hn k).time) : AllSync c hn k :=
  fun i => ⟨leftSync_of_leftSyncAt hn hi (leftSyncAt_all hn hi hab i) hk,
    rightSync_of_rightSyncAt hn hi (rightSyncAt_all hn hi hab i) hk⟩

/-- **Theorem 2.1 for a start configuration with no two drones on the same
point** — the hypothesis `ApartOnBoundaries` discharged, leaving only the
standing invariant. -/
theorem convergesBy_of_distinct {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hd : ∀ (i : Fin n) (h : i.val + 1 < n), ¬ c.CoLocated i h) :
    ConvergesBy c hn :=
  convergesBy hn hi (apartOnBoundaries_of_not_coLocated hd)

/-- **And for a start configuration in which every drone heads the same way** —
the paper's own worst case, all `n` drones released together at the left
border. -/
theorem convergesBy_of_dir_const {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {d : Dir} (hd : ∀ i : Fin n, c.dir i = d) : ConvergesBy c hn :=
  convergesBy hn hi (apartOnBoundaries_of_dir_const hd)

end Config

/-! ## The theorem is not vacuous

Every hypothesis of `convergesBy` is met by configurations already traced in
this development, and the general theorem reproduces the conclusions those
traces established by hand. That is the check worth having: a general proof
that no concrete configuration satisfies would be true for the empty reason.
-/

namespace Examples

open Config

/-- Two drones converging from inside their intervals, the configuration
`Examples.lean` uses to show the standing invariant is satisfiable. Nothing is
co-located, so `ApartOnBoundaries` is vacuous. -/
theorem approach_apartOnBoundaries : approach.ApartOnBoundaries := by
  refine apartOnBoundaries_of_not_coLocated ?_
  intro i h hco
  rcases fin2_cases i with hi | hi <;> subst hi
  · have hg : approach.gap d0 h = 0 := hco
    unfold gap at hg
    norm_num [approach, nextIdx, d0] at hg
  · exact absurd h (by norm_num [d1])

/-- **Theorem 2.1 for `approach`, from the general theorem.** `Examples.lean`
proves the same statement by tracing the run; this derives it. -/
theorem approach_converges_general : ConvergesBy approach hn2 :=
  convergesBy hn2 approach_invariant approach_apartOnBoundaries

/-- The team released near the left border, both heading out — the shape of the
paper's own worst case. -/
theorem spread_invariant : spread.Invariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases fin2_cases i with hi | hi <;> subst hi
    · exact ⟨by norm_num [spread, d0], by norm_num [spread, d0]⟩
    · exact ⟨by norm_num [spread, d1], by norm_num [spread, d1]⟩
  · intro i h
    rcases fin2_cases i with hi | hi <;> subst hi
    · unfold gap; norm_num [spread, nextIdx, d0]
    · exact absurd h (by norm_num [d1])
  · intro i h he
    exfalso
    rcases fin2_cases i with hi | hi <;> subst hi
    · have hg : spread.gap d0 h = 0 := he.1
      unfold gap at hg
      norm_num [spread, nextIdx, d0] at hg
    · exact absurd h (by norm_num [d1])

/-- **Theorem 2.1 for `spread`, from the general theorem.** The traced run
settles at `5/4` against the bound `3/2`; the general theorem gives the bound
without the trace. -/
theorem spread_converges_general : ConvergesBy spread hn2 :=
  convergesBy_of_dir_const hn2 spread_invariant (fun _ => rfl)

end Examples

namespace ExamplesThree

open Config

/-- Three drones, the left pair **co-located and heading apart** — exactly the
configuration `ApartOnBoundaries` is about, and they are on the boundary they
share. So the hypothesis is not merely satisfiable by avoiding the case; it is
satisfiable while exercising it. -/
theorem cfgB_apartOnBoundaries : (cfgB 0).ApartOnBoundaries := by
  intro i h hco _ _
  rcases fin3_cases i with hi | hi | hi <;> subst hi
  · show (cfgB 0).pos e0 = commonEnd e0
    unfold commonEnd rightEnd
    norm_num [cfgB, e0]
  · exfalso
    have hg : (cfgB 0).gap e1 h = 0 := hco
    unfold gap at hg
    norm_num [cfgB, nextIdx, e1] at hg
  · exact absurd h (by norm_num [e2])

/-- **Theorem 2.1 for the three-drone configuration**, from the general
theorem. -/
theorem cfgB_converges_general : ConvergesBy (cfgB 0) hn3 :=
  convergesBy hn3 cfgB_invariant cfgB_apartOnBoundaries

end ExamplesThree

end DPSS
