/-
# DPSS — the nondeterminism, modelled as a relation, and proved to collapse

**C1′**, and what is left of gap 5.

`newDir` assigns each drone a heading as a **function** of the configuration.
The paper's protocol does not: it leaves one thing open, and says exactly what:

> The description of the algorithm leaves two things unspecified. […] Second,
> it does not specify what happens when a group of three or more drones come
> together and determine that three of them are within the middle drone's
> interval; in that case, **the middle drone can escort either neighbor to
> their common border**.
>
> — Avigad–van Doorn, §2

`PLAN.md` sized C1′ as "make `step` a relation and re-prove the development over
an arbitrary trajectory": roughly thirty primitive lemmas re-derived from a
specification, and every statement in all 31 files gaining a parameter.

**That is not what this file does**, because the same passage of the paper says
why it is not necessary:

> Neither of these issues bears on the results reported below, since our upper
> bound only concerns **phase 2, where these issues do not arise**.

That is a claim about reachable states, and it is provable. So:

1. `LegitDir c d` specifies **every** heading assignment the protocol permits,
   with the middle drone's choice left genuinely open.
2. `legitDir_newDir` — the standard resolution is one of them.
3. `escortDir_eq_escortDirLeft_of_grouped` — **the collapse**. Under the
   standing invariants, a drone together with *both* neighbours has the same
   answer either way, so the choice is not a choice.
4. `legitDir_unique` — hence the specification has exactly one solution, and
5. `isRun_eq_run` — hence every trajectory of the step **relation** is the run
   of the step **function**, and `convergesBy_of_isRun` holds for all of them.

## Why the collapse happens

The two escort headings differ exactly when the meeting point lies strictly
inside the middle drone's own interval — which is precisely the paper's "three
of them are within the middle drone's interval". Suppose it does, at `p` with
`leftEnd i < p < rightEnd i`, with no border or separation due. Then:

* the pair `(i, i+1)` is together at `p < commonEnd i`. If they head apart,
  `ApartOnBoundary` puts them *on* `commonEnd i` — contradiction. If they
  escort, escort coherence points them at `commonEnd i`, which is to the right,
  so drone `i` heads **right**;
* so drone `i` heads right, and the pair `(i−1, i)` is together at
  `p > commonEnd (i−1)`. Heading apart puts them on `commonEnd (i−1)` —
  contradiction. Escorting points them at `commonEnd (i−1)`, to the *left* —
  contradicting that `i` heads right. And `i−1` heading right with `i` heading
  left is ruled out because `i` heads right.

Every case closes. The configuration the paper leaves unspecified is one the
algorithm never builds.

## The freedom is real, off the reachable set

`ExamplesThree.triple` is a three-drone configuration where the middle drone is
together with both neighbours and the two escort headings genuinely differ — so
`LegitDir` really is wider than `newDir`, and the collapse theorem is not
vacuous. By the collapse theorem, that configuration cannot satisfy the
standing invariants; `triple_not_invariant` says so.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2.
-/

import Dpss.SharpnessGeneral

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Being in a group

The paper's "a group of three or more drones come together" is, for the middle
drone, being co-located with a neighbour on each side. Note this is weaker than
a *meet*: a drone already escorting a neighbour is grouped with it without any
event being due. -/

/-- Drone `i` is together with its right-hand neighbour. -/
def GroupedRight (c : Config n) (i : Fin n) : Prop :=
  ∃ h : i.val + 1 < n, c.CoLocated i h

/-- Drone `i` is together with its left-hand neighbour. -/
def GroupedLeft (c : Config n) (i : Fin n) : Prop :=
  ∃ h : 0 < i.val, c.CoLocated (prevIdx i h) (prevIdx_lt i h)

theorem groupedRight_of_meetRight {c : Config n} {i : Fin n}
    (h : c.MeetRight i) : c.GroupedRight i := by
  obtain ⟨hlt, hco, -⟩ := h
  exact ⟨hlt, hco⟩

theorem groupedLeft_of_meetLeft {c : Config n} {i : Fin n}
    (h : c.MeetLeft i) : c.GroupedLeft i := by
  obtain ⟨hz, hco, -⟩ := h
  exact ⟨hz, hco⟩

/-! ## Every heading assignment the protocol permits -/

/-- **The specification of a legitimate heading update.**

Borders and separations are determined by the protocol. A meeting drone escorts
*a* neighbour it is together with, towards the boundary it shares with that
neighbour — and when it is together with both, which is the case the paper
deliberately leaves open, either is permitted. A drone with nothing due carries
on. -/
structure LegitDir (c : Config n) (d : Fin n → Dir) : Prop where
  /-- A drone at the left border turns round. -/
  border_left : ∀ i, c.AtLeftBorder i → d i = Dir.right
  /-- A drone at the right border turns round. -/
  border_right : ∀ i, ¬ c.AtLeftBorder i → c.AtRightBorder i → d i = Dir.left
  /-- A separation from the right-hand neighbour sends this drone back left. -/
  sep_right : ∀ i, ¬ c.AtLeftBorder i → ¬ c.AtRightBorder i →
    c.SepRight i → d i = Dir.left
  /-- A separation from the left-hand neighbour sends this drone back right. -/
  sep_left : ∀ i, ¬ c.AtLeftBorder i → ¬ c.AtRightBorder i →
    ¬ c.SepRight i → c.SepLeft i → d i = Dir.right
  /-- **The open case.** A meeting drone escorts a neighbour it is together
  with, to the boundary it shares with that neighbour. Together with both, it
  may choose. -/
  meet : ∀ i, ¬ c.AtLeftBorder i → ¬ c.AtRightBorder i →
    ¬ c.SepRight i → ¬ c.SepLeft i → (c.MeetRight i ∨ c.MeetLeft i) →
    (c.GroupedRight i ∧ d i = c.escortDir i) ∨
    (c.GroupedLeft i ∧ d i = c.escortDirLeft i)
  /-- A drone with nothing due carries on. -/
  none : ∀ i, ¬ c.AtLeftBorder i → ¬ c.AtRightBorder i →
    ¬ c.SepRight i → ¬ c.SepLeft i → ¬ c.MeetRight i → ¬ c.MeetLeft i →
    d i = c.dir i

/-- **The standard resolution is a legitimate one.** -/
theorem legitDir_newDir (c : Config n) : LegitDir c (fun i => c.newDir i) where
  border_left := fun i h => newDir_atLeftBorder h
  border_right := fun i h1 h2 => newDir_atRightBorder h1 h2
  sep_right := fun i h1 h2 h3 => by
    unfold newDir; rw [if_neg h1, if_neg h2, if_pos h3]
  sep_left := fun i h1 h2 h3 h4 => by
    unfold newDir; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  meet := fun i h1 h2 h3 h4 hm => by
    rcases hm with hmr | hml
    · refine Or.inl ⟨groupedRight_of_meetRight hmr, ?_⟩
      unfold newDir
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos hmr]
    · by_cases hmr : c.MeetRight i
      · refine Or.inl ⟨groupedRight_of_meetRight hmr, ?_⟩
        unfold newDir
        rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos hmr]
      · refine Or.inr ⟨groupedLeft_of_meetLeft hml, ?_⟩
        unfold newDir
        rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg hmr, if_pos hml]
  none := fun i h1 h2 h3 h4 h5 h6 => newDir_of_noEvent h1 h2 h3 h4 h5 h6

/-! ## The collapse

The mathematical content of this file: on a configuration the algorithm can
actually reach, a drone together with both neighbours gets the same answer
whichever it escorts. -/

/-- **A drone together with both neighbours, with no separation due, is never
strictly inside its own interval.** This is the paper's "three of them are
within the middle drone's interval", and it cannot happen. -/
theorem not_strictly_inside_of_grouped {c : Config n} (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) {i : Fin n}
    (hgr : c.GroupedRight i) (hgl : c.GroupedLeft i)
    (hnsr : ¬ c.SepRight i) (hnsl : ¬ c.SepLeft i) :
    ¬ (leftEnd i < c.pos i ∧ c.pos i < rightEnd i) := by
  rintro ⟨hgtL, hltR⟩
  obtain ⟨hR, hcoR⟩ := hgr
  obtain ⟨hz, hcoL⟩ := hgl
  have hposR : c.pos (nextIdx i hR) = c.pos i := by
    have hx : c.gap i hR = 0 := hcoR
    unfold gap at hx; linarith
  have hposL : c.pos (prevIdx i hz) = c.pos i := by
    have hx : c.gap (prevIdx i hz) (prevIdx_lt i hz) = 0 := hcoL
    unfold gap at hx
    rw [nextIdx_prevIdx] at hx
    linarith
  have hcommonL : commonEnd (prevIdx i hz) = leftEnd i := by
    unfold commonEnd
    rw [rightEnd_eq_leftEnd_succ (prevIdx i hz) (prevIdx_lt i hz)]
    congr 1
    exact nextIdx_prevIdx i hz
  rcases Dir.eq_left_or_right (c.dir i) with hdi | hdi
  · rcases Dir.eq_left_or_right (c.dir (nextIdx i hR)) with hdj | hdj
    · -- escorting leftward: coherence points them at `commonEnd i`, to the left
      have he : c.Escorting i hR := ⟨hcoR, by rw [hdi, hdj]⟩
      have hc := hi.escortsCoherent i hR he
      unfold separationTime at hc
      rw [hdi, Dir.sign_left] at hc
      unfold commonEnd at hc
      linarith
    · -- heading apart: `ApartOnBoundary` puts them on the boundary they share
      have hx := hab i hR hcoR hdi hdj
      unfold commonEnd at hx
      linarith
  · rcases Dir.eq_left_or_right (c.dir (prevIdx i hz)) with hdp | hdp
    · -- the left pair heads apart, so it sits on `commonEnd (i−1) = leftEnd i`
      have hx := hab (prevIdx i hz) (prevIdx_lt i hz) hcoL hdp
        (by rw [nextIdx_prevIdx]; exact hdi)
      rw [hcommonL, hposL] at hx
      linarith
    · -- the left pair escorts rightward: coherence caps this drone at `leftEnd i`
      have he : c.Escorting (prevIdx i hz) (prevIdx_lt i hz) := by
        refine ⟨hcoL, ?_⟩
        rw [nextIdx_prevIdx, hdp, hdi]
      have hc := hi.escortsCoherent _ _ he
      unfold separationTime at hc
      rw [hdp, Dir.sign_right, hcommonL, hposL] at hc
      linarith

/-- **The collapse.** A drone together with both neighbours reaches the same
heading whichever neighbour it escorts, so the paper's open choice is not a
choice on any configuration the algorithm builds. -/
theorem escortDir_eq_escortDirLeft_of_grouped {c : Config n} (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) {i : Fin n}
    (hgr : c.GroupedRight i) (hgl : c.GroupedLeft i)
    (hnsr : ¬ c.SepRight i) (hnsl : ¬ c.SepLeft i) :
    c.escortDir i = c.escortDirLeft i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hLR : leftEnd i < rightEnd i := leftEnd_lt_rightEnd hn i
  have hkey := not_strictly_inside_of_grouped hi hab hgr hgl hnsr hnsl
  -- the two answers differ only strictly inside the interval, and the
  -- endpoints are excluded by the absent separations
  have hne_R : c.pos i ≠ commonEnd i := by
    intro hx
    obtain ⟨hR, hcoR⟩ := hgr
    exact hnsr ⟨hR, hcoR, hx⟩
  have hne_L : c.pos i ≠ leftEnd i := by
    intro hx
    obtain ⟨hz, hcoL⟩ := hgl
    refine hnsl ⟨hz, hcoL, ?_⟩
    have hposL : c.pos (prevIdx i hz) = c.pos i := by
      have hg : c.gap (prevIdx i hz) (prevIdx_lt i hz) = 0 := hcoL
      unfold gap at hg
      rw [nextIdx_prevIdx] at hg
      linarith
    have hcommonL : commonEnd (prevIdx i hz) = leftEnd i := by
      unfold commonEnd
      rw [rightEnd_eq_leftEnd_succ (prevIdx i hz) (prevIdx_lt i hz)]
      congr 1
      exact nextIdx_prevIdx i hz
    rw [hcommonL, hposL, hx]
  have hneR' : c.pos i ≠ rightEnd i := by unfold commonEnd at hne_R; exact hne_R
  rcases lt_or_gt_of_ne hne_L with hlt | hgt
  · -- before its own left endpoint: both headings point right
    unfold escortDir escortDirLeft
    rw [if_pos (show c.pos i < commonEnd i by unfold commonEnd; linarith),
      if_pos hlt]
  · rcases lt_or_gt_of_ne hneR' with hlt2 | hgt2
    · exact absurd ⟨hgt, hlt2⟩ hkey
    · -- beyond its own right endpoint: both point left
      unfold escortDir escortDirLeft
      rw [if_neg (show ¬ c.pos i < commonEnd i by unfold commonEnd; linarith),
        if_neg (show ¬ c.pos i < leftEnd i by linarith)]

/-- **The specification has exactly one solution.** -/
theorem legitDir_unique {c : Config n} (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) {d : Fin n → Dir} (hd : LegitDir c d) :
    d = fun i => c.newDir i := by
  funext i
  by_cases h1 : c.AtLeftBorder i
  · rw [hd.border_left i h1, newDir_atLeftBorder h1]
  by_cases h2 : c.AtRightBorder i
  · rw [hd.border_right i h1 h2, newDir_atRightBorder h1 h2]
  by_cases h3 : c.SepRight i
  · rw [hd.sep_right i h1 h2 h3]
    unfold newDir; rw [if_neg h1, if_neg h2, if_pos h3]
  by_cases h4 : c.SepLeft i
  · rw [hd.sep_left i h1 h2 h3 h4]
    unfold newDir; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  by_cases h5 : c.MeetRight i
  · have hnd : c.newDir i = c.escortDir i := by
      unfold newDir; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    rcases hd.meet i h1 h2 h3 h4 (Or.inl h5) with ⟨-, hdi⟩ | ⟨hgl, hdi⟩
    · rw [hdi, hnd]
    · rw [hdi, hnd,
        escortDir_eq_escortDirLeft_of_grouped hi hab
          (groupedRight_of_meetRight h5) hgl h3 h4]
  by_cases h6 : c.MeetLeft i
  · have hnd : c.newDir i = c.escortDirLeft i := by
      unfold newDir
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
    rcases hd.meet i h1 h2 h3 h4 (Or.inr h6) with ⟨hgr, hdi⟩ | ⟨-, hdi⟩
    · rw [hdi, hnd,
        escortDir_eq_escortDirLeft_of_grouped hi hab hgr
          (groupedLeft_of_meetLeft h6) h3 h4]
    · rw [hdi, hnd]
  · rw [hd.none i h1 h2 h3 h4 h5 h6, newDir_of_noEvent h1 h2 h3 h4 h5 h6]

/-! ## The step relation, and its trajectories -/

/-- **One step of the system, as a relation.** Fly to the next event, then let
the headings be *any* legitimate resolution of what is due. -/
def StepRel (hn : 0 < n) (c c' : Config n) : Prop :=
  ∃ d : Fin n → Dir,
    LegitDir (c.advance (c.timeToNextEvent hn)) d ∧
    c' = { time := (c.advance (c.timeToNextEvent hn)).time,
           pos := (c.advance (c.timeToNextEvent hn)).pos,
           dir := d }

/-- A trajectory of the relation, from a given start. -/
def IsRun (c : Config n) (hn : 0 < n) (f : ℕ → Config n) : Prop :=
  f 0 = c ∧ ∀ k, StepRel hn (f k) (f (k + 1))

/-- The deterministic step is one of the relation's successors. -/
theorem stepRel_step (c : Config n) (hn : 0 < n) : StepRel hn c (c.step hn) :=
  ⟨fun i => (c.advance (c.timeToNextEvent hn)).newDir i,
    legitDir_newDir _, rfl⟩

/-! ### Carrying the standing conditions across the flight

The relation reads the configuration *after* flying, so the two standing
conditions are needed there rather than at the start of the step. -/

theorem escortsCoherent_advance {c : Config n} (hn : 0 < n) (hi : c.Invariant) :
    (c.advance (c.timeToNextEvent hn)).EscortsCoherent := by
  intro i h he
  have hdirs : c.dir i = c.dir (nextIdx i h) := he.2
  have hrate : c.sepRate i h = 0 := by unfold sepRate; rw [hdirs]; ring
  have hg : (c.advance (c.timeToNextEvent hn)).gap i h = 0 := he.1
  rw [gap_advance, hrate] at hg
  have hgapc : c.gap i h = 0 := by linarith
  have heC : c.Escorting i h := ⟨hgapc, hdirs⟩
  have hbound : c.timeToNextEvent hn ≤ c.separationTime i :=
    le_trans (timeToNextEvent_le hn i) (droneNextTime_le_separationTime heC)
  rw [separationTime_advance]
  linarith

theorem invariant_advance {c : Config n} (hn : 0 < n) (hi : c.Invariant) :
    (c.advance (c.timeToNextEvent hn)).Invariant :=
  ⟨onPerimeter_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent,
   adjOrdered_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent,
   escortsCoherent_advance hn hi⟩

theorem apartOnBoundaries_advance {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) :
    (c.advance (c.timeToNextEvent hn)).ApartOnBoundaries := by
  intro i h hco hL hR
  exact apart_transfer (hab i h) (hi.adjOrdered i h)
    (timeToNextEvent_nonneg hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent)
    hL hR hco

/-! ### The relation is a function, where it matters -/

/-- **A configuration the algorithm can reach has exactly one legitimate
successor.** -/
theorem stepRel_eq_step {c c' : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) (h : StepRel hn c c') : c' = c.step hn := by
  obtain ⟨d, hleg, rfl⟩ := h
  have hdeq : d = fun i => (c.advance (c.timeToNextEvent hn)).newDir i :=
    legitDir_unique (invariant_advance hn hi)
      (apartOnBoundaries_advance hn hi hab) hleg
  rw [hdeq]
  rfl

/-- **Every trajectory of the relation is the run of the function.** -/
theorem isRun_eq_run {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) {f : ℕ → Config n} (hf : IsRun c hn f) :
    ∀ k, f k = c.run hn k := by
  intro k
  induction k with
  | zero => rw [run_zero]; exact hf.1
  | succ k ih =>
    have hstep := hf.2 k
    rw [ih] at hstep
    rw [run_succ]
    exact stepRel_eq_step hn (invariant_run hn hi k)
      (apartOnBoundaries_run hn hi hab k) hstep

/-! ## What this buys

Every theorem in the development is now a theorem about every resolution of the
paper's nondeterminism, because there is only one. -/

/-- **Theorem 2.1, for every trajectory of the step relation.** -/
theorem convergesBy_of_isRun {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) {f : ℕ → Config n} (hf : IsRun c hn f)
    (i : Fin n) (j : ℕ) (hj : c.time + (2 - 1 / (n : ℝ)) ≤ (f j).time) :
    leftEnd i ≤ (f j).pos i ∧ (f j).pos i ≤ rightEnd i := by
  rw [isRun_eq_run hn hi hab hf j] at hj ⊢
  exact convergesBy hn hi hab i j hj

/-- **Non-Zeno, for every trajectory of the step relation.** -/
theorem nonZeno_of_isRun {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    (hab : c.ApartOnBoundaries) {f : ℕ → Config n} (hf : IsRun c hn f) (T : ℝ) :
    ∃ k, T < (f k).time := by
  obtain ⟨k, hk⟩ := nonZeno hn hi T
  exact ⟨k, by rw [isRun_eq_run hn hi hab hf k]; exact hk⟩

end Config

/-! ## The freedom is real, off the reachable set

Without this the collapse theorem would be an elaborate way of saying nothing.
-/

namespace ExamplesThree

open Config

/-- Three drones at `1/2`, the outer two closing on the middle one from the
right. The middle drone is together with **both** neighbours, and `1/2` is
strictly inside its interval `[1/3, 2/3]` — so escorting left and escorting
right give genuinely different headings. -/
noncomputable def triple : Config 3 where
  time := 0
  pos := fun _ => 1 / 2
  dir := fun i => if i.val = 2 then Dir.left else Dir.right

@[simp] theorem triple_pos (i : Fin 3) : triple.pos i = 1 / 2 := rfl
@[simp] theorem triple_dir_e0 : triple.dir e0 = Dir.right := rfl
@[simp] theorem triple_dir_e1 : triple.dir e1 = Dir.right := rfl
@[simp] theorem triple_dir_e2 : triple.dir e2 = Dir.left := rfl

/-- **The open case of the specification is genuinely open.** -/
theorem triple_ambiguous :
    ¬ triple.AtLeftBorder e1 ∧ ¬ triple.AtRightBorder e1 ∧
    ¬ triple.SepRight e1 ∧ ¬ triple.SepLeft e1 ∧
    triple.MeetRight e1 ∧ triple.GroupedRight e1 ∧ triple.GroupedLeft e1 ∧
    triple.escortDir e1 ≠ triple.escortDirLeft e1 := by
  have hcoR : triple.CoLocated e1 h12 := by
    unfold CoLocated gap; rw [nextIdx_e1, triple_pos, triple_pos]; norm_num
  have hcoL : triple.CoLocated e0 h01 := by
    unfold CoLocated gap; rw [nextIdx_e0, triple_pos, triple_pos]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ⟨h12, hcoR, ⟨triple_dir_e1, ?_⟩⟩, ⟨h12, hcoR⟩,
    ⟨by norm_num [e1], hcoL⟩, ?_⟩
  · rintro ⟨hp, -⟩; rw [triple_pos] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [triple_pos] at hp; norm_num at hp
  · rintro ⟨-, -, hp⟩; rw [triple_pos, commonEnd_e1] at hp; norm_num at hp
  · rintro ⟨hz, -, hp⟩
    have hx : (1 : ℝ) / 2 = commonEnd e0 := hp
    rw [commonEnd_e0] at hx
    norm_num at hx
  · rw [nextIdx_e1]; exact triple_dir_e2
  · unfold escortDir escortDirLeft
    rw [if_pos (show triple.pos e1 < commonEnd e1 by
      rw [triple_pos, commonEnd_e1]; norm_num),
      if_neg (show ¬ triple.pos e1 < leftEnd e1 by
      rw [triple_pos, leftEnd_e1]; norm_num)]
    exact fun hc => Dir.noConfusion hc

/-- **And the collapse theorem says why it does not matter**: a configuration
exhibiting the ambiguity cannot satisfy the standing conditions, so the
algorithm never reaches one. -/
theorem triple_not_reachable :
    ¬ (triple.Invariant ∧ triple.ApartOnBoundaries) := by
  rintro ⟨hi, hab⟩
  obtain ⟨-, -, hnsr, hnsl, -, hgr, hgl, hne⟩ := triple_ambiguous
  exact hne (escortDir_eq_escortDirLeft_of_grouped hi hab hgr hgl hnsr hnsl)

end ExamplesThree

end DPSS
