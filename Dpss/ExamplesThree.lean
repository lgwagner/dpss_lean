/-
# DPSS — three drones

`Examples.lean` traced two drones. With only two, several parts of the model
are never exercised at all: there is no *middle* drone, so `SepLeft` and
`MeetLeft` never fire for a drone that also has a right-hand neighbour, and no
cascade is possible. Avigad–van Doorn call `n = 3` the first interesting case.

This file builds the steady state for three drones and proves it is a genuine
cycle, exercising exactly that machinery: on each step the middle drone
separates from one neighbour while an end drone bounces off a border.

The assigned intervals are `[0, 1/3]`, `[1/3, 2/3]` and `[2/3, 1]`.

    B = (1/3 ←, 1/3 →, 1 ←)        C = (0 →, 2/3 ←, 2/3 →)

    B ──1/3──▶ C ──1/3──▶ B ──▶ ⋯        period 2/3 = 2/n ✓
-/

import Dpss.Examples

set_option linter.style.header false

namespace DPSS

namespace ExamplesThree

open Config

theorem hn3 : 0 < 3 := by norm_num

def e0 : Fin 3 := ⟨0, by norm_num⟩
def e1 : Fin 3 := ⟨1, by norm_num⟩
def e2 : Fin 3 := ⟨2, by norm_num⟩

theorem h01 : e0.val + 1 < 3 := by norm_num [e0]
theorem h12 : e1.val + 1 < 3 := by norm_num [e1]

@[simp] theorem nextIdx_e0 : nextIdx e0 h01 = e1 := rfl
@[simp] theorem nextIdx_e1 : nextIdx e1 h12 = e2 := rfl

theorem fin3_cases (i : Fin 3) : i = e0 ∨ i = e1 ∨ i = e2 := by
  rcases i with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-! ## Geometry -/

theorem leftEnd_e0 : leftEnd e0 = 0 := by unfold leftEnd e0; norm_num
theorem rightEnd_e0 : rightEnd e0 = 1 / 3 := by unfold rightEnd e0; norm_num
theorem leftEnd_e1 : leftEnd e1 = 1 / 3 := by unfold leftEnd e1; norm_num
theorem rightEnd_e1 : rightEnd e1 = 2 / 3 := by unfold rightEnd e1; norm_num
theorem leftEnd_e2 : leftEnd e2 = 2 / 3 := by unfold leftEnd e2; norm_num
theorem rightEnd_e2 : rightEnd e2 = 1 := by unfold rightEnd e2; norm_num
theorem commonEnd_e0 : commonEnd e0 = 1 / 3 := rightEnd_e0
theorem commonEnd_e1 : commonEnd e1 = 2 / 3 := rightEnd_e1

/-! ## Evaluating the schedule for three drones -/

theorem timeToNextEvent_three (c : Config 3) :
    c.timeToNextEvent hn3
      = min (c.droneNextTime e0) (min (c.droneNextTime e1) (c.droneNextTime e2)) := by
  unfold timeToNextEvent
  apply le_antisymm
  · refine le_min (Finset.inf'_le _ (Finset.mem_univ _))
      (le_min (Finset.inf'_le _ (Finset.mem_univ _))
        (Finset.inf'_le _ (Finset.mem_univ _)))
  · refine Finset.le_inf' _ _ (fun i _ => ?_)
    rcases fin3_cases i with h | h | h <;> subst h
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- The rightmost drone has no right-hand neighbour. -/
theorem droneNextTime_e2 (c : Config 3) :
    c.droneNextTime e2 = c.borderTime e2 := by
  unfold droneNextTime
  rw [dif_neg (by norm_num [e2])]

theorem droneNextTime_apart (c : Config 3) {i : Fin 3} (h : i.val + 1 < 3)
    (hA : ¬ c.Approaching i h) (hE : ¬ c.Escorting i h) :
    c.droneNextTime i = c.borderTime i := by
  unfold droneNextTime
  rw [dif_pos h, if_neg hA, if_neg hE]

theorem droneNextTime_approaching (c : Config 3) {i : Fin 3} (h : i.val + 1 < 3)
    (hA : c.Approaching i h) :
    c.droneNextTime i = min (c.borderTime i) (c.meetTime i h) := by
  unfold droneNextTime
  rw [dif_pos h, if_pos hA]

/-! ## Events that cannot occur at the ends -/

theorem not_sepRight_e2 (c : Config 3) : ¬ c.SepRight e2 := by
  rintro ⟨h, -⟩; exact absurd h (by norm_num [e2])

theorem not_meetRight_e2 (c : Config 3) : ¬ c.MeetRight e2 := by
  rintro ⟨h, -⟩; exact absurd h (by norm_num [e2])

theorem not_sepLeft_e0 (c : Config 3) : ¬ c.SepLeft e0 := by
  rintro ⟨h, -⟩; exact absurd h (by norm_num [e0])

theorem not_meetLeft_e0 (c : Config 3) : ¬ c.MeetLeft e0 := by
  rintro ⟨h, -⟩; exact absurd h (by norm_num [e0])

/-! ## The two steady-state configurations -/

/-- Left drone at its right endpoint heading back left; middle drone there too
heading right; right drone at the far border turning. -/
noncomputable def cfgB (t : ℝ) : Config 3 where
  time := t
  pos := fun i => if i.val = 2 then 1 else 1 / 3
  dir := fun i => if i.val = 1 then Dir.right else Dir.left

/-- Left drone at the left border turning; middle and right drones together at
the boundary they share. -/
noncomputable def cfgC (t : ℝ) : Config 3 where
  time := t
  pos := fun i => if i.val = 0 then 0 else 2 / 3
  dir := fun i => if i.val = 1 then Dir.left else Dir.right

@[simp] theorem cfgB_pos_e0 (t : ℝ) : (cfgB t).pos e0 = 1 / 3 := rfl
@[simp] theorem cfgB_pos_e1 (t : ℝ) : (cfgB t).pos e1 = 1 / 3 := rfl
@[simp] theorem cfgB_pos_e2 (t : ℝ) : (cfgB t).pos e2 = 1 := rfl
@[simp] theorem cfgB_dir_e0 (t : ℝ) : (cfgB t).dir e0 = Dir.left := rfl
@[simp] theorem cfgB_dir_e1 (t : ℝ) : (cfgB t).dir e1 = Dir.right := rfl
@[simp] theorem cfgB_dir_e2 (t : ℝ) : (cfgB t).dir e2 = Dir.left := rfl

@[simp] theorem cfgC_pos_e0 (t : ℝ) : (cfgC t).pos e0 = 0 := rfl
@[simp] theorem cfgC_pos_e1 (t : ℝ) : (cfgC t).pos e1 = 2 / 3 := rfl
@[simp] theorem cfgC_pos_e2 (t : ℝ) : (cfgC t).pos e2 = 2 / 3 := rfl
@[simp] theorem cfgC_dir_e0 (t : ℝ) : (cfgC t).dir e0 = Dir.right := rfl
@[simp] theorem cfgC_dir_e1 (t : ℝ) : (cfgC t).dir e1 = Dir.left := rfl
@[simp] theorem cfgC_dir_e2 (t : ℝ) : (cfgC t).dir e2 = Dir.right := rfl

/-! ## How long each configuration runs -/

theorem cfgB_timeToNext (t : ℝ) : (cfgB t).timeToNextEvent hn3 = 1 / 3 := by
  have hA0 : ¬ (cfgB t).Approaching e0 h01 := by
    rintro ⟨h1, -⟩; rw [cfgB_dir_e0] at h1; exact Dir.noConfusion h1
  have hE0 : ¬ (cfgB t).Escorting e0 h01 := by
    rintro ⟨-, h2⟩
    rw [nextIdx_e0, cfgB_dir_e0, cfgB_dir_e1] at h2
    exact Dir.noConfusion h2
  -- the middle and right drones *are* closing on each other here
  have hA1 : (cfgB t).Approaching e1 h12 := by
    refine ⟨cfgB_dir_e1 t, ?_⟩
    rw [nextIdx_e1]; exact cfgB_dir_e2 t
  have hgap1 : (cfgB t).gap e1 h12 = 2 / 3 := by
    unfold gap; rw [nextIdx_e1, cfgB_pos_e1, cfgB_pos_e2]; norm_num
  rw [timeToNextEvent_three, droneNextTime_e2,
      droneNextTime_apart _ h01 hA0 hE0, droneNextTime_approaching _ h12 hA1,
      borderTime_of_left (cfgB_dir_e0 t), borderTime_of_right (cfgB_dir_e1 t),
      borderTime_of_left (cfgB_dir_e2 t)]
  unfold meetTime
  rw [hgap1, cfgB_pos_e0, cfgB_pos_e1, cfgB_pos_e2]
  norm_num

theorem cfgC_timeToNext (t : ℝ) : (cfgC t).timeToNextEvent hn3 = 1 / 3 := by
  have hA0 : (cfgC t).Approaching e0 h01 := by
    refine ⟨cfgC_dir_e0 t, ?_⟩
    rw [nextIdx_e0]; exact cfgC_dir_e1 t
  have hgap0 : (cfgC t).gap e0 h01 = 2 / 3 := by
    unfold gap; rw [nextIdx_e0, cfgC_pos_e0, cfgC_pos_e1]; norm_num
  have hA1 : ¬ (cfgC t).Approaching e1 h12 := by
    rintro ⟨h1, -⟩; rw [cfgC_dir_e1] at h1; exact Dir.noConfusion h1
  have hE1 : ¬ (cfgC t).Escorting e1 h12 := by
    rintro ⟨-, h2⟩
    rw [nextIdx_e1, cfgC_dir_e1, cfgC_dir_e2] at h2
    exact Dir.noConfusion h2
  rw [timeToNextEvent_three, droneNextTime_e2,
      droneNextTime_approaching _ h01 hA0, droneNextTime_apart _ h12 hA1 hE1,
      borderTime_of_right (cfgC_dir_e0 t), borderTime_of_left (cfgC_dir_e1 t),
      borderTime_of_right (cfgC_dir_e2 t)]
  unfold meetTime
  rw [hgap0, cfgC_pos_e0, cfgC_pos_e1, cfgC_pos_e2]
  norm_num

/-! ## The two steps

Each step fires **two** events at once: the middle drone separates from one
neighbour while an end drone bounces off a border. That simultaneity is what
`newDir` exists for, and it is not exercised at all when `n = 2`. -/

theorem prevIdx_e1 : prevIdx e1 (by norm_num [e1]) = e0 := rfl
theorem prevIdx_e2 : prevIdx e2 (by norm_num [e2]) = e1 := rfl

theorem step_cfgB (t : ℝ) : (cfgB t).step hn3 = cfgC (t + 1 / 3) := by
  have hdt := cfgB_timeToNext t
  set c' := (cfgB t).advance (1 / 3) with hc'
  have hp0 : c'.pos e0 = 0 := by
    simp only [hc', advance_pos, cfgB_pos_e0, cfgB_dir_e0, Dir.sign_left]; norm_num
  have hp1 : c'.pos e1 = 2 / 3 := by
    simp only [hc', advance_pos, cfgB_pos_e1, cfgB_dir_e1, Dir.sign_right]; norm_num
  have hp2 : c'.pos e2 = 2 / 3 := by
    simp only [hc', advance_pos, cfgB_pos_e2, cfgB_dir_e2, Dir.sign_left]; norm_num
  -- the middle and right drones have arrived at the boundary they share
  have hsep12 : c'.AtSeparation e1 h12 := by
    refine ⟨?_, ?_⟩
    · unfold CoLocated gap; rw [nextIdx_e1, hp1, hp2]; norm_num
    · rw [hp1, commonEnd_e1]
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt]; rfl
  · rcases fin3_cases i with h | h | h <;> subst h
    · simp only [step_pos, hdt, cfgB_pos_e0, cfgB_dir_e0, Dir.sign_left,
        cfgC_pos_e0]; norm_num
    · simp only [step_pos, hdt, cfgB_pos_e1, cfgB_dir_e1, Dir.sign_right,
        cfgC_pos_e1]; norm_num
    · simp only [step_pos, hdt, cfgB_pos_e2, cfgB_dir_e2, Dir.sign_left,
        cfgC_pos_e2]; norm_num
  · rcases fin3_cases i with h | h | h <;> subst h
    · -- left drone bounces off the left border
      rw [step_dir, hdt, cfgC_dir_e0]
      apply newDir_atLeftBorder
      exact ⟨hp0, by simp only [advance_newDir_dir, cfgB_dir_e0]⟩
    · -- middle drone separates from its right neighbour
      rw [step_dir, hdt, cfgC_dir_e1]
      unfold newDir
      rw [if_neg, if_neg, if_pos ⟨h12, hsep12⟩]
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
    · -- right drone separates from its left neighbour
      rw [step_dir, hdt, cfgC_dir_e2]
      unfold newDir
      rw [if_neg, if_neg, if_neg (not_sepRight_e2 _),
          if_pos ⟨by norm_num [e2], hsep12⟩]
      · rintro ⟨hq, -⟩; rw [hp2] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp2] at hq; norm_num at hq

theorem step_cfgC (t : ℝ) : (cfgC t).step hn3 = cfgB (t + 1 / 3) := by
  have hdt := cfgC_timeToNext t
  set c' := (cfgC t).advance (1 / 3) with hc'
  have hp0 : c'.pos e0 = 1 / 3 := by
    simp only [hc', advance_pos, cfgC_pos_e0, cfgC_dir_e0, Dir.sign_right]; norm_num
  have hp1 : c'.pos e1 = 1 / 3 := by
    simp only [hc', advance_pos, cfgC_pos_e1, cfgC_dir_e1, Dir.sign_left]; norm_num
  have hp2 : c'.pos e2 = 1 := by
    simp only [hc', advance_pos, cfgC_pos_e2, cfgC_dir_e2, Dir.sign_right]; norm_num
  -- the left and middle drones have arrived at the boundary they share
  have hsep01 : c'.AtSeparation e0 h01 := by
    refine ⟨?_, ?_⟩
    · unfold CoLocated gap; rw [nextIdx_e0, hp0, hp1]; norm_num
    · rw [hp0, commonEnd_e0]
  have hnsep12 : ¬ c'.AtSeparation e1 h12 := by
    rintro ⟨hco, -⟩
    unfold CoLocated gap at hco
    rw [nextIdx_e1, hp1, hp2] at hco
    norm_num at hco
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt]; rfl
  · rcases fin3_cases i with h | h | h <;> subst h
    · simp only [step_pos, hdt, cfgC_pos_e0, cfgC_dir_e0, Dir.sign_right,
        cfgB_pos_e0]; norm_num
    · simp only [step_pos, hdt, cfgC_pos_e1, cfgC_dir_e1, Dir.sign_left,
        cfgB_pos_e1]; norm_num
    · simp only [step_pos, hdt, cfgC_pos_e2, cfgC_dir_e2, Dir.sign_right,
        cfgB_pos_e2]; norm_num
  · rcases fin3_cases i with h | h | h <;> subst h
    · -- left drone separates from the middle one
      rw [step_dir, hdt, cfgB_dir_e0]
      unfold newDir
      rw [if_neg, if_neg, if_pos ⟨h01, hsep01⟩]
      · rintro ⟨hq, -⟩; rw [hp0] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp0] at hq; norm_num at hq
    · -- middle drone separates from its *left* neighbour: the case two drones
      -- can never produce
      rw [step_dir, hdt, cfgB_dir_e1]
      unfold newDir
      rw [if_neg, if_neg, if_neg, if_pos ⟨by norm_num [e1], hsep01⟩]
      · rintro ⟨_hh, hs⟩; exact hnsep12 hs
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
    · -- right drone bounces off the right border
      rw [step_dir, hdt, cfgB_dir_e2]
      apply newDir_atRightBorder
      · rintro ⟨hq, -⟩; rw [hp2] at hq; norm_num at hq
      · exact ⟨hp2, by simp only [advance_newDir_dir, cfgC_dir_e2]⟩

/-! ## The cycle -/

/-- **The three-drone steady state, at every step index.** Each step takes
`1/3`, and the system alternates between the two configurations forever. -/
theorem run_cfgB (m : ℕ) :
    (cfgB 0).run hn3 (2 * m) = cfgB (2 * (m : ℝ) / 3) ∧
    (cfgB 0).run hn3 (2 * m + 1) = cfgC (2 * (m : ℝ) / 3 + 1 / 3) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * 0 = 0 from rfl, run_zero]; norm_num
    · rw [show 2 * 0 + 1 = 1 from rfl,
        show (cfgB 0).run hn3 1 = (cfgB 0).step hn3 from rfl, step_cfgB]
      norm_num
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1' : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    have heven : (cfgB 0).run hn3 (2 * (m + 1)) = cfgB (2 * ((m : ℝ) + 1) / 3) := by
      rw [e1', run_succ, h2, step_cfgC]
      congr 1
      ring
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    refine ⟨by rw [hcast]; exact heven, ?_⟩
    have e2' : 2 * (m + 1) + 1 = (2 * (m + 1)) + 1 := rfl
    rw [e2', run_succ, heven, step_cfgB, hcast]

/-- Every drone stays inside its own interval, at every step, forever. -/
theorem cfgB_in_intervals (j : ℕ) (i : Fin 3) :
    leftEnd i ≤ ((cfgB 0).run hn3 j).pos i ∧
      ((cfgB 0).run hn3 j).pos i ≤ rightEnd i := by
  obtain ⟨m, hm⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
  rcases hm with hm | hm <;> subst hm
  · rw [(run_cfgB m).1]
    rcases fin3_cases i with h | h | h <;> subst h
    · rw [leftEnd_e0, rightEnd_e0, cfgB_pos_e0]; norm_num
    · rw [leftEnd_e1, rightEnd_e1, cfgB_pos_e1]; norm_num
    · rw [leftEnd_e2, rightEnd_e2, cfgB_pos_e2]; norm_num
  · rw [(run_cfgB m).2]
    rcases fin3_cases i with h | h | h <;> subst h
    · rw [leftEnd_e0, rightEnd_e0, cfgC_pos_e0]; norm_num
    · rw [leftEnd_e1, rightEnd_e1, cfgC_pos_e1]; norm_num
    · rw [leftEnd_e2, rightEnd_e2, cfgC_pos_e2]; norm_num

/-- **Three drones, synchronized forever.** -/
theorem cfgB_allSync : AllSync (cfgB 0) hn3 0 := by
  intro i
  exact ⟨fun j _ => (cfgB_in_intervals j i).1, fun j _ => (cfgB_in_intervals j i).2⟩

/-- Theorem 2.1 for this configuration. -/
theorem cfgB_converges : ConvergesBy (cfgB 0) hn3 := by
  intro i j _
  exact cfgB_in_intervals j i

/-- **The period is `2/3`, which is `2/n` at `n = 3`.**

A third independent numerical check against the paper, and the first at a team
size where the drones genuinely interact three-way. -/
theorem cfgB_period (m : ℕ) :
    ((cfgB 0).run hn3 (2 * (m + 1))).pos = ((cfgB 0).run hn3 (2 * m)).pos ∧
      ((cfgB 0).run hn3 (2 * (m + 1))).time
        = ((cfgB 0).run hn3 (2 * m)).time + 2 / 3 := by
  rw [(run_cfgB m).1, (run_cfgB (m + 1)).1]
  refine ⟨rfl, ?_⟩
  change 2 * ((m + 1 : ℕ) : ℝ) / 3 = 2 * (m : ℝ) / 3 + 2 / 3
  push_cast
  ring

/-- The standing invariant is satisfiable at `n = 3` too. -/
theorem cfgB_invariant : (cfgB 0).Invariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases fin3_cases i with h | h | h <;> subst h
    · exact ⟨by rw [cfgB_pos_e0]; norm_num, by rw [cfgB_pos_e0]; norm_num⟩
    · exact ⟨by rw [cfgB_pos_e1]; norm_num, by rw [cfgB_pos_e1]; norm_num⟩
    · exact ⟨by rw [cfgB_pos_e2]; norm_num, by rw [cfgB_pos_e2]⟩
  · intro i h
    rcases fin3_cases i with hi | hi | hi <;> subst hi
    · unfold gap; rw [nextIdx_e0, cfgB_pos_e0, cfgB_pos_e1]; norm_num
    · unfold gap; rw [nextIdx_e1, cfgB_pos_e1, cfgB_pos_e2]; norm_num
    · exact absurd h (by norm_num [e2])
  · intro i h he
    rcases fin3_cases i with hi | hi | hi <;> subst hi
    · exfalso
      have h2 := he.2
      rw [nextIdx_e0, cfgB_dir_e0, cfgB_dir_e1] at h2
      exact Dir.noConfusion h2
    · exfalso
      have h2 := he.2
      rw [nextIdx_e1, cfgB_dir_e1, cfgB_dir_e2] at h2
      exact Dir.noConfusion h2
    · exact absurd h (by norm_num [e2])

end ExamplesThree

end DPSS
