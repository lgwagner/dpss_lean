/-
# DPSS — three drones that start out of position and settle

**C2**, and gap 3 of `STATUS.md`.

`ExamplesThree.lean` builds the three-drone *steady state* and proves it cycles
with period `2/n`. What it does not do is show the system ever **reaches** that
state: every trace there starts synchronized and stays so. This file traces a
run that does not.

The start is the configuration anyone would write down first — each drone on
its own left endpoint, all heading right:

    0 →     1/3 →    2/3 →

It is *not* synchronized. Drone `0` is carried out of `[0, 1/3]` almost at
once, reaching `2/3` before it is turned around, and the team is not confined
to its own segments until time `1`. The bound is `2 − 1/3 = 5/3`, so there is
plenty of room, which is the point: `5/3` is an upper bound, not a prediction.

    t = 0     0 →     1/3 →    2/3 →
    t = 1/3   1/3 →   2/3 →    1 ←      the right drone bounces
    t = 1/2   1/2 →   5/6 ←    5/6 ←    middle and right meet, escort back
    t = 2/3   2/3     2/3      2/3      ← all three at one point
    t = 1     1/3 ←   1/3 →    1 ←      = the steady state `cfgB`

## The three-way meeting

Step 3 is the configuration the two-drone traces cannot produce and that
`STATUS.md` asked for by name: **all three drones at the same point at the same
instant**, at `2/3`. It is also where the paper's nondeterminism is visible.
The middle drone is simultaneously
* co-located with drone `0`, which is still heading right — a *meet*; and
* on the boundary `2/3` it shares with drone `2` — a *separation*.

The paper leaves open which neighbour the middle drone escorts. `newDir` gives
separation priority, so here it turns left and takes drone `0` with it. That is
one resolution of a genuine choice, and `STATUS.md` gap 5 records it as such.
The trace below is therefore a trace of *this* model, and a different
resolution would give a different — also valid — run.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2, and `ExamplesThree.lean` for the steady
state this run falls into.
-/

import Dpss.Sharpness

set_option linter.style.header false

namespace DPSS

namespace ExamplesThree

open Config

/-! ## The four configurations before the steady state -/

/-- Each drone on its own left endpoint, all heading right. -/
noncomputable def cfgS : Config 3 where
  time := 0
  pos := fun i => if i.val = 0 then 0 else if i.val = 1 then 1 / 3 else 2 / 3
  dir := fun _ => Dir.right

/-- The right drone has reached the far border and is about to turn. -/
noncomputable def cfgS1 (t : ℝ) : Config 3 where
  time := t
  pos := fun i => if i.val = 0 then 1 / 3 else if i.val = 1 then 2 / 3 else 1
  dir := fun i => if i.val = 2 then Dir.left else Dir.right

/-- Middle and right drones have met at `5/6`, beyond the boundary they share,
and escort back towards it. The left drone is still heading out, already past
its own right endpoint. -/
noncomputable def cfgS2 (t : ℝ) : Config 3 where
  time := t
  pos := fun i => if i.val = 0 then 1 / 2 else 5 / 6
  dir := fun i => if i.val = 0 then Dir.right else Dir.left

/-- **All three drones at one point.** The middle drone is on the boundary it
shares with the right drone, so it separates from that one — and the left drone,
meeting it here, is sent left as well. -/
noncomputable def cfgS3 (t : ℝ) : Config 3 where
  time := t
  pos := fun _ => 2 / 3
  dir := fun i => if i.val = 2 then Dir.right else Dir.left

@[simp] theorem cfgS_pos_e0 : cfgS.pos e0 = 0 := rfl
@[simp] theorem cfgS_pos_e1 : cfgS.pos e1 = 1 / 3 := rfl
@[simp] theorem cfgS_pos_e2 : cfgS.pos e2 = 2 / 3 := rfl
@[simp] theorem cfgS_dir (i : Fin 3) : cfgS.dir i = Dir.right := rfl
@[simp] theorem cfgS_time : cfgS.time = 0 := rfl

@[simp] theorem cfgS1_pos_e0 (t : ℝ) : (cfgS1 t).pos e0 = 1 / 3 := rfl
@[simp] theorem cfgS1_pos_e1 (t : ℝ) : (cfgS1 t).pos e1 = 2 / 3 := rfl
@[simp] theorem cfgS1_pos_e2 (t : ℝ) : (cfgS1 t).pos e2 = 1 := rfl
@[simp] theorem cfgS1_dir_e0 (t : ℝ) : (cfgS1 t).dir e0 = Dir.right := rfl
@[simp] theorem cfgS1_dir_e1 (t : ℝ) : (cfgS1 t).dir e1 = Dir.right := rfl
@[simp] theorem cfgS1_dir_e2 (t : ℝ) : (cfgS1 t).dir e2 = Dir.left := rfl

@[simp] theorem cfgS2_pos_e0 (t : ℝ) : (cfgS2 t).pos e0 = 1 / 2 := rfl
@[simp] theorem cfgS2_pos_e1 (t : ℝ) : (cfgS2 t).pos e1 = 5 / 6 := rfl
@[simp] theorem cfgS2_pos_e2 (t : ℝ) : (cfgS2 t).pos e2 = 5 / 6 := rfl
@[simp] theorem cfgS2_dir_e0 (t : ℝ) : (cfgS2 t).dir e0 = Dir.right := rfl
@[simp] theorem cfgS2_dir_e1 (t : ℝ) : (cfgS2 t).dir e1 = Dir.left := rfl
@[simp] theorem cfgS2_dir_e2 (t : ℝ) : (cfgS2 t).dir e2 = Dir.left := rfl

@[simp] theorem cfgS3_pos (t : ℝ) (i : Fin 3) : (cfgS3 t).pos i = 2 / 3 := rfl
@[simp] theorem cfgS3_dir_e0 (t : ℝ) : (cfgS3 t).dir e0 = Dir.left := rfl
@[simp] theorem cfgS3_dir_e1 (t : ℝ) : (cfgS3 t).dir e1 = Dir.left := rfl
@[simp] theorem cfgS3_dir_e2 (t : ℝ) : (cfgS3 t).dir e2 = Dir.right := rfl

/-! ## The start is legitimate -/

theorem cfgS_invariant : cfgS.Invariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases fin3_cases i with h | h | h <;> subst h
    · exact ⟨by rw [cfgS_pos_e0], by rw [cfgS_pos_e0]; norm_num⟩
    · exact ⟨by rw [cfgS_pos_e1]; norm_num, by rw [cfgS_pos_e1]; norm_num⟩
    · exact ⟨by rw [cfgS_pos_e2]; norm_num, by rw [cfgS_pos_e2]; norm_num⟩
  · intro i h
    rcases fin3_cases i with hi | hi | hi <;> subst hi
    · unfold gap; rw [nextIdx_e0, cfgS_pos_e0, cfgS_pos_e1]; norm_num
    · unfold gap; rw [nextIdx_e1, cfgS_pos_e1, cfgS_pos_e2]; norm_num
    · exact absurd h (by norm_num [e2])
  · intro i h he
    exfalso
    rcases fin3_cases i with hi | hi | hi <;> subst hi
    · have hg : cfgS.gap e0 h = 0 := he.1
      unfold gap at hg
      rw [nextIdx_e0, cfgS_pos_e0, cfgS_pos_e1] at hg
      norm_num at hg
    · have hg : cfgS.gap e1 h = 0 := he.1
      unfold gap at hg
      rw [nextIdx_e1, cfgS_pos_e1, cfgS_pos_e2] at hg
      norm_num at hg
    · exact absurd h (by norm_num [e2])

theorem cfgS_apartOnBoundaries : cfgS.ApartOnBoundaries :=
  apartOnBoundaries_of_dir_const (fun _ => rfl)

/-! ## Step 0: the right drone runs for the border -/

theorem cfgS_timeToNext : cfgS.timeToNextEvent hn3 = 1 / 3 := by
  have hA0 : ¬ cfgS.Approaching e0 h01 := by
    rintro ⟨-, h2⟩; rw [nextIdx_e0, cfgS_dir] at h2; exact Dir.noConfusion h2
  have hE0 : ¬ cfgS.Escorting e0 h01 := by
    rintro ⟨hg, -⟩
    unfold CoLocated gap at hg
    rw [nextIdx_e0, cfgS_pos_e0, cfgS_pos_e1] at hg; norm_num at hg
  have hA1 : ¬ cfgS.Approaching e1 h12 := by
    rintro ⟨-, h2⟩; rw [nextIdx_e1, cfgS_dir] at h2; exact Dir.noConfusion h2
  have hE1 : ¬ cfgS.Escorting e1 h12 := by
    rintro ⟨hg, -⟩
    unfold CoLocated gap at hg
    rw [nextIdx_e1, cfgS_pos_e1, cfgS_pos_e2] at hg; norm_num at hg
  rw [timeToNextEvent_three, droneNextTime_e2,
      droneNextTime_apart _ h01 hA0 hE0, droneNextTime_apart _ h12 hA1 hE1,
      borderTime_of_right (cfgS_dir e0), borderTime_of_right (cfgS_dir e1),
      borderTime_of_right (cfgS_dir e2), cfgS_pos_e0, cfgS_pos_e1, cfgS_pos_e2]
  norm_num

theorem step_cfgS : cfgS.step hn3 = cfgS1 (1 / 3) := by
  have hdt := cfgS_timeToNext
  set c' := cfgS.advance (1 / 3) with hc'
  have hp0 : c'.pos e0 = 1 / 3 := by
    simp only [hc', advance_pos, cfgS_pos_e0, cfgS_dir, Dir.sign_right]; norm_num
  have hp1 : c'.pos e1 = 2 / 3 := by
    simp only [hc', advance_pos, cfgS_pos_e1, cfgS_dir, Dir.sign_right]; norm_num
  have hp2 : c'.pos e2 = 1 := by
    simp only [hc', advance_pos, cfgS_pos_e2, cfgS_dir, Dir.sign_right]; norm_num
  have hnco01 : ¬ c'.CoLocated e0 h01 := by
    unfold CoLocated gap; rw [nextIdx_e0, hp0, hp1]; norm_num
  have hnco12 : ¬ c'.CoLocated e1 h12 := by
    unfold CoLocated gap; rw [nextIdx_e1, hp1, hp2]; norm_num
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt, cfgS_time]; norm_num [cfgS1]
  · rcases fin3_cases i with h | h | h <;> subst h
    · simp only [step_pos, hdt, cfgS_pos_e0, cfgS_dir, Dir.sign_right,
        cfgS1_pos_e0]; norm_num
    · simp only [step_pos, hdt, cfgS_pos_e1, cfgS_dir, Dir.sign_right,
        cfgS1_pos_e1]; norm_num
    · simp only [step_pos, hdt, cfgS_pos_e2, cfgS_dir, Dir.sign_right,
        cfgS1_pos_e2]; norm_num
  · rcases fin3_cases i with h | h | h <;> subst h
    · rw [step_dir, hdt, cfgS1_dir_e0]
      refine Eq.trans (newDir_of_noEvent ?_ ?_ ?_ (not_sepLeft_e0 _) ?_
        (not_meetLeft_e0 _)) ?_
      · rintro ⟨hq, -⟩; rw [hp0] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp0] at hq; norm_num at hq
      · rintro ⟨_hh, hs⟩; exact hnco01 hs.1
      · rintro ⟨_hh, hs, _ha⟩; exact hnco01 hs
      · simp only [hc', advance_newDir_dir, cfgS_dir]
    · rw [step_dir, hdt, cfgS1_dir_e1]
      refine Eq.trans (newDir_of_noEvent ?_ ?_ ?_ ?_ ?_ ?_) ?_
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
      · rintro ⟨_hh, hs⟩; exact hnco12 hs.1
      · rintro ⟨_hh, hs⟩; exact hnco01 hs.1
      · rintro ⟨_hh, hs, _ha⟩; exact hnco12 hs
      · rintro ⟨_hh, hs, _ha⟩; exact hnco01 hs
      · simp only [hc', advance_newDir_dir, cfgS_dir]
    · rw [step_dir, hdt, cfgS1_dir_e2]
      apply newDir_atRightBorder
      · rintro ⟨hq, -⟩; rw [hp2] at hq; norm_num at hq
      · exact ⟨hp2, by simp only [hc', advance_newDir_dir, cfgS_dir]⟩

/-! ## Step 1: the middle and right drones meet beyond their boundary -/

theorem cfgS1_timeToNext (t : ℝ) : (cfgS1 t).timeToNextEvent hn3 = 1 / 6 := by
  have hA0 : ¬ (cfgS1 t).Approaching e0 h01 := by
    rintro ⟨-, h2⟩; rw [nextIdx_e0, cfgS1_dir_e1] at h2; exact Dir.noConfusion h2
  have hE0 : ¬ (cfgS1 t).Escorting e0 h01 := by
    rintro ⟨hg, -⟩
    unfold CoLocated gap at hg
    rw [nextIdx_e0, cfgS1_pos_e0, cfgS1_pos_e1] at hg; norm_num at hg
  have hA1 : (cfgS1 t).Approaching e1 h12 := by
    refine ⟨cfgS1_dir_e1 t, ?_⟩
    rw [nextIdx_e1]; exact cfgS1_dir_e2 t
  have hgap1 : (cfgS1 t).gap e1 h12 = 1 / 3 := by
    unfold gap; rw [nextIdx_e1, cfgS1_pos_e1, cfgS1_pos_e2]; norm_num
  rw [timeToNextEvent_three, droneNextTime_e2,
      droneNextTime_apart _ h01 hA0 hE0, droneNextTime_approaching _ h12 hA1,
      borderTime_of_right (cfgS1_dir_e0 t), borderTime_of_right (cfgS1_dir_e1 t),
      borderTime_of_left (cfgS1_dir_e2 t)]
  unfold meetTime
  rw [hgap1, cfgS1_pos_e0, cfgS1_pos_e1, cfgS1_pos_e2]
  norm_num

theorem step_cfgS1 (t : ℝ) : (cfgS1 t).step hn3 = cfgS2 (t + 1 / 6) := by
  have hdt := cfgS1_timeToNext t
  set c' := (cfgS1 t).advance (1 / 6) with hc'
  have hp0 : c'.pos e0 = 1 / 2 := by
    simp only [hc', advance_pos, cfgS1_pos_e0, cfgS1_dir_e0, Dir.sign_right]
    norm_num
  have hp1 : c'.pos e1 = 5 / 6 := by
    simp only [hc', advance_pos, cfgS1_pos_e1, cfgS1_dir_e1, Dir.sign_right]
    norm_num
  have hp2 : c'.pos e2 = 5 / 6 := by
    simp only [hc', advance_pos, cfgS1_pos_e2, cfgS1_dir_e2, Dir.sign_left]
    norm_num
  have hnco01 : ¬ c'.CoLocated e0 h01 := by
    unfold CoLocated gap; rw [nextIdx_e0, hp0, hp1]; norm_num
  have hco12 : c'.CoLocated e1 h12 := by
    unfold CoLocated gap; rw [nextIdx_e1, hp1, hp2]; norm_num
  have hA12 : c'.Approaching e1 h12 := by
    refine ⟨by simp only [hc', advance_newDir_dir, cfgS1_dir_e1], ?_⟩
    rw [nextIdx_e1]
    simp only [hc', advance_newDir_dir, cfgS1_dir_e2]
  have hnsep12 : ¬ c'.AtSeparation e1 h12 := by
    rintro ⟨-, hq⟩; rw [hp1, commonEnd_e1] at hq; norm_num at hq
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt]; rfl
  · rcases fin3_cases i with h | h | h <;> subst h
    · simp only [step_pos, hdt, cfgS1_pos_e0, cfgS1_dir_e0, Dir.sign_right,
        cfgS2_pos_e0]; norm_num
    · simp only [step_pos, hdt, cfgS1_pos_e1, cfgS1_dir_e1, Dir.sign_right,
        cfgS2_pos_e1]; norm_num
    · simp only [step_pos, hdt, cfgS1_pos_e2, cfgS1_dir_e2, Dir.sign_left,
        cfgS2_pos_e2]; norm_num
  · rcases fin3_cases i with h | h | h <;> subst h
    · rw [step_dir, hdt, cfgS2_dir_e0]
      refine Eq.trans (newDir_of_noEvent ?_ ?_ ?_ (not_sepLeft_e0 _) ?_
        (not_meetLeft_e0 _)) ?_
      · rintro ⟨hq, -⟩; rw [hp0] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp0] at hq; norm_num at hq
      · rintro ⟨_hh, hs⟩; exact hnco01 hs.1
      · rintro ⟨_hh, hs, _ha⟩; exact hnco01 hs
      · simp only [hc', advance_newDir_dir, cfgS1_dir_e0]
    · -- the middle drone meets its right neighbour beyond their boundary
      rw [step_dir, hdt, cfgS2_dir_e1]
      unfold newDir
      rw [if_neg, if_neg, if_neg, if_neg, if_pos ⟨h12, hco12, hA12⟩]
      · unfold escortDir
        rw [if_neg]
        rw [hp1, commonEnd_e1]; norm_num
      · rintro ⟨_hh, hs⟩; exact hnco01 hs.1
      · rintro ⟨_hh, hs⟩; exact hnsep12 hs
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
    · -- and the right drone meets its left neighbour
      rw [step_dir, hdt, cfgS2_dir_e2]
      unfold newDir
      rw [if_neg, if_neg, if_neg (not_sepRight_e2 _), if_neg,
          if_neg (not_meetRight_e2 _), if_pos ⟨by norm_num [e2], hco12, hA12⟩]
      · unfold escortDirLeft
        rw [if_neg]
        rw [hp2, leftEnd_e2]; norm_num
      · rintro ⟨_hh, hs⟩; exact hnsep12 hs
      · rintro ⟨hq, -⟩; rw [hp2] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp2] at hq; norm_num at hq

/-! ## Step 2: all three drones arrive at one point -/

theorem cfgS2_timeToNext (t : ℝ) : (cfgS2 t).timeToNextEvent hn3 = 1 / 6 := by
  have hA0 : (cfgS2 t).Approaching e0 h01 := by
    refine ⟨cfgS2_dir_e0 t, ?_⟩
    rw [nextIdx_e0]; exact cfgS2_dir_e1 t
  have hgap0 : (cfgS2 t).gap e0 h01 = 1 / 3 := by
    unfold gap; rw [nextIdx_e0, cfgS2_pos_e0, cfgS2_pos_e1]; norm_num
  have hA1 : ¬ (cfgS2 t).Approaching e1 h12 := by
    rintro ⟨h1, -⟩; rw [cfgS2_dir_e1] at h1; exact Dir.noConfusion h1
  have hE1 : (cfgS2 t).Escorting e1 h12 := by
    refine ⟨?_, ?_⟩
    · unfold CoLocated gap; rw [nextIdx_e1, cfgS2_pos_e1, cfgS2_pos_e2]; norm_num
    · rw [nextIdx_e1, cfgS2_dir_e1, cfgS2_dir_e2]
  have hd1 : (cfgS2 t).droneNextTime e1
      = min ((cfgS2 t).borderTime e1) ((cfgS2 t).separationTime e1) := by
    unfold droneNextTime
    rw [dif_pos h12, if_neg hA1, if_pos hE1]
  rw [timeToNextEvent_three, droneNextTime_e2,
      droneNextTime_approaching _ h01 hA0, hd1,
      borderTime_of_right (cfgS2_dir_e0 t), borderTime_of_left (cfgS2_dir_e1 t),
      borderTime_of_left (cfgS2_dir_e2 t)]
  unfold meetTime separationTime
  rw [hgap0, cfgS2_pos_e0, cfgS2_pos_e1, cfgS2_pos_e2, cfgS2_dir_e1,
    Dir.sign_left, commonEnd_e1]
  norm_num

theorem step_cfgS2 (t : ℝ) : (cfgS2 t).step hn3 = cfgS3 (t + 1 / 6) := by
  have hdt := cfgS2_timeToNext t
  set c' := (cfgS2 t).advance (1 / 6) with hc'
  have hp : ∀ i, c'.pos i = 2 / 3 := by
    intro i
    rcases fin3_cases i with h | h | h <;> subst h
    · simp only [hc', advance_pos, cfgS2_pos_e0, cfgS2_dir_e0, Dir.sign_right]
      norm_num
    · simp only [hc', advance_pos, cfgS2_pos_e1, cfgS2_dir_e1, Dir.sign_left]
      norm_num
    · simp only [hc', advance_pos, cfgS2_pos_e2, cfgS2_dir_e2, Dir.sign_left]
      norm_num
  have hco01 : c'.CoLocated e0 h01 := by
    unfold CoLocated gap; rw [nextIdx_e0, hp e0, hp e1]; norm_num
  have hA01 : c'.Approaching e0 h01 := by
    refine ⟨by simp only [hc', advance_newDir_dir, cfgS2_dir_e0], ?_⟩
    rw [nextIdx_e0]
    simp only [hc', advance_newDir_dir, cfgS2_dir_e1]
  have hnsep01 : ¬ c'.AtSeparation e0 h01 := by
    rintro ⟨-, hq⟩; rw [hp e0, commonEnd_e0] at hq; norm_num at hq
  have hsep12 : c'.AtSeparation e1 h12 := by
    refine ⟨?_, ?_⟩
    · unfold CoLocated gap; rw [nextIdx_e1, hp e1, hp e2]; norm_num
    · rw [hp e1, commonEnd_e1]
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt]; rfl
  · rcases fin3_cases i with h | h | h <;> subst h
    · simp only [step_pos, hdt, cfgS2_pos_e0, cfgS2_dir_e0, Dir.sign_right,
        cfgS3_pos]; norm_num
    · simp only [step_pos, hdt, cfgS2_pos_e1, cfgS2_dir_e1, Dir.sign_left,
        cfgS3_pos]; norm_num
    · simp only [step_pos, hdt, cfgS2_pos_e2, cfgS2_dir_e2, Dir.sign_left,
        cfgS3_pos]; norm_num
  · rcases fin3_cases i with h | h | h <;> subst h
    · -- the left drone meets the middle one, beyond *their* boundary
      rw [step_dir, hdt, cfgS3_dir_e0]
      unfold newDir
      rw [if_neg, if_neg, if_neg, if_neg (not_sepLeft_e0 _),
        if_pos ⟨h01, hco01, hA01⟩]
      · unfold escortDir
        rw [if_neg]
        rw [hp e0, commonEnd_e0]; norm_num
      · rintro ⟨_hh, hs⟩; exact hnsep01 hs
      · rintro ⟨hq, -⟩; rw [hp e0] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp e0] at hq; norm_num at hq
    · -- the middle drone is on the boundary it shares with the right one, and
      -- separation takes priority over the meet
      rw [step_dir, hdt, cfgS3_dir_e1]
      unfold newDir
      rw [if_neg, if_neg, if_pos ⟨h12, hsep12⟩]
      · rintro ⟨hq, -⟩; rw [hp e1] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp e1] at hq; norm_num at hq
    · rw [step_dir, hdt, cfgS3_dir_e2]
      unfold newDir
      rw [if_neg, if_neg, if_neg (not_sepRight_e2 _),
          if_pos ⟨by norm_num [e2], hsep12⟩]
      · rintro ⟨hq, -⟩; rw [hp e2] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp e2] at hq; norm_num at hq

/-! ## Step 3: the team reaches its steady state -/

theorem cfgS3_timeToNext (t : ℝ) : (cfgS3 t).timeToNextEvent hn3 = 1 / 3 := by
  have hA0 : ¬ (cfgS3 t).Approaching e0 h01 := by
    rintro ⟨h1, -⟩; rw [cfgS3_dir_e0] at h1; exact Dir.noConfusion h1
  have hE0 : (cfgS3 t).Escorting e0 h01 := by
    refine ⟨?_, ?_⟩
    · unfold CoLocated gap; rw [nextIdx_e0, cfgS3_pos, cfgS3_pos]; norm_num
    · rw [nextIdx_e0, cfgS3_dir_e0, cfgS3_dir_e1]
  have hd0 : (cfgS3 t).droneNextTime e0
      = min ((cfgS3 t).borderTime e0) ((cfgS3 t).separationTime e0) := by
    unfold droneNextTime
    rw [dif_pos h01, if_neg hA0, if_pos hE0]
  have hA1 : ¬ (cfgS3 t).Approaching e1 h12 := by
    rintro ⟨h1, -⟩; rw [cfgS3_dir_e1] at h1; exact Dir.noConfusion h1
  have hE1 : ¬ (cfgS3 t).Escorting e1 h12 := by
    rintro ⟨-, h2⟩
    rw [nextIdx_e1, cfgS3_dir_e1, cfgS3_dir_e2] at h2
    exact Dir.noConfusion h2
  rw [timeToNextEvent_three, droneNextTime_e2, hd0,
      droneNextTime_apart _ h12 hA1 hE1,
      borderTime_of_left (cfgS3_dir_e0 t), borderTime_of_left (cfgS3_dir_e1 t),
      borderTime_of_right (cfgS3_dir_e2 t)]
  unfold separationTime
  rw [cfgS3_pos, cfgS3_pos, cfgS3_pos, cfgS3_dir_e0, Dir.sign_left, commonEnd_e0]
  norm_num

theorem step_cfgS3 (t : ℝ) : (cfgS3 t).step hn3 = cfgB (t + 1 / 3) := by
  have hdt := cfgS3_timeToNext t
  set c' := (cfgS3 t).advance (1 / 3) with hc'
  have hp0 : c'.pos e0 = 1 / 3 := by
    simp only [hc', advance_pos, cfgS3_pos, cfgS3_dir_e0, Dir.sign_left]; norm_num
  have hp1 : c'.pos e1 = 1 / 3 := by
    simp only [hc', advance_pos, cfgS3_pos, cfgS3_dir_e1, Dir.sign_left]; norm_num
  have hp2 : c'.pos e2 = 1 := by
    simp only [hc', advance_pos, cfgS3_pos, cfgS3_dir_e2, Dir.sign_right]; norm_num
  have hsep01 : c'.AtSeparation e0 h01 := by
    refine ⟨?_, ?_⟩
    · unfold CoLocated gap; rw [nextIdx_e0, hp0, hp1]; norm_num
    · rw [hp0, commonEnd_e0]
  have hnsep12 : ¬ c'.AtSeparation e1 h12 := by
    rintro ⟨hco, -⟩
    unfold CoLocated gap at hco
    rw [nextIdx_e1, hp1, hp2] at hco; norm_num at hco
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt]; rfl
  · rcases fin3_cases i with h | h | h <;> subst h
    · simp only [step_pos, hdt, cfgS3_pos, cfgS3_dir_e0, Dir.sign_left,
        cfgB_pos_e0]; norm_num
    · simp only [step_pos, hdt, cfgS3_pos, cfgS3_dir_e1, Dir.sign_left,
        cfgB_pos_e1]; norm_num
    · simp only [step_pos, hdt, cfgS3_pos, cfgS3_dir_e2, Dir.sign_right,
        cfgB_pos_e2]; norm_num
  · rcases fin3_cases i with h | h | h <;> subst h
    · rw [step_dir, hdt, cfgB_dir_e0]
      unfold newDir
      rw [if_neg, if_neg, if_pos ⟨h01, hsep01⟩]
      · rintro ⟨hq, -⟩; rw [hp0] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp0] at hq; norm_num at hq
    · rw [step_dir, hdt, cfgB_dir_e1]
      unfold newDir
      rw [if_neg, if_neg, if_neg, if_pos ⟨by norm_num [e1], hsep01⟩]
      · rintro ⟨_hh, hs⟩; exact hnsep12 hs
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
      · rintro ⟨hq, -⟩; rw [hp1] at hq; norm_num at hq
    · rw [step_dir, hdt, cfgB_dir_e2]
      apply newDir_atRightBorder
      · rintro ⟨hq, -⟩; rw [hp2] at hq; norm_num at hq
      · exact ⟨hp2, by simp only [hc', advance_newDir_dir, cfgS3_dir_e2]⟩

/-! ## The run, end to end -/

theorem run_cfgS_1 : cfgS.run hn3 1 = cfgS1 (1 / 3) := by
  rw [show cfgS.run hn3 1 = cfgS.step hn3 from rfl, step_cfgS]

theorem run_cfgS_2 : cfgS.run hn3 2 = cfgS2 (1 / 2) := by
  rw [show cfgS.run hn3 2 = (cfgS.run hn3 1).step hn3 from rfl, run_cfgS_1,
    step_cfgS1]
  norm_num

theorem run_cfgS_3 : cfgS.run hn3 3 = cfgS3 (2 / 3) := by
  rw [show cfgS.run hn3 3 = (cfgS.run hn3 2).step hn3 from rfl, run_cfgS_2,
    step_cfgS2]
  norm_num

theorem run_cfgS_4 : cfgS.run hn3 4 = cfgB 1 := by
  rw [show cfgS.run hn3 4 = (cfgS.run hn3 3).step hn3 from rfl, run_cfgS_3,
    step_cfgS3]
  norm_num

/-- **The three-way meeting, stated.** At step 3 — time `2/3` — all three
drones occupy the same point. -/
theorem cfgS_three_way_meeting :
    (cfgS.run hn3 3).time = 2 / 3 ∧
      (cfgS.run hn3 3).pos e0 = 2 / 3 ∧
      (cfgS.run hn3 3).pos e1 = 2 / 3 ∧
      (cfgS.run hn3 3).pos e2 = 2 / 3 := by
  rw [run_cfgS_3]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The run really does start out of position.** At step 2 the left drone is
at `1/2`, well outside its own interval `[0, 1/3]`. -/
theorem cfgS_not_sync_at_start : ¬ AllSync cfgS hn3 0 := by
  intro hs
  have h := (hs e0).2 2 (by omega)
  rw [run_cfgS_2, cfgS2_pos_e0, rightEnd_e0] at h
  norm_num at h

/-! ## The steady state, from any starting time

`ExamplesThree.lean` proves the cycle for `cfgB 0`. The steps are already
stated for an arbitrary clock, so the same induction gives it from any. -/

theorem run_cfgB_at (t : ℝ) (m : ℕ) :
    (cfgB t).run hn3 (2 * m) = cfgB (t + 2 * (m : ℝ) / 3) ∧
    (cfgB t).run hn3 (2 * m + 1) = cfgC (t + 2 * (m : ℝ) / 3 + 1 / 3) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * 0 = 0 from rfl, run_zero]; norm_num
    · rw [show 2 * 0 + 1 = 1 from rfl,
        show (cfgB t).run hn3 1 = (cfgB t).step hn3 from rfl, step_cfgB]
      norm_num
  | succ m ih =>
    obtain ⟨-, h2⟩ := ih
    have e1' : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have heven : (cfgB t).run hn3 (2 * (m + 1)) = cfgB (t + 2 * ((m : ℝ) + 1) / 3) := by
      rw [e1', run_succ, h2, step_cfgC]
      congr 1
      ring
    refine ⟨by rw [hcast]; exact heven, ?_⟩
    rw [show 2 * (m + 1) + 1 = (2 * (m + 1)) + 1 from rfl, run_succ, heven,
      step_cfgB, hcast]

/-- Every drone is inside its own interval from step 4 on, for ever. -/
theorem cfgS_in_intervals (j : ℕ) (hj : 4 ≤ j) (i : Fin 3) :
    leftEnd i ≤ (cfgS.run hn3 j).pos i ∧ (cfgS.run hn3 j).pos i ≤ rightEnd i := by
  obtain ⟨q, rfl⟩ : ∃ q, j = 4 + q := ⟨j - 4, by omega⟩
  rw [run_add, run_cfgS_4]
  obtain ⟨m, hm⟩ : ∃ m, q = 2 * m ∨ q = 2 * m + 1 := ⟨q / 2, by omega⟩
  rcases hm with hm | hm <;> subst hm
  · rw [(run_cfgB_at 1 m).1]
    rcases fin3_cases i with h | h | h <;> subst h
    · rw [leftEnd_e0, rightEnd_e0, cfgB_pos_e0]; norm_num
    · rw [leftEnd_e1, rightEnd_e1, cfgB_pos_e1]; norm_num
    · rw [leftEnd_e2, rightEnd_e2, cfgB_pos_e2]; norm_num
  · rw [(run_cfgB_at 1 m).2]
    rcases fin3_cases i with h | h | h <;> subst h
    · rw [leftEnd_e0, rightEnd_e0, cfgC_pos_e0]; norm_num
    · rw [leftEnd_e1, rightEnd_e1, cfgC_pos_e1]; norm_num
    · rw [leftEnd_e2, rightEnd_e2, cfgC_pos_e2]; norm_num

/-- **The team settles at time 1** — and stays settled. -/
theorem cfgS_allSync : AllSync cfgS hn3 4 :=
  fun i => ⟨fun j hj => (cfgS_in_intervals j hj i).1,
    fun j hj => (cfgS_in_intervals j hj i).2⟩

/-- **Checked against the bound.** Theorem 2.1 promises synchronization by
`2 - 1/3 = 5/3`; this run is settled at `1`, comfortably inside. -/
theorem cfgS_within_bound :
    (cfgS.run hn3 4).time = 1 ∧ (1 : ℝ) ≤ 2 - 1 / (3 : ℝ) := by
  refine ⟨by rw [run_cfgS_4]; rfl, by norm_num⟩

/-- Theorem 2.1 for this configuration, **from the general theorem** rather
than from the trace. -/
theorem cfgS_converges : ConvergesBy cfgS hn3 :=
  convergesBy hn3 cfgS_invariant cfgS_apartOnBoundaries

end ExamplesThree

end DPSS
