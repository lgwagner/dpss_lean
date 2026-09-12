/-
# DPSS — concrete configurations

Everything else in this development is universally quantified. Nothing forces
the definitions to be *satisfiable*, and a formalization whose hypotheses can
never be met proves a great deal about nothing at all.

This file exhibits actual configurations and proves actual facts about them.

## The bounce regression test

`bounce` below is two drones meeting exactly on the boundary they share — the
paper's **bounce**, a meet and a separation occurring at the same instant.

This example found a real bug. `AtSeparation` originally required the pair to
be *escorting*, meaning co-located **and heading the same way**. But two drones
converging on their shared boundary have *opposite* headings right up to the
instant they meet, so no separation fired, the meet branch took over, and the
right-hand drone was sent **left — out of its own interval**, permanently
breaking the property the whole development is trying to prove.

The theorems below pin down the correct behaviour: the left drone turns left,
the right drone turns right, each going back to its own side.

This is exactly what gap 4 of `STATUS.md` warned about, and it is why working a
concrete case matters more than another layer of general theory.
-/

import Dpss.Coherence

set_option linter.style.header false

namespace DPSS

namespace Examples

open Config

/-- The left-hand drone of a two-drone team. -/
def d0 : Fin 2 := ⟨0, by norm_num⟩

/-- The right-hand drone. -/
def d1 : Fin 2 := ⟨1, by norm_num⟩

theorem d0_next : nextIdx d0 (by norm_num [d0]) = d1 := by
  apply Fin.ext; rfl

theorem commonEnd_d0 : commonEnd d0 = 1 / 2 := by
  unfold commonEnd rightEnd d0; norm_num

theorem leftEnd_d1 : leftEnd d1 = 1 / 2 := by
  unfold leftEnd d1; norm_num

/-! ## A bounce -/

/-- Two drones meeting exactly on their shared boundary, heading into each
other. The left one is travelling right, the right one left. -/
noncomputable def bounce : Config 2 where
  time := 0
  pos := fun _ => 1 / 2
  dir := fun i => if i.val = 0 then Dir.right else Dir.left

@[simp] theorem bounce_pos (i : Fin 2) : bounce.pos i = 1 / 2 := rfl
@[simp] theorem bounce_dir_d0 : bounce.dir d0 = Dir.right := rfl
@[simp] theorem bounce_dir_d1 : bounce.dir d1 = Dir.left := rfl

theorem bounce_h : d0.val + 1 < 2 := by norm_num [d0]

/-- The pair really is co-located. -/
theorem bounce_coLocated : bounce.CoLocated d0 bounce_h := by
  unfold CoLocated gap
  rw [d0_next]
  simp

/-- And really is sitting on the boundary it shares. -/
theorem bounce_atSeparation : bounce.AtSeparation d0 bounce_h :=
  ⟨bounce_coLocated, by rw [commonEnd_d0]; simp⟩

/-- They are genuinely approaching each other, so this is a meet as well as a
separation — which is precisely what makes it a bounce rather than an ordinary
separation. -/
theorem bounce_approaching : bounce.Approaching d0 bounce_h := by
  refine ⟨rfl, ?_⟩
  rw [d0_next]
  rfl

/-- **Regression test, left drone.** It turns left, back into `[0, 1/2]`. -/
theorem bounce_newDir_d0 : bounce.newDir d0 = Dir.left := by
  unfold newDir
  rw [if_neg, if_neg, if_pos]
  · exact ⟨bounce_h, bounce_atSeparation⟩
  · rintro ⟨hp, -⟩; rw [bounce_pos] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [bounce_pos] at hp; norm_num at hp

/-- **Regression test, right drone.** It turns right, back into `[1/2, 1]`.

Before the fix this returned `Dir.left`: the drone was driven out of its own
interval and could never be synchronized again. -/
theorem bounce_newDir_d1 : bounce.newDir d1 = Dir.right := by
  unfold newDir
  rw [if_neg, if_neg, if_neg, if_pos]
  · exact ⟨by norm_num [d1], bounce_atSeparation⟩
  · rintro ⟨h, -⟩
    exact absurd h (by norm_num [d1])
  · rintro ⟨hp, -⟩; rw [bounce_pos] at hp; norm_num at hp
  · rintro ⟨hp, -⟩; rw [bounce_pos] at hp; norm_num at hp

/-- The two drones leave the bounce heading in **opposite** directions. That is
the whole point of a separation, and it is what the bug destroyed. -/
theorem bounce_separates : bounce.newDir d0 ≠ bounce.newDir d1 := by
  rw [bounce_newDir_d0, bounce_newDir_d1]
  exact fun h => Dir.noConfusion h

/-! ## The invariant is satisfiable

A cheaper but equally necessary check: the standing invariant of a run is not
vacuous. -/

/-- Two drones approaching each other from inside their own intervals. -/
noncomputable def approach : Config 2 where
  time := 0
  pos := fun i => if i.val = 0 then 1 / 4 else 3 / 4
  dir := fun i => if i.val = 0 then Dir.right else Dir.left

/-- There are exactly two drones, so every index is one of them. -/
theorem fin2_cases (i : Fin 2) : i = d0 ∨ i = d1 := by
  rcases i with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

@[simp] theorem approach_pos_d0 : approach.pos d0 = 1 / 4 := rfl
@[simp] theorem approach_pos_d1 : approach.pos d1 = 3 / 4 := rfl

/-- **The standing invariant of a run is satisfiable.** Without this, every
theorem conditioned on `Invariant` would be true for the empty reason. -/
theorem approach_invariant : approach.Invariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases fin2_cases i with hi | hi <;> subst hi
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
  · intro i h
    rcases fin2_cases i with hi | hi <;> subst hi
    · unfold gap
      norm_num [approach, nextIdx, d0]
    · exact absurd h (by norm_num [d1])
  · intro i h he
    exfalso
    rcases fin2_cases i with hi | hi <;> subst hi
    · have hg : approach.gap d0 h = 0 := he.1
      unfold gap at hg
      norm_num [approach, nextIdx, d0] at hg
    · exact absurd h (by norm_num [d1])

/-! ## Computing with two drones

To trace the system we must actually evaluate `timeToNextEvent`, which is a
minimum over all drones. For two drones that is just a `min`. -/

theorem hn2 : 0 < 2 := by norm_num

/-- The team-wide deadline for two drones is the smaller of their two. -/
theorem timeToNextEvent_two (c : Config 2) :
    c.timeToNextEvent hn2 = min (c.droneNextTime d0) (c.droneNextTime d1) := by
  unfold timeToNextEvent
  apply le_antisymm
  · exact le_min (Finset.inf'_le _ (Finset.mem_univ _))
      (Finset.inf'_le _ (Finset.mem_univ _))
  · refine Finset.le_inf' _ _ (fun i _ => ?_)
    rcases fin2_cases i with h | h <;> subst h
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- The right-hand drone of a pair has no right-hand neighbour, so its only
deadline is its own border. -/
theorem droneNextTime_d1 (c : Config 2) :
    c.droneNextTime d1 = c.borderTime d1 := by
  unfold droneNextTime
  rw [dif_neg (by norm_num [d1])]

/-- The left-hand drone, when the pair is closing on each other. -/
theorem droneNextTime_d0_approaching (c : Config 2)
    (hA : c.Approaching d0 bounce_h) :
    c.droneNextTime d0 = min (c.borderTime d0) (c.meetTime d0 bounce_h) := by
  unfold droneNextTime
  rw [dif_pos bounce_h, if_pos hA]

/-- The left-hand drone, when the pair is neither closing nor escorting. -/
theorem droneNextTime_d0_apart (c : Config 2)
    (hA : ¬ c.Approaching d0 bounce_h) (hE : ¬ c.Escorting d0 bounce_h) :
    c.droneNextTime d0 = c.borderTime d0 := by
  unfold droneNextTime
  rw [dif_pos bounce_h, if_neg hA, if_neg hE]

/-! ## A complete trace

The two configurations the system settles into, and the fact that it alternates
between them forever. -/

@[simp] theorem nextIdx_d0_eq : nextIdx d0 bounce_h = d1 := rfl

/-- Just separated on the shared boundary: each drone heading back into its own
interval. -/
noncomputable def atBoundary (t : ℝ) : Config 2 where
  time := t
  pos := fun _ => 1 / 2
  dir := fun i => if i.val = 0 then Dir.left else Dir.right

/-- At the two ends of the perimeter, both turning inwards. -/
noncomputable def atEnds (t : ℝ) : Config 2 where
  time := t
  pos := fun i => if i.val = 0 then 0 else 1
  dir := fun i => if i.val = 0 then Dir.right else Dir.left

@[simp] theorem atBoundary_pos (t : ℝ) (i : Fin 2) : (atBoundary t).pos i = 1 / 2 := rfl
@[simp] theorem atBoundary_dir_d0 (t : ℝ) : (atBoundary t).dir d0 = Dir.left := rfl
@[simp] theorem atBoundary_dir_d1 (t : ℝ) : (atBoundary t).dir d1 = Dir.right := rfl
@[simp] theorem atEnds_pos_d0 (t : ℝ) : (atEnds t).pos d0 = 0 := rfl
@[simp] theorem atEnds_pos_d1 (t : ℝ) : (atEnds t).pos d1 = 1 := rfl
@[simp] theorem atEnds_dir_d0 (t : ℝ) : (atEnds t).dir d0 = Dir.right := rfl
@[simp] theorem atEnds_dir_d1 (t : ℝ) : (atEnds t).dir d1 = Dir.left := rfl

/-! ### How long until the next event -/

/-- From the boundary, the drones fly apart and each reaches its own end of the
perimeter after half a unit of time. -/
theorem atBoundary_timeToNext (t : ℝ) :
    (atBoundary t).timeToNextEvent hn2 = 1 / 2 := by
  have hA : ¬ (atBoundary t).Approaching d0 bounce_h := by
    rintro ⟨h1, -⟩
    rw [atBoundary_dir_d0] at h1
    exact Dir.noConfusion h1
  have hE : ¬ (atBoundary t).Escorting d0 bounce_h := by
    rintro ⟨-, h2⟩
    rw [nextIdx_d0_eq, atBoundary_dir_d0, atBoundary_dir_d1] at h2
    exact Dir.noConfusion h2
  rw [timeToNextEvent_two, droneNextTime_d1, droneNextTime_d0_apart _ hA hE,
      borderTime_of_left (atBoundary_dir_d0 t),
      borderTime_of_right (atBoundary_dir_d1 t)]
  norm_num

/-- From the two ends, the drones close on each other and meet in the middle
after half a unit of time. -/
theorem atEnds_timeToNext (t : ℝ) :
    (atEnds t).timeToNextEvent hn2 = 1 / 2 := by
  have hA : (atEnds t).Approaching d0 bounce_h := by
    refine ⟨atEnds_dir_d0 t, ?_⟩
    rw [nextIdx_d0_eq]
    exact atEnds_dir_d1 t
  have hgap : (atEnds t).gap d0 bounce_h = 1 := by
    unfold gap
    rw [nextIdx_d0_eq, atEnds_pos_d0, atEnds_pos_d1]
    norm_num
  rw [timeToNextEvent_two, droneNextTime_d1, droneNextTime_d0_approaching _ hA,
      borderTime_of_right (atEnds_dir_d0 t),
      borderTime_of_left (atEnds_dir_d1 t)]
  unfold meetTime
  rw [hgap, atEnds_pos_d0, atEnds_pos_d1]
  norm_num

/-! ### The trace

Three step equations, and then the whole future of the system. -/

/-- From the boundary the pair flies apart and arrives at the two perimeter
ends, turning inwards. -/
theorem step_atBoundary (t : ℝ) : (atBoundary t).step hn2 = atEnds (t + 1 / 2) := by
  have hdt := atBoundary_timeToNext t
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt]; rfl
  · rcases fin2_cases i with h | h <;> subst h
    · simp only [step_pos, hdt, atBoundary_pos, atBoundary_dir_d0, Dir.sign_left,
        atEnds_pos_d0]; norm_num
    · simp only [step_pos, hdt, atBoundary_pos, atBoundary_dir_d1, Dir.sign_right,
        atEnds_pos_d1]; norm_num
  · rcases fin2_cases i with h | h <;> subst h
    · rw [step_dir, hdt, atEnds_dir_d0]
      apply newDir_atLeftBorder
      refine ⟨?_, ?_⟩
      · simp only [advance_pos, atBoundary_pos, atBoundary_dir_d0, Dir.sign_left]
        norm_num
      · simp only [advance_newDir_dir, atBoundary_dir_d0]
    · rw [step_dir, hdt, atEnds_dir_d1]
      apply newDir_atRightBorder
      · rintro ⟨hp0, -⟩
        simp only [advance_pos, atBoundary_pos, atBoundary_dir_d1,
          Dir.sign_right] at hp0
        norm_num at hp0
      · refine ⟨?_, ?_⟩
        · simp only [advance_pos, atBoundary_pos, atBoundary_dir_d1, Dir.sign_right]
          norm_num
        · simp only [advance_newDir_dir, atBoundary_dir_d1]

/-- From the two ends the pair closes and bounces off each other in the middle,
returning to the boundary configuration. -/
theorem step_atEnds (t : ℝ) : (atEnds t).step hn2 = atBoundary (t + 1 / 2) := by
  have hdt := atEnds_timeToNext t
  have hpos : ((atEnds t).advance (1 / 2)).pos = bounce.pos := by
    funext i
    rcases fin2_cases i with h | h <;> subst h
    · simp only [advance_pos, atEnds_pos_d0, atEnds_dir_d0, Dir.sign_right,
        bounce_pos]; norm_num
    · simp only [advance_pos, atEnds_pos_d1, atEnds_dir_d1, Dir.sign_left,
        bounce_pos]; norm_num
  have hdir : ((atEnds t).advance (1 / 2)).dir = bounce.dir := by
    funext i
    rcases fin2_cases i with h | h <;> subst h
    · simp only [advance_newDir_dir, atEnds_dir_d0, bounce_dir_d0]
    · simp only [advance_newDir_dir, atEnds_dir_d1, bounce_dir_d1]
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt]; rfl
  · rcases fin2_cases i with h | h <;> subst h
    · simp only [step_pos, hdt, atEnds_pos_d0, atEnds_dir_d0, Dir.sign_right,
        atBoundary_pos]; norm_num
    · simp only [step_pos, hdt, atEnds_pos_d1, atEnds_dir_d1, Dir.sign_left,
        atBoundary_pos]; norm_num
  · rcases fin2_cases i with h | h <;> subst h
    · rw [step_dir, hdt, newDir_congr hpos hdir, bounce_newDir_d0,
        atBoundary_dir_d0]
    · rw [step_dir, hdt, newDir_congr hpos hdir, bounce_newDir_d1,
        atBoundary_dir_d1]

/-- The starting configuration also bounces, after a quarter unit of time. -/
theorem approach_timeToNext : approach.timeToNextEvent hn2 = 1 / 4 := by
  have hA : approach.Approaching d0 bounce_h := by
    refine ⟨rfl, ?_⟩
    rw [nextIdx_d0_eq]; rfl
  have hgap : approach.gap d0 bounce_h = 1 / 2 := by
    unfold gap
    rw [nextIdx_d0_eq, approach_pos_d0, approach_pos_d1]
    norm_num
  rw [timeToNextEvent_two, droneNextTime_d1, droneNextTime_d0_approaching _ hA,
      borderTime_of_right (by rfl : approach.dir d0 = Dir.right),
      borderTime_of_left (by rfl : approach.dir d1 = Dir.left)]
  unfold meetTime
  rw [hgap, approach_pos_d0, approach_pos_d1]
  norm_num

theorem step_approach : approach.step hn2 = atBoundary (1 / 4) := by
  have hdt := approach_timeToNext
  have hpos : (approach.advance (1 / 4)).pos = bounce.pos := by
    funext i
    rcases fin2_cases i with h | h <;> subst h
    · simp only [advance_pos, approach_pos_d0, bounce_pos]
      rw [(by rfl : approach.dir d0 = Dir.right), Dir.sign_right]; norm_num
    · simp only [advance_pos, approach_pos_d1, bounce_pos]
      rw [(by rfl : approach.dir d1 = Dir.left), Dir.sign_left]; norm_num
  have hdir : (approach.advance (1 / 4)).dir = bounce.dir := by
    funext i
    rcases fin2_cases i with h | h <;> subst h
    · simp only [advance_newDir_dir]; rfl
    · simp only [advance_newDir_dir]; rfl
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt]
    show (0 : ℝ) + 1 / 4 = 1 / 4
    norm_num
  · rcases fin2_cases i with h | h <;> subst h
    · simp only [step_pos, hdt, approach_pos_d0, atBoundary_pos]
      rw [(by rfl : approach.dir d0 = Dir.right), Dir.sign_right]; norm_num
    · simp only [step_pos, hdt, approach_pos_d1, atBoundary_pos]
      rw [(by rfl : approach.dir d1 = Dir.left), Dir.sign_left]; norm_num
  · rcases fin2_cases i with h | h <;> subst h
    · rw [step_dir, hdt, newDir_congr hpos hdir, bounce_newDir_d0,
        atBoundary_dir_d0]
    · rw [step_dir, hdt, newDir_congr hpos hdir, bounce_newDir_d1,
        atBoundary_dir_d1]

/-! ### Where the trace goes

The assigned intervals for two drones are `[0, 1/2]` and `[1/2, 1]`. -/

theorem leftEnd_d0 : leftEnd d0 = 0 := by unfold leftEnd d0; norm_num
theorem rightEnd_d0 : rightEnd d0 = 1 / 2 := by unfold rightEnd d0; norm_num
theorem rightEnd_d1 : rightEnd d1 = 1 := by unfold rightEnd d1; norm_num

/-- **The complete trace.** After an initial quarter unit of approach, the
system alternates forever between the boundary configuration and the
two-ends configuration. -/
theorem run_approach (m : ℕ) :
    approach.run hn2 (2 * m + 1) = atBoundary (1 / 4 + m) ∧
    approach.run hn2 (2 * m + 2) = atEnds (3 / 4 + m) := by
  induction m with
  | zero =>
    have h1 : approach.run hn2 1 = atBoundary (1 / 4) := by
      rw [show approach.run hn2 1 = approach.step hn2 from rfl, step_approach]
    refine ⟨?_, ?_⟩
    · rw [show 2 * 0 + 1 = 1 from rfl, h1]; norm_num
    · rw [show 2 * 0 + 2 = 2 from rfl,
        show approach.run hn2 2 = (approach.run hn2 1).step hn2 from rfl, h1,
        step_atBoundary]
      norm_num
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by ring
    have hodd : approach.run hn2 (2 * (m + 1) + 1) = atBoundary (1 / 4 + (m + 1)) := by
      rw [e1, run_succ, h2, step_atEnds]
      congr 1
      push_cast
      ring
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    refine ⟨by rw [hcast]; exact hodd, ?_⟩
    have e2 : 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 := by ring
    rw [e2, run_succ, hodd, step_atBoundary]
    congr 1
    push_cast
    ring

/-- **Every drone stays inside its own interval, forever.** -/
theorem approach_pos_bounds (j : ℕ) :
    0 ≤ (approach.run hn2 j).pos d0 ∧ (approach.run hn2 j).pos d0 ≤ 1 / 2 ∧
    1 / 2 ≤ (approach.run hn2 j).pos d1 ∧ (approach.run hn2 j).pos d1 ≤ 1 := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [run_zero]
    exact ⟨by rw [approach_pos_d0]; norm_num,
           by rw [approach_pos_d0]; norm_num,
           by rw [approach_pos_d1]; norm_num,
           by rw [approach_pos_d1]; norm_num⟩
  · obtain ⟨m, hm⟩ : ∃ m, j = 2 * m + 1 ∨ j = 2 * m + 2 := ⟨(j - 1) / 2, by omega⟩
    rcases hm with hm | hm <;> subst hm
    · rw [(run_approach m).1]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [atBoundary_pos] <;> norm_num
    · rw [(run_approach m).2]
      exact ⟨by rw [atEnds_pos_d0], by rw [atEnds_pos_d0]; norm_num,
             by rw [atEnds_pos_d1]; norm_num, by rw [atEnds_pos_d1]⟩

/-- **This team is synchronized from the very start.**

The first end-to-end result about a running DPSS system in this development:
not a property of one step, but of the entire infinite future. -/
theorem approach_allSync : AllSync approach hn2 0 := by
  intro i
  constructor
  · intro j _
    rcases fin2_cases i with h | h <;> subst h
    · rw [leftEnd_d0]; exact (approach_pos_bounds j).1
    · rw [leftEnd_d1]; exact (approach_pos_bounds j).2.2.1
  · intro j _
    rcases fin2_cases i with h | h <;> subst h
    · rw [rightEnd_d0]; exact (approach_pos_bounds j).2.1
    · rw [rightEnd_d1]; exact (approach_pos_bounds j).2.2.2

/-- **Theorem 2.1 holds for this configuration**, and comfortably: the bound
for `n = 2` is `2 - 1/2 = 3/2`, and this team is already synchronized at time
zero. -/
theorem approach_converges : ConvergesBy approach hn2 := by
  intro i j _
  rcases fin2_cases i with h | h <;> subst h
  · exact ⟨by rw [leftEnd_d0]; exact (approach_pos_bounds j).1,
           by rw [rightEnd_d0]; exact (approach_pos_bounds j).2.1⟩
  · exact ⟨by rw [leftEnd_d1]; exact (approach_pos_bounds j).2.2.1,
           by rw [rightEnd_d1]; exact (approach_pos_bounds j).2.2.2⟩

/-- **The steady state is periodic with period 1 in time.**

The paper states the steady-state period as `2/n`, which at `n = 2` is exactly
1. The positions repeat and the clock has advanced by one unit — an independent
check of the model against a number the paper gives. -/
theorem approach_period (m : ℕ) :
    (approach.run hn2 (2 * (m + 1) + 1)).pos = (approach.run hn2 (2 * m + 1)).pos ∧
    (approach.run hn2 (2 * (m + 1) + 1)).time
      = (approach.run hn2 (2 * m + 1)).time + 1 := by
  rw [(run_approach m).1, (run_approach (m + 1)).1]
  refine ⟨rfl, ?_⟩
  show (1 : ℝ) / 4 + (↑(m + 1) : ℝ) = 1 / 4 + (m : ℝ) + 1
  push_cast
  ring

end Examples

end DPSS
