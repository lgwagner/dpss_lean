/-
# DPSS — the bound `2 − 1/n` is attained

**C3**, and the answer to gap 4 of `STATUS.md`.

`Convergence.lean` proves the drones are synchronized by time `2 − 1/n`. That
is only half of what the paper claims: it also says the bound is **sharp**, and
a proof that lost even an `ε` would be a weaker theorem than the one advertised.
Nothing in this development checked that until now — `Examples.lean` traces one
`n = 2` configuration which converges at `5/4` against a bound of `3/2`, a
quarter of slack, and a single configuration cannot close it.

Closing it needs a **family**. The paper's own worst case:

> let all `n` drones start arbitrarily close to the left border, moving right
> independently. After close to one unit of time they reach the right border,
> at which point the rightmost drone turns left and quickly meets all the
> others. The group then moves to the left, with each drone separating from the
> group at its left endpoint.

At `n = 2` that is: drone `0` at the border and drone `1` a distance `ε` ahead,
both heading right. The trace is four configurations long and every time in it
is a function of `ε`:

| step | time | state |
|---|---|---|
| 0 | `0` | `0 →`, `ε →` |
| 1 | `1 − ε` | `1−ε →`, `1 ←` — the right drone has bounced |
| 2 | `1 − ε/2` | both at `1 − ε/2 ←` — they have met and escort back |
| 3 | `3/2 − ε` | both at `1/2`, separating — synchronized |

Drone `0` is outside its own interval `[0, 1/2]` for the whole of the return
leg, and does not re-enter it until `3/2 − ε`. So for every `ε` there is an
instant as late as `3/2 − 2ε` at which the team is **not** synchronized, and
`3/2 − 2ε → 3/2 = 2 − 1/2` as `ε → 0`.

Hence no bound smaller than `2 − 1/n` is correct, which is `bound_sharp` below.

## What this does and does not establish

It establishes sharpness **at `n = 2`**. The paper's construction works for
every `n`, and the general version would need an `n`-drone cascade — each drone
peeling off the group at its own endpoint — which is a much larger trace. What
the `n = 2` family settles is the thing that actually matters for judging the
proof: the `2 − 1/n` in `Convergence.lean` is not slack that a sharper argument
could tighten. It is the truth.
-/

import Dpss.Convergence

set_option linter.style.header false

namespace DPSS

namespace Examples

open Config

/-! ## The family -/

variable {e : ℝ}

/-- Two drones at the left end, a distance `e` apart, both heading out. -/
noncomputable def spreadE (e : ℝ) : Config 2 where
  time := 0
  pos := fun i => if i.val = 0 then 0 else e
  dir := fun _ => Dir.right

/-- The right drone has bounced off the far border; the left one is still
heading out, far outside its own interval. -/
noncomputable def chaseE (e t : ℝ) : Config 2 where
  time := t
  pos := fun i => if i.val = 0 then 1 - e else 1
  dir := fun i => if i.val = 0 then Dir.right else Dir.left

/-- They have met at `1 − e/2`, beyond their shared boundary, and escort back
towards it. -/
noncomputable def escortE (e t : ℝ) : Config 2 where
  time := t
  pos := fun _ => 1 - e / 2
  dir := fun _ => Dir.left

@[simp] theorem spreadE_pos_d0 : (spreadE e).pos d0 = 0 := rfl
@[simp] theorem spreadE_pos_d1 : (spreadE e).pos d1 = e := rfl
@[simp] theorem spreadE_dir (i : Fin 2) : (spreadE e).dir i = Dir.right := rfl
@[simp] theorem spreadE_time : (spreadE e).time = 0 := rfl
@[simp] theorem chaseE_pos_d0 (t : ℝ) : (chaseE e t).pos d0 = 1 - e := rfl
@[simp] theorem chaseE_pos_d1 (t : ℝ) : (chaseE e t).pos d1 = 1 := rfl
@[simp] theorem chaseE_dir_d0 (t : ℝ) : (chaseE e t).dir d0 = Dir.right := rfl
@[simp] theorem chaseE_dir_d1 (t : ℝ) : (chaseE e t).dir d1 = Dir.left := rfl
@[simp] theorem chaseE_time (t : ℝ) : (chaseE e t).time = t := rfl
@[simp] theorem escortE_pos (t : ℝ) (i : Fin 2) : (escortE e t).pos i = 1 - e / 2 := rfl
@[simp] theorem escortE_dir (t : ℝ) (i : Fin 2) : (escortE e t).dir i = Dir.left := rfl
@[simp] theorem escortE_time (t : ℝ) : (escortE e t).time = t := rfl

/-! ## The starting configuration is a legitimate one

A counterexample only bites if it is reachable behaviour rather than a
malformed start, so both standing conditions are discharged. -/

theorem spreadE_invariant (h0 : 0 < e) (h1 : e < 1) : (spreadE e).Invariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases fin2_cases i with hi | hi <;> subst hi
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by simp; linarith, by simp; linarith⟩
  · intro i h
    rcases fin2_cases i with hi | hi <;> subst hi
    · unfold gap
      rw [nextIdx_d0_eq, spreadE_pos_d0, spreadE_pos_d1]
      linarith
    · exact absurd h (by norm_num [d1])
  · intro i h he
    exfalso
    rcases fin2_cases i with hi | hi <;> subst hi
    · have hg : (spreadE e).gap d0 h = 0 := he.1
      unfold gap at hg
      rw [nextIdx_d0_eq, spreadE_pos_d0, spreadE_pos_d1] at hg
      linarith
    · exact absurd h (by norm_num [d1])

theorem spreadE_apartOnBoundaries : (spreadE e).ApartOnBoundaries :=
  apartOnBoundaries_of_dir_const (fun _ => rfl)

/-! ## The trace -/

theorem spreadE_timeToNext (h0 : 0 < e) (h1 : e < 1) :
    (spreadE e).timeToNextEvent hn2 = 1 - e := by
  have hA : ¬ (spreadE e).Approaching d0 bounce_h := by
    rintro ⟨-, h2⟩
    rw [nextIdx_d0_eq, spreadE_dir] at h2
    exact Dir.noConfusion h2
  have hE : ¬ (spreadE e).Escorting d0 bounce_h := by
    rintro ⟨hg, -⟩
    unfold CoLocated gap at hg
    rw [nextIdx_d0_eq, spreadE_pos_d0, spreadE_pos_d1] at hg
    linarith
  rw [timeToNextEvent_two, droneNextTime_d1, droneNextTime_d0_apart _ hA hE,
      borderTime_of_right (spreadE_dir d0), borderTime_of_right (spreadE_dir d1),
      spreadE_pos_d0, spreadE_pos_d1]
  rw [min_eq_right (by linarith)]

theorem chaseE_timeToNext (t : ℝ) (h0 : 0 < e) (h1 : e < 1) :
    (chaseE e t).timeToNextEvent hn2 = e / 2 := by
  have hA : (chaseE e t).Approaching d0 bounce_h := by
    refine ⟨chaseE_dir_d0 t, ?_⟩
    rw [nextIdx_d0_eq]; exact chaseE_dir_d1 t
  have hgap : (chaseE e t).gap d0 bounce_h = e := by
    unfold gap
    rw [nextIdx_d0_eq, chaseE_pos_d0, chaseE_pos_d1]; ring
  rw [timeToNextEvent_two, droneNextTime_d1, droneNextTime_d0_approaching _ hA,
      borderTime_of_right (chaseE_dir_d0 t), borderTime_of_left (chaseE_dir_d1 t),
      chaseE_pos_d0, chaseE_pos_d1]
  unfold meetTime
  rw [hgap, show (1 : ℝ) - (1 - e) = e from by ring,
    min_eq_left (le_trans (min_le_right _ _) (show e / 2 ≤ (1 : ℝ) by linarith)),
    min_eq_right (show e / 2 ≤ e by linarith)]

theorem escortE_timeToNext (t : ℝ) (h0 : 0 < e) (h1 : e < 1) :
    (escortE e t).timeToNextEvent hn2 = 1 / 2 - e / 2 := by
  have hA : ¬ (escortE e t).Approaching d0 bounce_h := by
    rintro ⟨hd, -⟩
    rw [escortE_dir] at hd
    exact Dir.noConfusion hd
  have hE : (escortE e t).Escorting d0 bounce_h := by
    refine ⟨?_, ?_⟩
    · unfold CoLocated gap
      rw [nextIdx_d0_eq, escortE_pos, escortE_pos]; ring
    · rw [nextIdx_d0_eq, escortE_dir, escortE_dir]
  have hd : (escortE e t).droneNextTime d0
      = min ((escortE e t).borderTime d0) ((escortE e t).separationTime d0) := by
    unfold droneNextTime
    rw [dif_pos bounce_h, if_neg hA, if_pos hE]
  rw [timeToNextEvent_two, droneNextTime_d1, hd,
      borderTime_of_left (escortE_dir t d0),
      borderTime_of_left (escortE_dir t d1), escortE_pos, escortE_pos]
  unfold separationTime
  rw [escortE_pos, escortE_dir, Dir.sign_left, commonEnd_d0]
  rw [show (1 / 2 - (1 - e / 2)) * (-1 : ℝ) = 1 / 2 - e / 2 by ring,
    min_eq_left (min_le_left _ _),
    min_eq_right (show (1 : ℝ) / 2 - e / 2 ≤ 1 - e / 2 by linarith)]

theorem step_spreadE (h0 : 0 < e) (h1 : e < 1) :
    (spreadE e).step hn2 = chaseE e (1 - e) := by
  have hdt := spreadE_timeToNext h0 h1
  have hp0 : ((spreadE e).advance (1 - e)).pos d0 = 1 - e := by
    simp only [advance_pos, spreadE_pos_d0, spreadE_dir, Dir.sign_right]; ring
  have hp1 : ((spreadE e).advance (1 - e)).pos d1 = 1 := by
    simp only [advance_pos, spreadE_pos_d1, spreadE_dir, Dir.sign_right]; ring
  have hco : ¬ ((spreadE e).advance (1 - e)).CoLocated d0 bounce_h := by
    unfold CoLocated gap
    rw [nextIdx_d0_eq, hp0, hp1]
    intro hx; linarith
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt, spreadE_time, chaseE_time]; ring
  · rcases fin2_cases i with h | h <;> subst h
    · simp only [step_pos, hdt, spreadE_pos_d0, spreadE_dir, Dir.sign_right,
        chaseE_pos_d0]; ring
    · simp only [step_pos, hdt, spreadE_pos_d1, spreadE_dir, Dir.sign_right,
        chaseE_pos_d1]; ring
  · rcases fin2_cases i with h | h <;> subst h
    · rw [step_dir, hdt, chaseE_dir_d0]
      rw [newDir_d0_unchanged ?_ ?_ ?_ ?_]
      · simp only [advance_newDir_dir, spreadE_dir]
      · rintro ⟨hp, -⟩; rw [hp0] at hp; linarith
      · rintro ⟨hp, -⟩; rw [hp0] at hp; linarith
      · rintro ⟨_hh, hs⟩; exact hco hs.1
      · rintro ⟨_hh, hs, _ha⟩; exact hco hs
    · rw [step_dir, hdt, chaseE_dir_d1]
      apply newDir_atRightBorder
      · rintro ⟨hp, -⟩; rw [hp1] at hp; norm_num at hp
      · exact ⟨hp1, by simp only [advance_newDir_dir, spreadE_dir]⟩

theorem step_chaseE (t : ℝ) (h0 : 0 < e) (h1 : e < 1) :
    (chaseE e t).step hn2 = escortE e (t + e / 2) := by
  have hdt := chaseE_timeToNext t h0 h1
  have hpos : ∀ i, ((chaseE e t).advance (e / 2)).pos i = 1 - e / 2 := by
    intro i
    rcases fin2_cases i with h | h <;> subst h
    · simp only [advance_pos, chaseE_pos_d0, chaseE_dir_d0, Dir.sign_right]; ring
    · simp only [advance_pos, chaseE_pos_d1, chaseE_dir_d1, Dir.sign_left]; ring
  have hco : ((chaseE e t).advance (e / 2)).CoLocated d0 bounce_h := by
    unfold CoLocated gap
    rw [nextIdx_d0_eq, hpos d0, hpos d1]; ring
  have hnotsep : ¬ ((chaseE e t).advance (e / 2)).AtSeparation d0 bounce_h := by
    rintro ⟨-, hp⟩
    rw [hpos d0, commonEnd_d0] at hp
    linarith
  have hA : ((chaseE e t).advance (e / 2)).Approaching d0 bounce_h := by
    refine ⟨by simp only [advance_newDir_dir, chaseE_dir_d0], ?_⟩
    rw [nextIdx_d0_eq]
    simp only [advance_newDir_dir, chaseE_dir_d1]
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt, chaseE_time, escortE_time]
  · rcases fin2_cases i with h | h <;> subst h
    · simp only [step_pos, hdt, chaseE_pos_d0, chaseE_dir_d0, Dir.sign_right,
        escortE_pos]; ring
    · simp only [step_pos, hdt, chaseE_pos_d1, chaseE_dir_d1, Dir.sign_left,
        escortE_pos]; ring
  · rcases fin2_cases i with h | h <;> subst h
    · rw [step_dir, hdt, escortE_dir]
      unfold newDir
      rw [if_neg, if_neg, if_neg, if_neg (not_sepLeft_d0 _),
        if_pos ⟨bounce_h, hco, hA⟩]
      · unfold escortDir
        rw [if_neg]
        rw [hpos d0, commonEnd_d0]
        intro hx; linarith
      · rintro ⟨_hh, hs⟩; exact hnotsep hs
      · rintro ⟨hp, -⟩; rw [hpos d0] at hp; linarith
      · rintro ⟨hp, -⟩; rw [hpos d0] at hp; linarith
    · rw [step_dir, hdt, escortE_dir]
      unfold newDir
      rw [if_neg, if_neg, if_neg (not_sepRight_d1 _), if_neg,
          if_neg (not_meetRight_d1 _), if_pos ⟨by norm_num [d1], hco, hA⟩]
      · unfold escortDirLeft
        rw [if_neg]
        rw [hpos d1, leftEnd_d1]
        intro hx; linarith
      · rintro ⟨_hh, hs⟩; exact hnotsep hs
      · rintro ⟨hp, -⟩; rw [hpos d1] at hp; linarith
      · rintro ⟨hp, -⟩; rw [hpos d1] at hp; linarith

theorem step_escortE (t : ℝ) (h0 : 0 < e) (h1 : e < 1) :
    (escortE e t).step hn2 = atBoundary (t + (1 / 2 - e / 2)) := by
  have hdt := escortE_timeToNext t h0 h1
  have hpos : ∀ i, ((escortE e t).advance (1 / 2 - e / 2)).pos i = 1 / 2 := by
    intro i
    simp only [advance_pos, escortE_pos, escortE_dir, Dir.sign_left]; ring
  have hsep : ((escortE e t).advance (1 / 2 - e / 2)).AtSeparation d0 bounce_h := by
    refine ⟨?_, ?_⟩
    · unfold CoLocated gap
      rw [nextIdx_d0_eq, hpos d0, hpos d1]; ring
    · rw [hpos d0, commonEnd_d0]
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · simp only [step_time, hdt, escortE_time]; rfl
  · rcases fin2_cases i with h | h <;> subst h
    · simp only [step_pos, hdt, escortE_pos, escortE_dir, Dir.sign_left,
        atBoundary_pos]; ring
    · simp only [step_pos, hdt, escortE_pos, escortE_dir, Dir.sign_left,
        atBoundary_pos]; ring
  · rcases fin2_cases i with h | h <;> subst h
    · rw [step_dir, hdt, atBoundary_dir_d0]
      unfold newDir
      rw [if_neg, if_neg, if_pos ⟨bounce_h, hsep⟩]
      · rintro ⟨hp, -⟩; rw [hpos d0] at hp; norm_num at hp
      · rintro ⟨hp, -⟩; rw [hpos d0] at hp; norm_num at hp
    · rw [step_dir, hdt, atBoundary_dir_d1]
      unfold newDir
      rw [if_neg, if_neg, if_neg (not_sepRight_d1 _), if_pos ⟨by norm_num [d1], hsep⟩]
      · rintro ⟨hp, -⟩; rw [hpos d1] at hp; norm_num at hp
      · rintro ⟨hp, -⟩; rw [hpos d1] at hp; norm_num at hp

/-! ## Where the run is, step by step -/

theorem run_spreadE_1 (h0 : 0 < e) (h1 : e < 1) :
    (spreadE e).run hn2 1 = chaseE e (1 - e) := by
  rw [run_succ, run_zero, step_spreadE h0 h1]

theorem run_spreadE_2 (h0 : 0 < e) (h1 : e < 1) :
    (spreadE e).run hn2 2 = escortE e (1 - e / 2) := by
  rw [show (spreadE e).run hn2 2 = ((spreadE e).run hn2 1).step hn2 from rfl,
    run_spreadE_1 h0 h1, step_chaseE _ h0 h1]
  congr 1
  ring

theorem run_spreadE_3 (h0 : 0 < e) (h1 : e < 1) :
    (spreadE e).run hn2 3 = atBoundary (3 / 2 - e) := by
  rw [show (spreadE e).run hn2 3 = ((spreadE e).run hn2 2).step hn2 from rfl,
    run_spreadE_2 h0 h1, step_escortE _ h0 h1]
  congr 1
  ring

/-! ## The late instant at which the team is still unsynchronized

Step 2 is the return leg: both drones at `1 − e/2` heading left, arriving at
`1/2` only at time `3/2 − e`. Drone `0`'s interval is `[0, 1/2]`, so it is
outside it for the whole leg. Read the position at `3/2 − 2e`. -/

/-- **At time `3/2 − 2e` the left drone is at `1/2 + e`** — outside its own
interval, and `3/2 − 2e` is as close to `3/2` as one likes. -/
theorem spreadE_outside (h0 : 0 < e) (h3 : e < 1 / 3) :
    (spreadE e).InStep hn2 2 (3 / 2 - 2 * e) ∧
      (spreadE e).posIn hn2 2 d0 (3 / 2 - 2 * e) = 1 / 2 + e := by
  have h1 : e < 1 := by linarith
  have hr2 := run_spreadE_2 h0 h1
  have hr3 := run_spreadE_3 h0 h1
  constructor
  · refine ⟨?_, ?_⟩
    · rw [hr2, escortE_time]; linarith
    · rw [show ((2 : ℕ) + 1) = 3 from rfl, hr3]
      show (3 : ℝ) / 2 - 2 * e ≤ 3 / 2 - e
      linarith
  · unfold posIn
    rw [hr2, escortE_pos, escortE_dir, escortE_time, Dir.sign_left]
    ring

/-- **The bound `2 − 1/n` cannot be lowered.** For any `B` strictly less than
`2 − 1/2`, some legitimate two-drone configuration has a drone outside its own
interval at an instant at or after `B`. -/
theorem bound_sharp (B : ℝ) (hB : B < 2 - 1 / (2 : ℝ)) :
    ∃ c : Config 2, c.Invariant ∧ c.ApartOnBoundaries ∧ c.time = 0 ∧
      ∃ (p : ℕ) (s : ℝ), c.time + B ≤ s ∧ c.InStep hn2 p s ∧
        ¬ (leftEnd d0 ≤ c.posIn hn2 p d0 s ∧ c.posIn hn2 p d0 s ≤ rightEnd d0) := by
  -- pick `e` small enough that `3/2 - 2e` is still past `B`
  set e : ℝ := min (1 / 4) ((3 / 2 - B) / 2) with he
  have hB' : (0 : ℝ) < 3 / 2 - B := by norm_num at hB ⊢; linarith
  have h0 : 0 < e := lt_min (by norm_num) (by linarith)
  have h3 : e < 1 / 3 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hBe : B ≤ 3 / 2 - 2 * e := by
    have := min_le_right (1 / 4 : ℝ) ((3 / 2 - B) / 2)
    rw [← he] at this
    linarith
  obtain ⟨hin, hpos⟩ := spreadE_outside h0 h3
  refine ⟨spreadE e, spreadE_invariant h0 (by linarith), spreadE_apartOnBoundaries,
    rfl, 2, 3 / 2 - 2 * e, by simpa using hBe, hin, ?_⟩
  rintro ⟨-, hle⟩
  rw [hpos, rightEnd_d0] at hle
  linarith

end Examples

end DPSS
