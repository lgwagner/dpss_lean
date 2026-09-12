/-
# DPSS — the bound `2 − 1/n` is attained for every `n`

**C3′**, and gap 9 of `STATUS.md`.

`Dpss/Sharpness.lean` shows the bound is attained at `n = 2`, by tracing a
four-configuration family. The paper's construction works for every `n`:

> let all `n` drones start arbitrarily close to the left border, moving right
> independently. After close to one unit of time they reach the right border,
> at which point the rightmost drone turns left and quickly meets all the
> others. The group then moves to the left, with each drone separating from the
> group at its left endpoint.

`PLAN.md` sized the general case as an `n`-drone cascade — `2(n−1)` phases,
each a configuration described by a formula in the phase index, each needing a
minimum over `Fin n` computed by hand. That is the obvious route and it is a
large one.

**This file does not take it.** The trace is never computed. What replaces it
is two observations, both about Lemma 3.1.

## Nobody can turn until the rightmost drone hits the border

Start the drones on a *ladder*: drone `i` at `i·d`, all heading right, with `d`
positive and small. No pair is co-located, so no pair is escorting and none is
approaching — every gap is exactly `d` and, while all drones head right, stays
exactly `d`.

Now suppose some drone turns left. Lemma 3.1's companion
(`coLocated_of_turnsLeft`) says a drone that reverses to leftward is
**co-located with its right-hand neighbour** — so its gap is zero, and the gap
is `d`. Contradiction, *unless the drone has no right-hand neighbour*. So the
first drone to turn is drone `n−1`, and Lemma 3.1 puts its turn at or beyond
`rightEnd (n−1) = 1`.

That pins the elapsed time: positions track time exactly while headings are
fixed, so **nothing turns before time `1 − (n−1)·d`** (`ladder_state`).

## And drone 0's round trip is then forced

Drone `0` heads right until it turns. By Lemma 3.1 it turns at or beyond
`rightEnd 0 = 1/n`; by the paragraph above it cannot turn before time
`1 − (n−1)·d`; and since it started at `0`, its position *is* the elapsed time,
so it turns at a position `w ≥ 1 − (n−1)·d`.

Then it heads left — and Lemma 3.1's other half says a leftward drone reverses
only at or before `leftEnd 0 = 0`, so it keeps going all the way to the border.
It therefore re-enters its own interval `[0, 1/n]` only at time `2w − 1/n`, and

    2w − 1/n  ≥  2 − 2(n−1)d − 1/n  →  2 − 1/n   as  d → 0.

No trace, no cascade, no phases. The construction is the paper's; the proof is
not.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §3, the sharpness paragraph.
-/

import Dpss.Priority

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## The ladder -/

/-- `n` drones evenly spaced by `d` at the left end of the perimeter, all
heading right. The paper's worst case, with the spacing as a parameter. -/
noncomputable def ladder (n : ℕ) (d : ℝ) : Config n where
  time := 0
  pos := fun i => (i.val : ℝ) * d
  dir := fun _ => Dir.right

@[simp] theorem ladder_time (d : ℝ) : (ladder n d).time = 0 := rfl
@[simp] theorem ladder_pos (d : ℝ) (i : Fin n) :
    (ladder n d).pos i = (i.val : ℝ) * d := rfl
@[simp] theorem ladder_dir (d : ℝ) (i : Fin n) :
    (ladder n d).dir i = Dir.right := rfl

theorem ladder_gap (d : ℝ) (i : Fin n) (h : i.val + 1 < n) :
    (ladder n d).gap i h = d := by
  unfold gap
  simp only [ladder_pos, nextIdx_val]
  push_cast
  ring

/-- Every drone heads the same way, so the extra standing condition is free. -/
theorem ladder_apartOnBoundaries (d : ℝ) : (ladder n d).ApartOnBoundaries :=
  apartOnBoundaries_of_dir_const (fun _ => rfl)

/-- And the ladder is a well-formed configuration: on the perimeter, ordered,
and with no escorting pair to keep coherent. -/
theorem ladder_invariant (d : ℝ) (hd : 0 < d) (hdn : ((n : ℝ) - 1) * d ≤ 1) :
    (ladder n d).Invariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi1 : (i.val : ℝ) ≤ (n : ℝ) - 1 := by
      have : (i.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast i.isLt
      linarith
    have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    constructor
    · rw [ladder_pos]; positivity
    · rw [ladder_pos]
      have : (i.val : ℝ) * d ≤ ((n : ℝ) - 1) * d :=
        mul_le_mul_of_nonneg_right hi1 (le_of_lt hd)
      linarith
  · intro i h
    rw [ladder_gap]
    linarith
  · intro i h he
    exfalso
    have hg : (ladder n d).gap i h = 0 := he.1
    rw [ladder_gap] at hg
    linarith

/-! ## Nothing turns before the rightmost drone reaches the border

The heart of the file. While no drone has turned, positions track elapsed time
exactly and every gap is still `d`; a turn would need a gap of zero, which only
the drone without a right-hand neighbour can avoid, and Lemma 3.1 puts *its*
turn at position 1. -/

/-- **The state of a ladder run, for as long as the clock is short of
`1 − (n−1)·d`**: every drone still heads right, and its position is exactly its
starting rung plus the elapsed time. -/
theorem ladder_state {d : ℝ} (hn : 0 < n) (hd : 0 < d)
    (hi : (ladder n d).Invariant) :
    ∀ k : ℕ, ((ladder n d).run hn k).time < 1 - ((n : ℝ) - 1) * d →
      (∀ i : Fin n, ((ladder n d).run hn k).dir i = Dir.right) ∧
      (∀ i : Fin n, ((ladder n d).run hn k).pos i
        = (i.val : ℝ) * d + ((ladder n d).run hn k).time) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun i => rfl, fun i => by rw [run_zero, ladder_pos, ladder_time]; ring⟩
  | succ k ih =>
    intro ht
    have hmono : ((ladder n d).run hn k).time ≤ ((ladder n d).run hn (k + 1)).time :=
      time_mono_run hn hi k
    obtain ⟨hdirk, hposk⟩ := ih (by linarith)
    -- positions at `k+1` follow from the headings at `k`
    have hposk1 : ∀ i : Fin n, ((ladder n d).run hn (k + 1)).pos i
        = (i.val : ℝ) * d + ((ladder n d).run hn (k + 1)).time := by
      intro i
      have hp : ((ladder n d).run hn (k + 1)).pos i
          = ((ladder n d).run hn k).pos i
            + (((ladder n d).run hn k).dir i).sign
              * ((ladder n d).run hn k).timeToNextEvent hn := rfl
      have htt : ((ladder n d).run hn (k + 1)).time
          = ((ladder n d).run hn k).time
            + ((ladder n d).run hn k).timeToNextEvent hn := rfl
      rw [hp, hdirk i, Dir.sign_right, one_mul, hposk i, htt]
      ring
    refine ⟨?_, hposk1⟩
    intro i
    by_contra hne
    -- the only alternative is that drone `i` has just turned left
    have hL : ((ladder n d).run hn (k + 1)).dir i = Dir.left := by
      rcases Dir.eq_left_or_right (((ladder n d).run hn (k + 1)).dir i) with hx | hx
      · exact hx
      · exact absurd hx hne
    have hturn : TurnsLeftAt (ladder n d) hn i k := ⟨hdirk i, hL⟩
    have hge : rightEnd i ≤ ((ladder n d).run hn (k + 1)).pos i :=
      rightEnd_le_pos_of_turnsLeftAt hn hturn
    by_cases hlt : i.val + 1 < n
    · -- it has a right-hand neighbour, so it is now co-located with it — but
      -- the gap is still exactly `d`
      have hinv := invariant_run hn hi (k + 1)
      have hco : ((ladder n d).run hn (k + 1)).CoLocated i hlt :=
        coLocated_of_turnsLeft
          (c := ((ladder n d).run hn k).advance
            (((ladder n d).run hn k).timeToNextEvent hn))
          hinv.onPerimeter (ordered_of_adjOrdered hinv.adjOrdered) hlt
          ⟨hturn.1, hturn.2⟩
      have hg : ((ladder n d).run hn (k + 1)).gap i hlt = 0 := hco
      unfold gap at hg
      rw [hposk1 i, hposk1 (nextIdx i hlt), nextIdx_val] at hg
      push_cast at hg
      have : d = 0 := by linarith
      linarith
    · -- it is the rightmost drone, so Lemma 3.1 puts it on the border
      have hval : i.val + 1 = n := by have := i.isLt; omega
      have hcast : (i.val : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hval
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hre : rightEnd i = 1 := by
        unfold rightEnd
        rw [hcast, div_self (ne_of_gt hnR)]
      rw [hre, hposk1 i] at hge
      have hiv : (i.val : ℝ) = (n : ℝ) - 1 := by linarith
      rw [hiv] at hge
      linarith

/-! ## Drone 0's round trip

Everything above is about the ladder. From here on it is Lemma 3.1 twice: a
rightward drone turns only at or beyond its right endpoint, and a leftward one
only at or before its left endpoint — so drone 0 goes out past `1/n` and comes
back to `0` without stopping. -/

/-- **Drone 0 leaves its interval and does not return until `2w − 1/n`**, where
`w` is where it turns — and `w` is at least `1 − (n−1)·d`. Stated as: at the
instant `s`, drone 0 is strictly beyond its own right endpoint. -/
theorem ladder_outside {d : ℝ} (hn : 0 < n) (hd : 0 < d)
    (hdn : ((n : ℝ) - 1) * d ≤ 1) {s : ℝ}
    (hs1 : 1 / (n : ℝ) < s)
    (hs2 : s < 2 * (1 - ((n : ℝ) - 1) * d) - 1 / (n : ℝ)) :
    ∃ p : ℕ, (ladder n d).InStep hn p s ∧
      rightEnd (⟨0, hn⟩ : Fin n) < (ladder n d).posIn hn p (⟨0, hn⟩ : Fin n) s := by
  classical
  set c : Config n := ladder n d with hc
  set z : Fin n := ⟨0, hn⟩ with hz
  have hi : c.Invariant := ladder_invariant d hd hdn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : rightEnd z = 1 / (n : ℝ) := by
    unfold rightEnd; rw [hz]; norm_num
  have hle : leftEnd z = 0 := leftEnd_zero hn
  -- the first index at which drone 0 heads left
  obtain ⟨b, -, hbL, hbR, hbt⟩ := exists_firstLeft hn hi z 0
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, run_zero] at hbL
    exact Dir.noConfusion hbL
  obtain ⟨b0, rfl⟩ : ∃ b0, b = b0 + 1 := ⟨b - 1, by omega⟩
  -- where it turns, and that the turn is late
  have hturnL : TurnsLeftAt c hn z b0 := ⟨hbR b0 (by omega) (by omega), hbL⟩
  have hw : rightEnd z ≤ (c.run hn (b0 + 1)).pos z :=
    rightEnd_le_pos_of_turnsLeftAt hn hturnL
  have htw : (c.run hn (b0 + 1)).time = (c.run hn (b0 + 1)).pos z := by
    have h0 : (c.run hn 0).time = 0 := rfl
    have hp0 : (c.run hn 0).pos z = 0 := by
      rw [run_zero, hc, ladder_pos, hz]; norm_num
    rw [h0, hp0] at hbt
    linarith
  have hlate : 1 - ((n : ℝ) - 1) * d ≤ (c.run hn (b0 + 1)).time := by
    by_contra hcon
    exact absurd ((ladder_state hn hd hi (b0 + 1) (not_le.mp hcon)).1 z)
      (by rw [hbL]; simp)
  -- it heads left from there all the way to the left border
  obtain ⟨b', hb'ge, hb'R, hb'L, hb't⟩ := exists_firstRight hn hi z (b0 + 1)
  have hb'gt : b0 + 1 < b' := by
    rcases eq_or_lt_of_le hb'ge with rfl | hlt
    · rw [hbL] at hb'R; exact Dir.noConfusion hb'R
    · exact hlt
  have hzero : (c.run hn b').pos z = 0 := by
    obtain ⟨b1, hb1⟩ : ∃ b1, b' = b1 + 1 := ⟨b' - 1, by omega⟩
    have hturnR : TurnsRightAt c hn z b1 := by
      refine ⟨hb'L b1 (by omega) (by omega), ?_⟩
      rw [← hb1]; exact hb'R
    have h1 : (c.run hn (b1 + 1)).pos z ≤ leftEnd z :=
      pos_le_leftEnd_of_turnsRightAt hn hturnR
    have h2 : 0 ≤ (c.run hn b').pos z := (onPerimeter_run hn hi b' z).1
    rw [hb1]
    rw [hle] at h1
    rw [hb1] at h2
    linarith
  have hb't' : (c.run hn b').time = 2 * (c.run hn (b0 + 1)).time := by
    rw [hzero] at hb't
    linarith [htw]
  -- locate the instant `s`
  have hs0 : c.time ≤ s := by
    rw [hc, ladder_time]
    have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  obtain ⟨p, hp1, hp2⟩ := exists_lastBefore hn hi hs0
  refine ⟨p, ⟨hp1, le_of_lt hp2⟩, ?_⟩
  rcases lt_or_ge p (b0 + 1) with hpb | hpb
  · -- still on the way out: drone 0's position *is* the elapsed time
    have hdirp : (c.run hn p).dir z = Dir.right := hbR p (by omega) hpb
    have hconst : ∀ j, 0 ≤ j → j < 0 + p → (c.run hn j).dir z = (c.run hn 0).dir z := by
      intro j _ hj2
      rw [hbR j (by omega) (by omega)]
      rfl
    have hkey := pos_sub_eq_of_dirConst hn z 0 p hconst
    rw [show (c.run hn 0).dir z = Dir.right from rfl, Dir.sign_right, one_mul,
      Nat.zero_add] at hkey
    have hp00 : (c.run hn 0).pos z = 0 := by
      rw [run_zero, hc, ladder_pos, hz]; norm_num
    have ht00 : (c.run hn 0).time = 0 := rfl
    rw [hp00, ht00] at hkey
    have : c.posIn hn p z s = s := by
      unfold posIn
      rw [hdirp, Dir.sign_right, one_mul]
      linarith
    rw [this, hre]
    exact hs1
  · -- on the way back, unless it has already finished — which the clock forbids
    have hpb' : p < b' := by
      by_contra hcon
      have h1 : (c.run hn b').time ≤ (c.run hn p).time :=
        time_mono_run' hn hi (not_lt.mp hcon)
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      have h2 : 2 * (1 - ((n : ℝ) - 1) * d) ≤ (c.run hn b').time := by
        rw [hb't']; linarith
      linarith
    have hdirp : (c.run hn p).dir z = Dir.left := hb'L p hpb hpb'
    have hconst : ∀ j, b0 + 1 ≤ j → j < (b0 + 1) + (p - (b0 + 1)) →
        (c.run hn j).dir z = (c.run hn (b0 + 1)).dir z := by
      intro j hj1 hj2
      rw [hb'L j hj1 (by omega), hbL]
    have hkey := pos_sub_eq_of_dirConst hn z (b0 + 1) (p - (b0 + 1)) hconst
    rw [show (b0 + 1) + (p - (b0 + 1)) = p from by omega, hbL, Dir.sign_left] at hkey
    have heq : c.posIn hn p z s
        = 2 * (c.run hn (b0 + 1)).time - s := by
      unfold posIn
      rw [hdirp, Dir.sign_left]
      have := htw
      linarith
    rw [heq, hre]
    linarith

/-! ## The bound cannot be lowered, at any team size -/

/-- **`2 − 1/n` is attained for every `n ≥ 2`.**

For any `B` strictly less than `2 − 1/n` there is a well-formed configuration
of `n` drones — satisfying the standing invariant and the one extra standing
condition — with a drone outside its own interval at an instant at or after
`B`. So no smaller constant is a correct bound.

At `n = 1` the statement is false and must be: a single drone's interval *is*
the whole perimeter, so it is synchronized from the start, and `2 − 1/1 = 1` is
not attained. -/
theorem bound_sharp_general (hn2 : 2 ≤ n) (B : ℝ) (hB : B < 2 - 1 / (n : ℝ)) :
    ∃ (c : Config n) (hn : 0 < n) (p : ℕ) (s : ℝ),
      c.Invariant ∧ c.ApartOnBoundaries ∧ c.time = 0 ∧
      B ≤ s ∧ c.InStep hn p s ∧
      ¬ (leftEnd (⟨0, hn⟩ : Fin n) ≤ c.posIn hn p (⟨0, hn⟩ : Fin n) s ∧
         c.posIn hn p (⟨0, hn⟩ : Fin n) s ≤ rightEnd (⟨0, hn⟩ : Fin n)) := by
  have hn : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- the instant we aim at must clear both `B` and drone 0's right endpoint
  set B' : ℝ := max B (1 / (n : ℝ)) with hB'
  have hninv : 1 / (n : ℝ) < 2 - 1 / (n : ℝ) := by
    have h1 : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]
      linarith
    linarith
  have hB'lt : B' < 2 - 1 / (n : ℝ) := max_lt hB hninv
  -- choose the rung spacing small enough
  set g : ℝ := 2 - 1 / (n : ℝ) - B' with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  set d : ℝ := min (g / (4 * (n : ℝ))) (1 / (2 * (n : ℝ))) with hd
  have hdpos : 0 < d := lt_min (by positivity) (by positivity)
  have hdle1 : d ≤ 1 / (2 * (n : ℝ)) := min_le_right _ _
  have hdle2 : d ≤ g / (4 * (n : ℝ)) := min_le_left _ _
  have hnd : ((n : ℝ) - 1) * d ≤ 1 := by
    have h1 : ((n : ℝ) - 1) * d ≤ (n : ℝ) * d :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdpos)
    have h2 : (n : ℝ) * d ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hdle1 (by linarith)
    have h3 : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by field_simp
    linarith
  have hnd2 : 2 * (((n : ℝ) - 1) * d) < g := by
    have h1 : ((n : ℝ) - 1) * d ≤ (n : ℝ) * d :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hdpos)
    have h2 : (n : ℝ) * d ≤ (n : ℝ) * (g / (4 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hdle2 (by linarith)
    have h3 : (n : ℝ) * (g / (4 * (n : ℝ))) = g / 4 := by field_simp
    linarith
  -- the instant itself
  set M : ℝ := 2 * (1 - ((n : ℝ) - 1) * d) - 1 / (n : ℝ) with hM
  have hMB : B' < M := by rw [hM, hg] at *; linarith
  set s : ℝ := (B' + M) / 2 with hs
  have hsB' : B' < s := by rw [hs]; linarith
  have hsM : s < M := by rw [hs]; linarith
  have hs1 : 1 / (n : ℝ) < s := lt_of_le_of_lt (le_max_right _ _) hsB'
  obtain ⟨p, hin, hout⟩ := ladder_outside hn hdpos hnd hs1 (by rw [← hM]; exact hsM)
  refine ⟨ladder n d, hn, p, s, ladder_invariant d hdpos hnd,
    ladder_apartOnBoundaries d, rfl,
    le_of_lt (lt_of_le_of_lt (le_max_left _ _) hsB'), hin, ?_⟩
  rintro ⟨-, hle⟩
  linarith

end Config

end DPSS
