/-
# DPSS — escorts stay coherent

`EscortsCoherent` says that an escorting pair points at the boundary it is
escorting to. Until now it has been *assumed* wherever needed — the weakest
link in the invariant set, and the last hypothesis in this development that was
never discharged.

This file proves it is preserved by a step.

## Why it is delicate

The obligation is about drone `i` only: `separationTime` reads just that
drone's position and heading. So the proof is a case analysis on which branch
of `newDir` fired for drone `i`, and most branches settle immediately — a
border event, a separation, or a meet with the right neighbour each place the
drone somewhere that makes the sign work out.

Two branches need real work.

* **Nothing fired.** Then the heading is unchanged, so the pair was already
  escorting *before* the step, and the old coherence carries over — provided
  the step did not overshoot the separation. It cannot, because
  `droneNextTime` includes exactly that deadline.
* **A meet with the *left* neighbour.** Drone `i` then heads towards its own
  left endpoint, which says nothing directly about the boundary it shares with
  `i+1`. This case is settled by asking what could have turned drone `i+1` the
  same way, and every possibility puts the pair at or beyond the shared
  boundary.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2.
-/

import Dpss.Synchronization

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## How a separation deadline evolves -/

/-- **Flying eats into the separation deadline exactly.** The two direction
factors cancel, leaving a clean subtraction. -/
theorem separationTime_advance (c : Config n) (dt : ℝ) (i : Fin n) :
    (c.advance dt).separationTime i = c.separationTime i - dt := by
  unfold separationTime
  simp only [advance_pos, advance_newDir_dir]
  have hs : (c.dir i).sign * (c.dir i).sign = 1 := Dir.sign_mul_self _
  have expand : (commonEnd i - (c.pos i + (c.dir i).sign * dt)) * (c.dir i).sign
      = (commonEnd i - c.pos i) * (c.dir i).sign
        - dt * ((c.dir i).sign * (c.dir i).sign) := by ring
  rw [expand, hs, mul_one]

/-- A pair with equal headings keeps a constant gap, so it is co-located after
flying exactly when it was co-located before. -/
theorem gap_advance_of_dir_eq {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hdir : c.dir i = c.dir (nextIdx i h)) (dt : ℝ) :
    (c.advance dt).gap i h = c.gap i h := by
  rw [gap_advance]
  unfold sepRate
  rw [hdir]
  ring

/-! ## Coherence, branch by branch

Each lemma says: given where the drone ended up and which way it now points,
the separation deadline is not in the past. -/

/-- A drone on the left border, turning right, has its shared boundary ahead. -/
theorem sepTime_nonneg_left_border {c : Config n} {i : Fin n}
    (hpos : c.pos i = 0) (hdir : c.dir i = Dir.right) :
    0 ≤ c.separationTime i := by
  unfold separationTime
  rw [hpos, hdir, Dir.sign_right, mul_one, sub_zero]
  unfold commonEnd
  have := leftEnd_nonneg i
  have := (leftEnd_lt_rightEnd (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt) i)
  linarith

/-- A drone on the right border, turning left, likewise. -/
theorem sepTime_nonneg_right_border {c : Config n} {i : Fin n}
    (hpos : c.pos i = 1) (hdir : c.dir i = Dir.left) :
    0 ≤ c.separationTime i := by
  unfold separationTime commonEnd
  rw [hpos, hdir, Dir.sign_left]
  have := rightEnd_le_one i
  nlinarith [rightEnd_le_one i]

/-- A drone sitting exactly on its shared boundary owes nothing: the deadline
is zero, whichever way it points. -/
theorem sepTime_eq_zero_at_commonEnd {c : Config n} {i : Fin n}
    (hpos : c.pos i = commonEnd i) : c.separationTime i = 0 :=
  (separationTime_eq_zero_iff c i).mpr hpos

/-- A drone at its *left* endpoint heading right has the whole interval ahead
of it before the shared boundary. -/
theorem sepTime_nonneg_at_leftEnd {c : Config n} {i : Fin n}
    (hpos : c.pos i = leftEnd i) (hdir : c.dir i = Dir.right) :
    0 ≤ c.separationTime i := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  unfold separationTime commonEnd
  rw [hpos, hdir, Dir.sign_right, mul_one]
  have := leftEnd_lt_rightEnd hn i
  linarith

/-- A drone at or beyond its shared boundary heading left. -/
theorem sepTime_nonneg_of_ge {c : Config n} {i : Fin n}
    (hpos : commonEnd i ≤ c.pos i) (hdir : c.dir i = Dir.left) :
    0 ≤ c.separationTime i := by
  unfold separationTime
  rw [hdir, Dir.sign_left]
  nlinarith

/-- A drone at or before its shared boundary heading right. -/
theorem sepTime_nonneg_of_le {c : Config n} {i : Fin n}
    (hpos : c.pos i ≤ commonEnd i) (hdir : c.dir i = Dir.right) :
    0 ≤ c.separationTime i := by
  unfold separationTime
  rw [hdir, Dir.sign_right, mul_one]
  linarith

/-! ## Monotonicity of the shared boundaries -/

/-- Shared boundaries increase from left to right. -/
theorem commonEnd_lt_commonEnd_next (i : Fin n) (h : i.val + 1 < n) :
    commonEnd i < commonEnd (nextIdx i h) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold commonEnd rightEnd
  rw [div_lt_div_iff_of_pos_right hn']
  simp only [nextIdx_val]
  push_cast
  linarith

/-- The boundary drone `i` shares with `i+1` is `i+1`'s own left endpoint. -/
theorem leftEnd_next_eq_commonEnd (i : Fin n) (h : i.val + 1 < n) :
    leftEnd (nextIdx i h) = commonEnd i := by
  unfold commonEnd
  exact (rightEnd_eq_leftEnd_succ i h).symm

/-- An escorting pair's deadline is one of the candidates `droneNextTime`
minimises over, so a step never overshoots it. -/
theorem droneNextTime_le_separationTime {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hE : c.Escorting i h) :
    c.droneNextTime i ≤ c.separationTime i := by
  have hnA : ¬ c.Approaching i h := by
    intro hA
    have hEq := hE.2
    rw [hA.1, hA.2] at hEq
    exact Dir.noConfusion hEq
  unfold droneNextTime
  rw [dif_pos h, if_neg hnA, if_pos hE]
  exact min_le_right _ _

/-! ## The workhorse

Both awkward branches of the main proof reduce to the same question: drone `i`
is heading left and co-located with `i+1`, which is *also* heading left — so
where are they? The answer is: at or beyond the boundary they share. Every way
drone `i+1` could have acquired a leftward heading puts it there. -/

/-- **If a co-located pair both end up heading left, they are at or beyond
their shared boundary.** -/
theorem commonEnd_le_pos_of_both_left {c : Config n} (hn : 0 < n)
    {i : Fin n} {h : i.val + 1 < n}
    (hco : (c.advance (c.timeToNextEvent hn)).gap i h = 0)
    (hdi : (c.advance (c.timeToNextEvent hn)).dir i = Dir.left)
    (hnext : (c.advance (c.timeToNextEvent hn)).newDir (nextIdx i h) = Dir.left) :
    commonEnd i ≤ (c.advance (c.timeToNextEvent hn)).pos i := by
  set dt := c.timeToNextEvent hn with hdt
  set c' := c.advance dt with hc'
  -- the pair occupies one point
  have hsame : c'.pos (nextIdx i h) = c'.pos i := by
    have : c'.gap i h = 0 := hco
    unfold gap at this
    linarith
  -- what turned `i+1` leftward?
  unfold newDir at hnext
  split_ifs at hnext with k1 k2 k3 k4 k5 k6
  · -- at the right border: position 1, past every boundary
    have h1 : c'.pos i = 1 := by rw [← hsame]; exact k2.1
    rw [h1]
    unfold commonEnd
    exact rightEnd_le_one i
  · -- separating from *its* right neighbour: on the next boundary along
    have h1 : c'.pos i = commonEnd (nextIdx i h) := by rw [← hsame]; exact k3.2.2
    rw [h1]
    exact le_of_lt (commonEnd_lt_commonEnd_next i h)
  · -- meeting its right neighbour, and turned left, so it is beyond that
    -- boundary, which is beyond ours
    unfold escortDir at hnext
    split_ifs at hnext with hlt
    rw [not_lt] at hlt
    rw [← hsame]
    exact le_trans (le_of_lt (commonEnd_lt_commonEnd_next i h)) hlt
  · -- meeting *us*: then it turned towards our shared boundary, which is its
    -- own left endpoint, and it turned left, so it is at or beyond it
    unfold escortDirLeft at hnext
    split_ifs at hnext with hlt
    rw [not_lt, leftEnd_next_eq_commonEnd] at hlt
    rw [← hsame]
    exact hlt
  · -- nothing fired for `i+1`: it was already heading left, so the pair was
    -- escorting before the step and the old coherence carries over
    have hdj : c'.dir (nextIdx i h) = Dir.left := hnext
    have hdirEq : c.dir i = c.dir (nextIdx i h) := by
      have e1 : c.dir i = Dir.left := hdi
      have e2 : c.dir (nextIdx i h) = Dir.left := hdj
      rw [e1, e2]
    have hgapc : c.gap i h = 0 := by
      rw [← gap_advance_of_dir_eq hdirEq dt]; exact hco
    have hE : c.Escorting i h := ⟨hgapc, hdirEq⟩
    have hbound : dt ≤ c.separationTime i :=
      le_trans (timeToNextEvent_le hn i) (droneNextTime_le_separationTime hE)
    have hnn : 0 ≤ c'.separationTime i := by
      rw [hc', separationTime_advance]; linarith
    unfold separationTime at hnn
    rw [hdi, Dir.sign_left] at hnn
    nlinarith

/-! ## The theorem -/

/-- **Escorts stay coherent across a step.**

The last standing assumption in this development, now discharged. Coherence
concerns drone `i` alone, so the proof is a case analysis on which branch of
`newDir` fired for it: a border event, a separation, or a meet with the right
neighbour each settle the sign immediately, and the two remaining branches go
through `commonEnd_le_pos_of_both_left`. -/
theorem escortsCoherent_step {c : Config n} (hn : 0 < n) :
    (c.step hn).EscortsCoherent := by
  intro i h he
  set dt := c.timeToNextEvent hn with hdt
  set c' := c.advance dt with hc'
  have hco : c'.gap i h = 0 := he.1
  have hesc : c'.newDir i = c'.newDir (nextIdx i h) := he.2
  change 0 ≤ (commonEnd i - c'.pos i) * ((c'.newDir i).sign)
  unfold newDir
  split_ifs with k1 k2 k3 k4 k5 k6
  · -- left border: at 0, heading right; the boundary is ahead
    rw [Dir.sign_right, mul_one, k1.1]
    unfold commonEnd
    have h1 := leftEnd_nonneg i
    have h2 := leftEnd_lt_rightEnd hn i
    linarith
  · -- right border: at 1, heading left
    rw [Dir.sign_left, k2.1]
    have := rightEnd_le_one i
    unfold commonEnd
    nlinarith
  · -- separating from the right neighbour: exactly on the boundary
    have : c'.pos i = commonEnd i := k3.2.2
    rw [this]
    simp
  · -- separating from the left neighbour: at our left endpoint, heading right
    rw [Dir.sign_right, mul_one, pos_eq_leftEnd_of_sepLeft k4]
    unfold commonEnd
    have := leftEnd_lt_rightEnd hn i
    linarith
  · -- meeting the right neighbour: `escortDir` points at the boundary
    unfold escortDir
    split_ifs with hlt
    · rw [Dir.sign_right, mul_one]; linarith
    · rw [Dir.sign_left]; rw [not_lt] at hlt; nlinarith
  · -- meeting the left neighbour
    unfold escortDirLeft
    split_ifs with hlt
    · rw [Dir.sign_right, mul_one]
      have h1 : leftEnd i < commonEnd i := by
        unfold commonEnd; exact leftEnd_lt_rightEnd hn i
      linarith
    · rw [Dir.sign_left]
      have hdi : c'.dir i = Dir.left := by
        obtain ⟨hposi, _, hA⟩ := k6
        have h2 := hA.2
        rwa [nextIdx_prevIdx] at h2
      have hnext : c'.newDir (nextIdx i h) = Dir.left := by
        rw [← hesc]
        unfold newDir
        rw [if_neg k1, if_neg k2, if_neg k3, if_neg k4, if_neg k5, if_pos k6]
        unfold escortDirLeft
        rw [if_neg hlt]
      have := commonEnd_le_pos_of_both_left hn hco hdi hnext
      nlinarith
  · -- nothing fired: heading unchanged
    have hdi : c'.dir i = c'.dir i := rfl
    rcases Dir.eq_left_or_right (c'.dir i) with hL | hR
    · rw [hL, Dir.sign_left]
      have hnext : c'.newDir (nextIdx i h) = Dir.left := by
        rw [← hesc]
        unfold newDir
        rw [if_neg k1, if_neg k2, if_neg k3, if_neg k4, if_neg k5, if_neg k6]
        exact hL
      have := commonEnd_le_pos_of_both_left hn hco hL hnext
      nlinarith
    · -- heading right with nothing due: the pair cannot be approaching, so it
      -- was already escorting and the old deadline carries over
      have hnextR : c'.newDir (nextIdx i h) = Dir.right := by
        rw [← hesc]
        unfold newDir
        rw [if_neg k1, if_neg k2, if_neg k3, if_neg k4, if_neg k5, if_neg k6]
        exact hR
      have hdj : c'.dir (nextIdx i h) = Dir.right := by
        by_contra hne
        have hLj : c'.dir (nextIdx i h) = Dir.left := by
          rcases Dir.eq_left_or_right (c'.dir (nextIdx i h)) with hx | hx
          · exact hx
          · exact absurd hx hne
        exact k5 ⟨h, hco, ⟨hR, hLj⟩⟩
      have hdirEq : c.dir i = c.dir (nextIdx i h) := by
        have e1 : c.dir i = Dir.right := hR
        have e2 : c.dir (nextIdx i h) = Dir.right := hdj
        rw [e1, e2]
      have hgapc : c.gap i h = 0 := by
        rw [← gap_advance_of_dir_eq hdirEq dt]; exact hco
      have hE : c.Escorting i h := ⟨hgapc, hdirEq⟩
      have hbound : dt ≤ c.separationTime i :=
        le_trans (timeToNextEvent_le hn i) (droneNextTime_le_separationTime hE)
      have hnn : 0 ≤ c'.separationTime i := by
        rw [hc', separationTime_advance]; linarith
      unfold separationTime at hnn
      rw [hR, Dir.sign_right] at hnn
      rw [hR, Dir.sign_right]
      exact hnn

/-! ## The invariants close under iteration

With coherence discharged, the three standing properties can finally be bundled
and carried along a whole run rather than assumed afresh at each step. This is
the point at which the development stops reasoning about isolated steps and
starts reasoning about the running system. -/

/-- The standing invariant of a run: drones on the perimeter, in order, with
coherent escorts. -/
structure Invariant (c : Config n) : Prop where
  onPerimeter : c.OnPerimeter
  adjOrdered : c.AdjOrdered
  escortsCoherent : c.EscortsCoherent

/-- **A step preserves the invariant.** -/
theorem invariant_step {c : Config n} (hn : 0 < n) (hi : c.Invariant) :
    (c.step hn).Invariant :=
  ⟨onPerimeter_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent,
   adjOrdered_step hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent,
   escortsCoherent_step hn⟩

/-- **And therefore the whole run satisfies it.** -/
theorem invariant_run {c : Config n} (hn : 0 < n) (hi : c.Invariant) (k : ℕ) :
    (c.run hn k).Invariant := by
  induction k with
  | zero => exact hi
  | succ k ih => exact invariant_step hn ih

/-- Drones never leave the perimeter, ever. -/
theorem onPerimeter_run {c : Config n} (hn : 0 < n) (hi : c.Invariant) (k : ℕ) :
    (c.run hn k).OnPerimeter := (invariant_run hn hi k).onPerimeter

/-- Drones never overtake one another, ever. -/
theorem ordered_run {c : Config n} (hn : 0 < n) (hi : c.Invariant) (k : ℕ) :
    (c.run hn k).Ordered :=
  ordered_of_adjOrdered (invariant_run hn hi k).adjOrdered

/-- Time never runs backwards along a run. -/
theorem time_mono_run {c : Config n} (hn : 0 < n) (hi : c.Invariant) (k : ℕ) :
    (c.run hn k).time ≤ (c.run hn (k + 1)).time := by
  have h := invariant_run hn hi k
  exact step_time_le hn h.onPerimeter h.adjOrdered h.escortsCoherent

/-- **Theorem 2.1 at `n = 1`, unconditionally.**

Earlier this needed "assume the drones stay on the perimeter" as a hypothesis.
That assumption is now a theorem, so the `n = 1` case of the convergence result
stands on its own. -/
theorem convergesBy_of_one' (c : Config 1) (hn : 0 < 1) (hi : c.Invariant) :
    ConvergesBy c hn :=
  convergesBy_of_one c hn (fun j => onPerimeter_run hn hi j)

end Config

end DPSS
