/-
# DPSS — the balance of a pair about their shared boundary

This file opens the attack on **Lemma 3.2**, the gate to the whole convergence
proof: *if drone `j` is left synchronized and `j`, `j+1` separate at their
common endpoint, then `j+1` is left synchronized too.*

## The idea

The paper argues it through timing — *"drone `j+1` must have taken at least as
long to turn around as drone `j`"* — with a picture. That is awkward to
formalize directly. The same content packs into a single number.

Define the pair's **balance** about the boundary they share:

    balance = (pos j − commonEnd) + (pos (j+1) − commonEnd)

Two facts make it the right quantity.

* At a separation the pair sits exactly on the boundary, so **balance is zero**.
* It evolves linearly at rate `sign j + sign (j+1)`, so it is *constant*
  whenever the two drones head opposite ways — which is exactly what they do
  immediately after separating, and again while approaching each other.

And its sign says precisely what Lemma 3.2's induction needs: **balance ≥ 0 iff
any meeting of the pair happens at or beyond their shared boundary.**

## What is proved here, and what is not

Everything below is proved. What is *not* yet proved is that balance stays
nonnegative along a run. That is the real content of Lemma 3.2 and it needs the
timing argument: the danger is both drones heading left at once, which drives
the balance down, and ruling that out requires knowing how their turns
interleave. `LeftSyncFrom` at the end states the obligation precisely rather
than assuming it.

## Reference

Avigad–van Doorn, arXiv:2008.04262, Lemma 3.2 and Fig. 2.
-/

import Dpss.ExamplesThree

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-- How far the pair `(i, i+1)` sits, jointly, beyond the boundary they share.
Zero when they straddle it symmetrically or sit on it; positive when they are
displaced outward on balance. -/
noncomputable def pairBalance (c : Config n) (i : Fin n) (h : i.val + 1 < n) : ℝ :=
  (c.pos i - commonEnd i) + (c.pos (nextIdx i h) - commonEnd i)

/-- The balance evolves linearly, at the sum of the two headings. In
particular it is **constant whenever the drones head opposite ways**. -/
theorem pairBalance_advance (c : Config n) (dt : ℝ) (i : Fin n)
    (h : i.val + 1 < n) :
    (c.advance dt).pairBalance i h
      = c.pairBalance i h
        + ((c.dir i).sign + (c.dir (nextIdx i h)).sign) * dt := by
  unfold pairBalance
  simp only [advance_pos]
  ring

/-- Opposite headings hold the balance fixed. -/
theorem pairBalance_advance_of_opposite {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hd : c.dir (nextIdx i h) = (c.dir i).flip) (dt : ℝ) :
    (c.advance dt).pairBalance i h = c.pairBalance i h := by
  rw [pairBalance_advance, hd, Dir.sign_flip]
  ring

/-- **A separation zeroes the balance.** The pair is co-located on the very
boundary the balance is measured from. -/
theorem pairBalance_eq_zero_of_atSeparation {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hs : c.AtSeparation i h) : c.pairBalance i h = 0 := by
  obtain ⟨hco, hp⟩ := hs
  unfold CoLocated gap at hco
  unfold pairBalance
  have : c.pos (nextIdx i h) = c.pos i := by linarith
  rw [this, hp]
  ring

/-- **The sign of the balance decides where the pair can meet.** If it is
nonnegative, any co-location happens at or beyond the shared boundary — which
is exactly the induction hypothesis Lemma 3.2 carries. -/
theorem commonEnd_le_pos_of_coLocated {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hco : c.CoLocated i h)
    (hb : 0 ≤ c.pairBalance i h) : commonEnd i ≤ c.pos i := by
  unfold CoLocated gap at hco
  unfold pairBalance at hb
  have hEq : c.pos (nextIdx i h) = c.pos i := by linarith
  rw [hEq] at hb
  linarith

/-- Conversely, a meeting strictly inside the boundary forces a negative
balance. Stated so that a failure of Lemma 3.2 would be visible as a balance
going negative, rather than as something unnamed. -/
theorem pairBalance_neg_of_coLocated_lt {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hco : c.CoLocated i h)
    (hlt : c.pos i < commonEnd i) : c.pairBalance i h < 0 := by
  unfold CoLocated gap at hco
  unfold pairBalance
  have hEq : c.pos (nextIdx i h) = c.pos i := by linarith
  rw [hEq]
  linarith

/-- **The payoff: a nonnegative balance keeps the right-hand drone inside its
own interval.**

Either the left drone is at or before the boundary, in which case the balance
pushes its partner past it; or the left drone is already beyond the boundary,
in which case ordering puts its partner beyond too. The boundary they share
*is* the right-hand drone's left endpoint, so this is precisely left
synchronization for that drone. -/
theorem leftEnd_le_pos_of_pairBalance {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hb : 0 ≤ c.pairBalance i h) (hord : 0 ≤ c.gap i h) :
    leftEnd (nextIdx i h) ≤ c.pos (nextIdx i h) := by
  rw [leftEnd_next_eq_commonEnd i h]
  unfold pairBalance at hb
  unfold gap at hord
  rcases le_or_gt (c.pos i) (commonEnd i) with hle | hlt
  · linarith
  · linarith

/-! ## What can drive the balance down

The balance changes at `sign i + sign (i+1)`, so it can only *fall* when both
drones head left. And when both head left while **co-located**, they are
escorting — so the scheduler will not let the step run past their separation,
which is exactly where the balance reaches zero. It stops there.

That leaves one configuration class, and only one. -/

/-- Both drones of the pair heading left while apart. **The only way the
balance can go negative.** -/
def BothLeftApart (c : Config n) (i : Fin n) (h : i.val + 1 < n) : Prop :=
  c.dir i = Dir.left ∧ c.dir (nextIdx i h) = Dir.left ∧ ¬ c.CoLocated i h

/-- An escorting pair's balance is exactly twice its separation deadline. So
"the step does not overshoot the separation" and "the step does not drive the
balance negative" are the *same statement*. -/
theorem pairBalance_eq_two_mul_separationTime {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (he : c.Escorting i h) (hd : c.dir i = Dir.left) :
    c.pairBalance i h = 2 * c.separationTime i := by
  have hco : c.gap i h = 0 := he.1
  unfold gap at hco
  unfold pairBalance separationTime
  rw [hd, Dir.sign_left]
  have hEq : c.pos (nextIdx i h) = c.pos i := by linarith
  rw [hEq]
  ring

/-- **A step cannot drive the balance negative, except from the one bad class.** -/
theorem pairBalance_nonneg_step {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} (hb : 0 ≤ c.pairBalance i h)
    (hnb : ¬ c.BothLeftApart i h) : 0 ≤ (c.step hn).pairBalance i h := by
  have hdt : 0 ≤ c.timeToNextEvent hn :=
    timeToNextEvent_nonneg hn hi.onPerimeter hi.adjOrdered hi.escortsCoherent
  have hev : (c.step hn).pairBalance i h
      = c.pairBalance i h
        + ((c.dir i).sign + (c.dir (nextIdx i h)).sign) * c.timeToNextEvent hn :=
    pairBalance_advance c _ i h
  rw [hev]
  rcases Dir.eq_left_or_right (c.dir i) with hL | hR
  · rcases Dir.eq_left_or_right (c.dir (nextIdx i h)) with hL2 | hR2
    · -- both heading left: they must be co-located, hence escorting, and the
      -- scheduler stops them exactly at the boundary
      have hco : c.CoLocated i h := by
        by_contra hnc
        exact hnb ⟨hL, hL2, hnc⟩
      have he : c.Escorting i h := ⟨hco, by rw [hL, hL2]⟩
      have hbal : c.pairBalance i h = 2 * c.separationTime i :=
        pairBalance_eq_two_mul_separationTime he hL
      have hbound : c.timeToNextEvent hn ≤ c.separationTime i :=
        le_trans (timeToNextEvent_le hn i) (droneNextTime_le_separationTime he)
      rw [hL, hL2, Dir.sign_left, hbal]
      linarith
    · -- opposite headings: the balance is untouched
      rw [hL, hR2, Dir.sign_left, Dir.sign_right]
      linarith
  · rcases Dir.eq_left_or_right (c.dir (nextIdx i h)) with hL2 | hR2
    · rw [hR, hL2, Dir.sign_left, Dir.sign_right]
      linarith
    · -- both heading right: the balance only grows
      rw [hR, hR2, Dir.sign_right]
      linarith

/-! ## A drone only ever turns left onto its neighbour

The `BothLeftApart` obstruction has three ways to arise: the left drone turns
left, the right drone turns left, or neither turns and the pair was already in
that state. This settles the first, and it settles it outright.

**Whenever drone `i` reverses to leftward, it is co-located with `i+1`.** Look
at what can reverse it: a meet with `i+1` (co-located by definition), a
separation from `i+1` (likewise), or the right perimeter border — and a drone
at position 1 has its right-hand neighbour pinned there too, between it and the
edge. Nothing else can turn a rightward drone around.

So a leftward-turning drone is never *apart* from its neighbour, and that
branch of `BothLeftApart` cannot occur. -/

/-- **A drone that reverses to leftward is co-located with its right-hand
neighbour.** -/
theorem coLocated_of_turnsLeft {c : Config n} (hp : c.OnPerimeter)
    (ho : c.Ordered) {i : Fin n} (h : i.val + 1 < n) (ht : c.TurnsLeft i) :
    c.CoLocated i h := by
  obtain ⟨hd, hnew⟩ := ht
  have hle : i ≤ nextIdx i h := by
    rw [Fin.le_def, nextIdx_val]; omega
  unfold newDir at hnew
  split_ifs at hnew with h1 h2 h3 h4 h5 h6
  · -- at the right perimeter border: the neighbour is pinned there too
    unfold CoLocated gap
    rw [pos_eq_one_of_ge ho hp hle h2.1, h2.1]
    ring
  · -- separating from that very neighbour
    exact h3.2.1
  · -- meeting that very neighbour
    exact h5.2.1
  · -- a rightward drone cannot be meeting its *left* neighbour
    exact absurd h6 (not_meetLeft_of_dir_right hd)
  · -- nothing fired, so it did not turn at all
    rw [hd] at hnew
    exact absurd hnew (fun hc => Dir.noConfusion hc)

/-- Restated for the obstruction: a drone that reverses to leftward cannot be
the left member of a `BothLeftApart` pair. -/
theorem not_bothLeftApart_of_turnsLeft {c : Config n} (hp : c.OnPerimeter)
    (ho : c.Ordered) {i : Fin n} (h : i.val + 1 < n) (ht : c.TurnsLeft i) :
    ¬ (c.newDir i = Dir.left ∧ c.newDir (nextIdx i h) = Dir.left ∧
        ¬ c.CoLocated i h) := by
  rintro ⟨-, -, hnc⟩
  exact hnc (coLocated_of_turnsLeft hp ho h ht)

/-- **The mirror: a drone that reverses to rightward is co-located with its
left-hand neighbour.**

Symmetric to `coLocated_of_turnsLeft`, and needed for the same reason: to know
what a pair's headings can be immediately after a step. Whatever can reverse a
leftward drone — a meet with its left neighbour, a separation from it, or the
left perimeter border — leaves it on top of that neighbour. -/
theorem coLocated_of_turnsRight {c : Config n} (hp : c.OnPerimeter)
    (ho : c.Ordered) {i : Fin n} (hpos : 0 < i.val) (ht : c.TurnsRight i) :
    c.CoLocated (prevIdx i hpos) (prevIdx_lt i hpos) := by
  obtain ⟨hd, hnew⟩ := ht
  have hle : prevIdx i hpos ≤ i := by
    rw [Fin.le_def, prevIdx_val]; omega
  have hself : nextIdx (prevIdx i hpos) (prevIdx_lt i hpos) = i :=
    nextIdx_prevIdx i hpos
  unfold newDir at hnew
  split_ifs at hnew with h1 h2 h3 h4 h5 h6
  · -- at the left border: the left-hand neighbour is pinned there too
    unfold CoLocated gap
    rw [hself, h1.1, pos_eq_zero_of_le ho hp hle h1.1]
    ring
  · -- separating from that very neighbour
    exact h4.2.1
  · -- a leftward drone cannot be meeting its *right* neighbour
    exact absurd h5 (not_meetRight_of_dir_left hd)
  · -- meeting that very neighbour
    exact h6.2.1
  · -- nothing fired, so it did not turn at all
    rw [hd] at hnew
    exact absurd hnew (fun hc => Dir.noConfusion hc)

/-! ## A pair already escorting stays together

The second of the three ways `BothLeftApart` could arise: neither drone turns,
and the pair was already heading left. If the obstruction did not hold before
the step, the pair was co-located — hence escorting — and uniform speed keeps
them together. So that branch cannot introduce the obstruction either. -/

/-- **If a leftward pair was not already apart, it is still together after a
step.** -/
theorem coLocated_step_of_both_left {c : Config n} (hn : 0 < n) {i : Fin n}
    {h : i.val + 1 < n} (hIH : ¬ c.BothLeftApart i h) (hL : c.dir i = Dir.left)
    (hL2 : c.dir (nextIdx i h) = Dir.left) : (c.step hn).CoLocated i h := by
  have hco : c.CoLocated i h := by
    by_contra hnc
    exact hIH ⟨hL, hL2, hnc⟩
  exact coLocated_advance_of_escorting ⟨hco, by rw [hL, hL2]⟩ _

/-! ## What is left of the obstruction

`BothLeftApart` can only appear at a step in one of three ways, and two are now
closed:

1. the **left** drone reverses to leftward — impossible, it would be
   co-located (`coLocated_of_turnsLeft`);
2. **neither** drone reverses — impossible, they were already escorting and
   stay together (`coLocated_step_of_both_left`);
3. the left drone **holds** its leftward heading while the right one
   **reverses** to leftward — still open.

Case 3 is where drone `j`'s left synchronization has to do its work, and it is
positional rather than temporal, which is the useful discovery. In the state
preceding it the pair heads in opposite directions, so the balance is constant;
starting from a separation it is zero, so the two drones are displaced from the
shared boundary by *equal* amounts. Left synchronization caps the left drone's
displacement at `1/n`, hence caps the right drone's at `1/n` too — so the right
drone is at or before `rightEnd (j+1)`. But Lemma 3.1 only permits it to
reverse at or *beyond* that point. The two meet exactly, which pins both drones
to their endpoints, and the left drone must then reverse as well — so it does
not hold its heading after all.

Formalizing that needs one extra invariant alongside `BalanceNonneg`: that the
balance is exactly zero whenever the pair heads in opposite directions with the
left one going left. -/

/-! ## What left synchronization buys

The timing argument behind Lemma 3.2 turns on knowing *exactly when* drone `j`
turns around, not merely that it does. Left synchronization supplies that, and
the paper says so in one line: *"Since it is left synchronized, we know it is at
its left endpoint."*

Here is that line, proved. -/

/-- **A left-synchronized drone turns round exactly at its left endpoint.**

Lemma 3.1 puts the turn at or *before* the endpoint; left synchronization
forbids going beyond it. Together they pin it precisely — which is what makes
the drone's turn time exactly `1/n` after it set off from the boundary, and
hence no later than its right-hand neighbour's. -/
theorem pos_eq_leftEnd_of_turnsRightAt_of_leftSync {c : Config n} (hn : 0 < n)
    {i : Fin n} {k j : ℕ} (hsync : LeftSync c hn i k) (hkj : k ≤ j + 1)
    (ht : TurnsRightAt c hn i j) :
    (c.run hn (j + 1)).pos i = leftEnd i := by
  have hle : (c.run hn (j + 1)).pos i ≤ leftEnd i :=
    pos_le_leftEnd_of_turnsRightAt hn ht
  have hge : leftEnd i ≤ (c.run hn (j + 1)).pos i := hsync (j + 1) hkj
  linarith

/-- Symmetrically, a right-synchronized drone turns round exactly at its right
endpoint. -/
theorem pos_eq_rightEnd_of_turnsLeftAt_of_rightSync {c : Config n} (hn : 0 < n)
    {i : Fin n} {k j : ℕ} (hsync : RightSync c hn i k) (hkj : k ≤ j + 1)
    (ht : TurnsLeftAt c hn i j) :
    (c.run hn (j + 1)).pos i = rightEnd i := by
  have hge : rightEnd i ≤ (c.run hn (j + 1)).pos i :=
    rightEnd_le_pos_of_turnsLeftAt hn ht
  have hle : (c.run hn (j + 1)).pos i ≤ rightEnd i := hsync (j + 1) hkj
  linarith

/-! ## The positional core of case 3

The paper argues Lemma 3.2 by timing. These two lemmas replace that with
arithmetic on interval endpoints, and they are the mathematical content of the
one remaining case.

The setting: the pair has separated and is moving apart, so the balance is
constant and — starting from a separation — **zero**. The two drones are then
displaced from their shared boundary by *equal* amounts. Left synchronization
caps the left drone's displacement at `1/n`, and that caps its partner's at
`1/n` too. But Lemma 3.1 lets the partner reverse only at or *beyond* that very
point. The two constraints meet exactly, and pin both drones. -/

/-- The right-hand drone's own right endpoint is `1/n` beyond the boundary the
pair shares. -/
theorem rightEnd_next_eq (i : Fin n) (h : i.val + 1 < n) :
    rightEnd (nextIdx i h) = commonEnd i + 1 / (n : ℝ) := by
  have h1 : rightEnd (nextIdx i h) - leftEnd (nextIdx i h) = 1 / (n : ℝ) :=
    rightEnd_sub_leftEnd _
  rw [leftEnd_next_eq_commonEnd i h] at h1
  linarith

/-- And the left-hand drone's own left endpoint is `1/n` before it. -/
theorem leftEnd_eq (i : Fin n) :
    leftEnd i = commonEnd i - 1 / (n : ℝ) := by
  have h1 : rightEnd i - leftEnd i = 1 / (n : ℝ) := rightEnd_sub_leftEnd i
  unfold commonEnd
  linarith

/-- **With the balance at zero, left synchronization of the left drone caps
where its partner can be.**

The partner cannot have got past its own right endpoint — which is exactly the
only place Lemma 3.1 would let it turn around. -/
theorem pos_next_le_rightEnd_of_balance_zero {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hbal : c.pairBalance i h = 0)
    (hsync : leftEnd i ≤ c.pos i) :
    c.pos (nextIdx i h) ≤ rightEnd (nextIdx i h) := by
  unfold pairBalance at hbal
  rw [rightEnd_next_eq i h]
  rw [leftEnd_eq i] at hsync
  linarith

/-- **So if the partner does turn, both drones are pinned to their endpoints.**

This is the crux. The partner may only reverse at or beyond its right endpoint
(Lemma 3.1); the balance and left synchronization put it at or before. Equality
follows, and with it the left drone sits exactly on *its* left endpoint — where
it, too, must turn. That is what makes the pair turn together and never both
head left while apart. -/
theorem pinned_of_balance_zero {c : Config n} {i : Fin n} {h : i.val + 1 < n}
    (hbal : c.pairBalance i h = 0) (hsync : leftEnd i ≤ c.pos i)
    (hturn : rightEnd (nextIdx i h) ≤ c.pos (nextIdx i h)) :
    c.pos (nextIdx i h) = rightEnd (nextIdx i h) ∧ c.pos i = leftEnd i := by
  have hle := pos_next_le_rightEnd_of_balance_zero hbal hsync
  have heq : c.pos (nextIdx i h) = rightEnd (nextIdx i h) := le_antisymm hle hturn
  refine ⟨heq, ?_⟩
  unfold pairBalance at hbal
  rw [heq, rightEnd_next_eq i h] at hbal
  rw [leftEnd_eq i]
  linarith

/-! ## The remaining obligation, stated

Everything above is unconditional. What Lemma 3.2 additionally needs is that
the balance, once zero, never goes negative. Stated here as a definition rather
than assumed as a hypothesis, so that it is visible as an open obligation and
cannot be used by accident. -/

/-- The balance of pair `(i, i+1)` never goes negative from step `k` on.

This is the missing half of Lemma 3.2. The danger is both drones heading left
at once, which drives the balance down at rate 2; ruling it out needs the
paper's timing argument about how their turns interleave. -/
def BalanceNonneg (c : Config n) (hn : 0 < n) (i : Fin n) (h : i.val + 1 < n)
    (k : ℕ) : Prop :=
  ∀ j, k ≤ j → 0 ≤ (c.run hn j).pairBalance i h

/-- **The invariance, reduced to the one bad class.**

If a pair with nonnegative balance is never both-heading-left-while-apart, its
balance stays nonnegative forever. So all that remains of Lemma 3.2 is to rule
out that single configuration — which is where drone `j`'s left
synchronization finally earns its keep, by pinning down *when* `j` turns. -/
theorem balanceNonneg_of_never_bothLeftApart {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (hb0 : 0 ≤ (c.run hn k).pairBalance i h)
    (hnever : ∀ j, k ≤ j → ¬ (c.run hn j).BothLeftApart i h) :
    BalanceNonneg c hn i h k := by
  have key : ∀ m : ℕ, 0 ≤ (c.run hn (k + m)).pairBalance i h := by
    intro m
    induction m with
    | zero => exact hb0
    | succ m ih =>
      have hstep : c.run hn (k + (m + 1)) = (c.run hn (k + m)).step hn := rfl
      rw [hstep]
      exact pairBalance_nonneg_step hn (invariant_run hn hi (k + m)) ih
        (hnever (k + m) (by omega))
  intro j hj
  obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
  exact key m

/-- **Lemma 3.2, modulo the balance obligation.**

Given that the balance stays nonnegative, the right-hand drone of the pair is
left synchronized. Combined with `pairBalance_eq_zero_of_atSeparation` — a
separation starts the balance at exactly zero — this is the whole of Lemma 3.2
except for the invariance argument. -/
theorem leftSync_of_balanceNonneg {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (hb : BalanceNonneg c hn i h k) :
    LeftSync c hn (nextIdx i h) k := by
  intro j hj
  exact leftEnd_le_pos_of_pairBalance (hb j hj)
    ((invariant_run hn hi j).adjOrdered i h)

end Config

end DPSS
