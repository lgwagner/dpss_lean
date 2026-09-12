/-
# DPSS — Lemmas 3.3 and 3.4

Two corollaries Avigad–van Doorn draw from Lemma 3.2, each giving a
configuration from which the right-hand drone of a pair is already left
synchronized:

> **Lemma 3.3.** If `j` and `j+1` are together moving left and `j` is left
> synchronized, then so is `j+1`.
>
> **Lemma 3.4.** If `j` is at or beyond its right endpoint moving right and is
> left synchronized, then `j+1` is left synchronized.

## How the balance makes them short

`PairBalance.lean` reduced left synchronization of `j+1` to one number staying
nonnegative. So each lemma needs only its *starting* configuration to put the
balance at or above zero — and in both cases that falls out at once:

* **Lemma 3.3.** An escorting pair's balance is exactly twice its separation
  deadline, and escort coherence — proved unconditionally in `Coherence.lean` —
  says that deadline is never in the past. So the balance is nonnegative
  because the scheduler makes it so.
* **Lemma 3.4.** If `j` has reached its right endpoint, which *is* the shared
  boundary, then ordering puts `j+1` at or beyond it too. Both terms of the
  balance are nonnegative separately.

Both then inherit whatever is true of `BalanceNonneg`, exactly as Lemma 3.2
does. They are stated in that conditional form rather than assumed.

## Reference

Avigad–van Doorn, arXiv:2008.04262, Lemmas 3.3 and 3.4.
-/

import Dpss.NonZenoProof

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Two ways to start with a nonnegative balance -/

/-- **An escorting pair heading left has a nonnegative balance.**

Not an accident of the configuration: the balance is twice the separation
deadline, and the scheduler never lets that deadline fall into the past. -/
theorem pairBalance_nonneg_of_escorting_left {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hec : c.EscortsCoherent) (he : c.Escorting i h)
    (hL : c.dir i = Dir.left) : 0 ≤ c.pairBalance i h := by
  rw [pairBalance_eq_two_mul_separationTime he hL]
  have := hec i h he
  linarith

/-- **A pair whose left drone has reached the shared boundary has a
nonnegative balance.** Ordering carries the right drone past it too, so both
terms are nonnegative separately. -/
theorem pairBalance_nonneg_of_pos_ge {c : Config n} {i : Fin n}
    {h : i.val + 1 < n} (hord : 0 ≤ c.gap i h) (hge : commonEnd i ≤ c.pos i) :
    0 ≤ c.pairBalance i h := by
  unfold pairBalance
  unfold gap at hord
  linarith

/-! ## The lemmas

Each is Lemma 3.2 applied from a configuration that supplies the balance for
free, so each carries the same `BalanceNonneg` obligation and nothing more. -/

/-- **Lemma 3.3.** A pair escorting leftward, with the left drone left
synchronized, has its right drone left synchronized too.

Conditional on nothing but `BothLeftApart` — the single obstruction that
Lemma 3.2 also waits on. The starting balance comes free from escort
coherence. -/
theorem leftSync_of_escorting_left {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (he : (c.run hn k).Escorting i h)
    (hL : (c.run hn k).dir i = Dir.left)
    (hnever : ∀ j, k ≤ j → ¬ (c.run hn j).BothLeftApart i h) :
    LeftSync c hn (nextIdx i h) k :=
  leftSync_of_balanceNonneg hn hi
    (balanceNonneg_of_never_bothLeftApart hn hi
      (pairBalance_nonneg_of_escorting_left
        (invariant_run hn hi k).escortsCoherent he hL) hnever)

/-- **Lemma 3.4.** If the left drone has reached the boundary it shares with
its neighbour and is left synchronized, the neighbour is left synchronized.

Again conditional only on `BothLeftApart`; the starting balance comes free
from ordering. -/
theorem leftSync_of_pos_ge {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (hge : commonEnd i ≤ (c.run hn k).pos i)
    (hnever : ∀ j, k ≤ j → ¬ (c.run hn j).BothLeftApart i h) :
    LeftSync c hn (nextIdx i h) k :=
  leftSync_of_balanceNonneg hn hi
    (balanceNonneg_of_never_bothLeftApart hn hi
      (pairBalance_nonneg_of_pos_ge ((invariant_run hn hi k).adjOrdered i h) hge)
      hnever)

/-- **Lemma 3.2 in the same form**, for comparison: a pair that has just
separated at their shared boundary starts with balance exactly zero, so the
right drone is left synchronized on the same single condition. -/
theorem leftSync_of_atSeparation {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {h : i.val + 1 < n} {k : ℕ}
    (hs : (c.run hn k).AtSeparation i h)
    (hnever : ∀ j, k ≤ j → ¬ (c.run hn j).BothLeftApart i h) :
    LeftSync c hn (nextIdx i h) k :=
  leftSync_of_balanceNonneg hn hi
    (balanceNonneg_of_never_bothLeftApart hn hi
      (le_of_eq (pairBalance_eq_zero_of_atSeparation hs).symm) hnever)

/-! ## `have met`

Lemmas 3.5, 3.6 and 3.7 are all phrased in terms of a pair having *met* by some
time. Nothing so far models that, so here it is.

The paper says drones `j` and `j+1` have met by time `t` if they started
together moving the same way, or have been involved in a meet or bounce event.
Both cases are instances of one thing — **the pair was co-located at some
moment no later than `t`** — so that is the definition used, and it is the
weaker and therefore more useful one.

A note for whoever takes this further. The ACL2 team reported that phrasing
this over execution *history* "drew heavily on human intuition about system
behaviour and was difficult to work with in a mechanized proof", and that
recasting it as a **locally checkable** predicate over a drone and its
immediate neighbour was what made their development tractable. The definition
below is the history-shaped one. If Lemma 3.5 or 3.7 becomes unwieldy, that is
the first thing to change. -/

/-- Drones `i` and `i+1` have been co-located at some moment at or before time
`T`. -/
def HaveMetBy (c : Config n) (hn : 0 < n) (i : Fin n) (h : i.val + 1 < n)
    (T : ℝ) : Prop :=
  ∃ m : ℕ, (c.run hn m).time ≤ T ∧ (c.run hn m).CoLocated i h

/-- Having met by one time, a pair has met by any later one. -/
theorem haveMetBy_mono {c : Config n} {hn : 0 < n} {i : Fin n}
    {h : i.val + 1 < n} {T T' : ℝ} (hTT : T ≤ T')
    (hm : HaveMetBy c hn i h T) : HaveMetBy c hn i h T' := by
  obtain ⟨m, hm1, hm2⟩ := hm
  exact ⟨m, le_trans hm1 hTT, hm2⟩

/-- A pair that starts co-located has met at once. -/
theorem haveMetBy_of_start {c : Config n} (hn : 0 < n) {i : Fin n}
    {h : i.val + 1 < n} (hco : c.CoLocated i h) :
    HaveMetBy c hn i h c.time :=
  ⟨0, le_of_eq rfl, hco⟩

/-- Meeting is what a `meetTime` deadline delivers: if an approaching pair's
deadline is the one that sets the step, they have met by the end of it. -/
theorem haveMetBy_of_meet_deadline {c : Config n} (hn : 0 < n) {i : Fin n}
    {h : i.val + 1 < n} (hA : c.Approaching i h)
    (hmin : c.timeToNextEvent hn = c.meetTime i h) :
    HaveMetBy c hn i h (c.run hn 1).time := by
  refine ⟨1, le_of_eq rfl, ?_⟩
  have := (meet_due_of_meet_deadline hn hA hmin).1
  exact this

end Config

end DPSS
