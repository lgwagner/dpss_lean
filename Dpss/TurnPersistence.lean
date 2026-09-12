/-
# DPSS — Lemma 3.6: a drone heading left has been heading left

> **Lemma 3.6.** Suppose at time `t` drone `j` is moving left and is not
> together with `j+1`, and that the two have met. Let `t'` be the last time
> before `t` that they bounced or separated. Then `j` has been moving left
> since `t'`.

## Why it is short here

The paper's proof: *"If at some point between `t'` and `t` drone `j` was moving
to the right, something must have turned it to the left. But that can only have
been a meet or separation or bounce event"* — all of which put the pair
together, contradicting `t'` being the **last** such moment.

`PairBalance.lean` already proved the load-bearing step, for its own reasons:
**a drone that reverses to leftward is co-located with its right-hand
neighbour** (`coLocated_of_turnsLeft`). Whatever can reverse a rightward drone
— a meet, a separation, or the right border — leaves it on top of its
neighbour.

So over any stretch in which the pair is never together, drone `j` never turns
left. And a drone found heading left at the end of such a stretch must have
been heading left throughout it: it cannot have turned left (just shown), and
had it turned right it would still be heading right.

## Reference

Avigad–van Doorn, arXiv:2008.04262, Lemma 3.6.
-/

import Dpss.LeftSyncLemmas

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-- **A pair that is never together is a pair whose left drone never turns
left.** -/
theorem not_turnsLeftAt_of_never_coLocated {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {h : i.val + 1 < n} {a b : ℕ}
    (hnc : ∀ p, a < p → p ≤ b → ¬ (c.run hn p).CoLocated i h) :
    ∀ p, a ≤ p → p < b → ¬ TurnsLeftAt c hn i p := by
  intro p hp1 hp2 ht
  have hinv := invariant_run hn hi (p + 1)
  have hco : (c.run hn (p + 1)).CoLocated i h :=
    coLocated_of_turnsLeft (c := (c.run hn p).advance
        ((c.run hn p).timeToNextEvent hn))
      hinv.onPerimeter (ordered_of_adjOrdered hinv.adjOrdered) h ⟨ht.1, ht.2⟩
  exact hnc (p + 1) (by omega) (by omega) hco

/-- **A drone heading left at the end of a turn-free stretch was heading left
throughout it.** It cannot have turned left, and had it turned right it would
still be heading right. -/
theorem dir_left_of_no_turnsLeft {c : Config n} (hn : 0 < n) {i : Fin n}
    {a b : ℕ} (hab : a ≤ b)
    (hno : ∀ p, a ≤ p → p < b → ¬ TurnsLeftAt c hn i p)
    (hb : (c.run hn b).dir i = Dir.left) :
    ∀ p, a ≤ p → p ≤ b → (c.run hn p).dir i = Dir.left := by
  have key : ∀ q : ℕ, q ≤ b - a → (c.run hn (b - q)).dir i = Dir.left := by
    intro q
    induction q with
    | zero => intro _; simpa using hb
    | succ q ih =>
      intro hq
      have hprev := ih (by omega)
      have heq : (b - (q + 1)) + 1 = b - q := by omega
      by_contra hne
      have hR : (c.run hn (b - (q + 1))).dir i = Dir.right := by
        rcases Dir.eq_left_or_right ((c.run hn (b - (q + 1))).dir i) with hx | hx
        · exact absurd hx hne
        · exact hx
      exact hno (b - (q + 1)) (by omega) (by omega)
        ⟨hR, by rw [heq]; exact hprev⟩
  intro p hp1 hp2
  have hk := key (b - p) (by omega)
  rwa [show b - (b - p) = p from by omega] at hk

/-- **Lemma 3.6.** If the pair has not been together since step `a`, and drone
`i` is heading left at step `b`, then it has been heading left ever since `a`.

The paper phrases `a` as "the last time before `t` that they bounced or
separated"; here it is any step after which they have not been together, which
is the property the proof actually uses. -/
theorem dir_left_since_of_never_coLocated {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {h : i.val + 1 < n} {a b : ℕ} (hab : a ≤ b)
    (hnc : ∀ p, a < p → p ≤ b → ¬ (c.run hn p).CoLocated i h)
    (hb : (c.run hn b).dir i = Dir.left) :
    ∀ p, a ≤ p → p ≤ b → (c.run hn p).dir i = Dir.left :=
  dir_left_of_no_turnsLeft hn hab
    (not_turnsLeftAt_of_never_coLocated hn hi hnc) hb

end Config

end DPSS
