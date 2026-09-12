/-
# DPSS — synchronization, and the statement of the convergence theorem

Avigad–van Doorn define the target property as a *safety* property with a
"from now on" quantifier:

> a drone is **left synchronized** at time `t` if beyond that point it never
> goes to the left of its left endpoint, and similarly for right synchronized.
> A drone is **synchronized** at time `t` if it is left and right synchronized.

The team is synchronized when every drone is, and Theorem 2.1 says that happens
by time `2 − 1/n`.

## Why checking only at event times is enough

The definitions below quantify over **run indices**, not over all real times.
That is not a weakening. Between consecutive events every drone flies in a
straight line at constant speed, so its position over a step is monotone and
its extremes are attained at the two endpoints. A drone that is inside its
interval at every event time is therefore inside it at every time whatsoever.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2 and Theorem 2.1.
-/

import Dpss.NonZeno

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## The perimeter is never left

Before synchronization, a much cruder containment: drones stay on `[0,1]`. This
is the first genuine *invariant of the running system* proved here — earlier
results were about single steps in isolation. -/

/-- **A step keeps every drone on the perimeter.**

The reason is exactly the `borderTime` term in `droneNextTime`: the step never
flies for longer than any drone's time to the border it is heading for, so
nobody can overshoot the edge. -/
theorem onPerimeter_step {c : Config n} (hn : 0 < n) (hp : c.OnPerimeter)
    (ha : c.AdjOrdered) (hec : c.EscortsCoherent) :
    (c.step hn).OnPerimeter := by
  intro i
  have hdt : 0 ≤ c.timeToNextEvent hn := timeToNextEvent_nonneg hn hp ha hec
  have hle : c.timeToNextEvent hn ≤ c.borderTime i :=
    le_trans (timeToNextEvent_le hn i) (droneNextTime_le_borderTime c i)
  rcases Dir.eq_left_or_right (c.dir i) with hd | hd
  · rw [borderTime_of_left hd] at hle
    have h2 := (hp i).2
    constructor
    · rw [step_pos, hd, Dir.sign_left]; linarith
    · rw [step_pos, hd, Dir.sign_left]; linarith
  · rw [borderTime_of_right hd] at hle
    have h1 := (hp i).1
    constructor
    · rw [step_pos, hd, Dir.sign_right]; linarith
    · rw [step_pos, hd, Dir.sign_right]; linarith

/-! ## Synchronization -/

/-- Drone `i` is **left synchronized** from step `k` on: from then on it never
goes left of its own left endpoint. -/
def LeftSync (c : Config n) (hn : 0 < n) (i : Fin n) (k : ℕ) : Prop :=
  ∀ j, k ≤ j → leftEnd i ≤ (c.run hn j).pos i

/-- Drone `i` is **right synchronized** from step `k` on. -/
def RightSync (c : Config n) (hn : 0 < n) (i : Fin n) (k : ℕ) : Prop :=
  ∀ j, k ≤ j → (c.run hn j).pos i ≤ rightEnd i

/-- Drone `i` is **synchronized**: confined to its own interval from `k` on. -/
def Sync (c : Config n) (hn : 0 < n) (i : Fin n) (k : ℕ) : Prop :=
  LeftSync c hn i k ∧ RightSync c hn i k

/-- The whole team is synchronized from step `k` on. This is the optimal
surveillance pattern: each drone confined to its own segment. -/
def AllSync (c : Config n) (hn : 0 < n) (k : ℕ) : Prop :=
  ∀ i : Fin n, Sync c hn i k

/-- Synchronization is inherited by later times — it is a "from now on"
property, so pushing the start point forward only weakens it. -/
theorem leftSync_mono {c : Config n} {hn : 0 < n} {i : Fin n} {k k' : ℕ}
    (hk : k ≤ k') (h : LeftSync c hn i k) : LeftSync c hn i k' :=
  fun j hj => h j (le_trans hk hj)

theorem rightSync_mono {c : Config n} {hn : 0 < n} {i : Fin n} {k k' : ℕ}
    (hk : k ≤ k') (h : RightSync c hn i k) : RightSync c hn i k' :=
  fun j hj => h j (le_trans hk hj)

theorem sync_mono {c : Config n} {hn : 0 < n} {i : Fin n} {k k' : ℕ}
    (hk : k ≤ k') (h : Sync c hn i k) : Sync c hn i k' :=
  ⟨leftSync_mono hk h.1, rightSync_mono hk h.2⟩

/-! ## The goal

Stated as a `Prop`-valued definition rather than a `theorem` with a `sorry`,
so that the repository stays provably free of `sorry` (CI enforces this) while
still recording precisely what is being aimed at. -/

/-- **Theorem 2.1 of Avigad–van Doorn, as a formal statement.**

> Assuming all the drones have the correct estimates, they are all synchronized
> at time `2 − 1/n`.

Read: at every event at or after `2 − 1/n` from the start, every drone is
inside its own assigned interval. "Correct estimates" is not a hypothesis here
because this development models Algorithm A throughout — estimates are absent
from `Config` precisely because they are assumed correct.

The bound is **sharp**: the paper exhibits a configuration attaining it, so no
proof that loses even an `ε` can close. -/
def ConvergesBy (c : Config n) (hn : 0 < n) : Prop :=
  ∀ (i : Fin n) (j : ℕ),
    c.time + (2 - 1 / (n : ℝ)) ≤ (c.run hn j).time →
      leftEnd i ≤ (c.run hn j).pos i ∧ (c.run hn j).pos i ≤ rightEnd i

/-! ## The trivial case

`n = 1` is the one case the paper calls trivial, and it is: the single drone's
interval *is* the whole perimeter, so staying inside it and staying on the
perimeter are the same statement. Worth having as a check that the definitions
are not vacuous or mis-signed. -/

theorem leftEnd_eq_zero_of_one (i : Fin 1) : leftEnd i = 0 := by
  have h : i.val = 0 := by have := i.isLt; omega
  unfold leftEnd; rw [h]; simp

theorem rightEnd_eq_one_of_one (i : Fin 1) : rightEnd i = 1 := by
  have h : i.val = 0 := by have := i.isLt; omega
  unfold rightEnd; rw [h]; norm_num

/-- With a single drone, synchronization is exactly staying on the perimeter. -/
theorem sync_of_one (c : Config 1) (hn : 0 < 1) (i : Fin 1) (k : ℕ)
    (hp : ∀ j, k ≤ j → (c.run hn j).OnPerimeter) : Sync c hn i k := by
  constructor
  · intro j hj
    rw [leftEnd_eq_zero_of_one i]
    exact (hp j hj i).1
  · intro j hj
    rw [rightEnd_eq_one_of_one i]
    exact (hp j hj i).2

/-- And therefore a single drone converges immediately, well inside the bound.
The `n = 1` instance of Theorem 2.1. -/
theorem convergesBy_of_one (c : Config 1) (hn : 0 < 1)
    (hp : ∀ j, (c.run hn j).OnPerimeter) : ConvergesBy c hn := by
  intro i j _
  refine ⟨?_, ?_⟩
  · rw [leftEnd_eq_zero_of_one i]; exact (hp j i).1
  · rw [rightEnd_eq_one_of_one i]; exact (hp j i).2

end Config

end DPSS
