/-
# DPSS — towards non-Zeno

The plan, in one line: **a drone that crosses its own interval spends at least
`1/n` of time doing it**, and `Turning.lean` showed every pair of consecutive
turns brackets exactly such a crossing. So turns cannot bunch up, and neither
can events.

This file supplies the run-level half of that argument:

* `pos_sub_eq_of_dirConst` — while a drone holds its heading, its position
  advances by exactly the elapsed time. Pure telescoping over the run.
* `time_advance_of_crossing` — therefore, crossing from one endpoint to the
  other costs at least `1/n` of time.

The counting step that completes non-Zeno — every event turns at least one
drone, each drone turns at most once per `1/n`, so only finitely many events
fit in a bounded interval — is in `NonZenoProof.lean`, which is where `nonZeno`
itself is proved.

## Careful: when does a turn actually happen?

A step flies first and turns afterwards, so the configuration at which `newDir`
is evaluated is `advance c dt`, not `c`. Concretely, if drone `i` turns during
step `k` then

* the heading it *flew* with is `(run k).dir i`,
* the position it turned *at* is `(run (k+1)).pos i`,
* the heading it leaves with is `(run (k+1)).dir i`.

Getting this off by one would silently wreck every bound below, so the turn
predicates are stated on run indices and connected to `Turning.lean` explicitly.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2.
-/

import Dpss.Turning

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

@[simp] theorem step_dir (c : Config n) (hn : 0 < n) (i : Fin n) :
    (c.step hn).dir i = (c.advance (c.timeToNextEvent hn)).newDir i := rfl

@[simp] theorem advance_newDir_dir (c : Config n) (dt : ℝ) (i : Fin n) :
    (c.advance dt).dir i = c.dir i := rfl

/-! ## Turning, indexed by step number -/

/-- Drone `i` reverses to rightward during step `k`. -/
def TurnsRightAt (c : Config n) (hn : 0 < n) (i : Fin n) (k : ℕ) : Prop :=
  (c.run hn k).dir i = Dir.left ∧ (c.run hn (k + 1)).dir i = Dir.right

/-- Drone `i` reverses to leftward during step `k`. -/
def TurnsLeftAt (c : Config n) (hn : 0 < n) (i : Fin n) (k : ℕ) : Prop :=
  (c.run hn k).dir i = Dir.right ∧ (c.run hn (k + 1)).dir i = Dir.left

/-- **A drone that turns rightward during step `k` is at or before its left
endpoint when it does.** `Turning.lean`'s Lemma 3.1, transported onto run
indices — note the position is the one *after* the flight. -/
theorem pos_le_leftEnd_of_turnsRightAt {c : Config n} (hn : 0 < n) {i : Fin n}
    {k : ℕ} (ht : TurnsRightAt c hn i k) :
    (c.run hn (k + 1)).pos i ≤ leftEnd i :=
  pos_le_leftEnd_of_turnsRight (c := (c.run hn k).advance
      ((c.run hn k).timeToNextEvent hn)) ⟨ht.1, ht.2⟩

/-- And symmetrically for a leftward turn. -/
theorem rightEnd_le_pos_of_turnsLeftAt {c : Config n} (hn : 0 < n) {i : Fin n}
    {k : ℕ} (ht : TurnsLeftAt c hn i k) :
    rightEnd i ≤ (c.run hn (k + 1)).pos i :=
  rightEnd_le_pos_of_turnsLeft (c := (c.run hn k).advance
      ((c.run hn k).timeToNextEvent hn)) ⟨ht.1, ht.2⟩

/-! ## Motion along a run -/

/-- **While a drone holds its heading, position advances exactly as time does.**

Each individual step moves the drone by `sign · dt` and the clock by `dt`; with
the heading fixed the two telescope. Unit speed is doing the work — this is
where the normalization "one unit of distance per unit of time" is cashed in. -/
theorem pos_sub_eq_of_dirConst {c : Config n} (hn : 0 < n) (i : Fin n) (a m : ℕ)
    (hconst : ∀ j, a ≤ j → j < a + m → (c.run hn j).dir i = (c.run hn a).dir i) :
    (c.run hn (a + m)).pos i - (c.run hn a).pos i
      = ((c.run hn a).dir i).sign
        * ((c.run hn (a + m)).time - (c.run hn a).time) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlt : a + m < a + (m + 1) := by omega
    have hdm : (c.run hn (a + m)).dir i = (c.run hn a).dir i :=
      hconst (a + m) (by omega) hlt
    have hih : (c.run hn (a + m)).pos i - (c.run hn a).pos i
        = ((c.run hn a).dir i).sign
          * ((c.run hn (a + m)).time - (c.run hn a).time) :=
      ih (fun j hj1 hj2 => hconst j hj1 (by omega))
    have hs : c.run hn (a + (m + 1)) = (c.run hn (a + m)).step hn := rfl
    rw [hs, step_pos, step_time, hdm]
    ring_nf
    ring_nf at hih
    linarith

/-- **Crossing the interval costs at least `1/n` of time.**

If a drone starts at or before its left endpoint, finishes at or beyond its
right endpoint, and heads right throughout, then it covered at least the width
of its interval — and at unit speed that is at least `1/n` of time. -/
theorem time_advance_of_crossing {c : Config n} (hn : 0 < n) {i : Fin n}
    {a m : ℕ}
    (hstart : (c.run hn a).pos i ≤ leftEnd i)
    (hend : rightEnd i ≤ (c.run hn (a + m)).pos i)
    (hconst : ∀ j, a ≤ j → j < a + m → (c.run hn j).dir i = Dir.right)
    (ha : (c.run hn a).dir i = Dir.right) :
    (c.run hn a).time + 1 / (n : ℝ) ≤ (c.run hn (a + m)).time := by
  have hkey := pos_sub_eq_of_dirConst hn i a m
    (fun j hj1 hj2 => by rw [hconst j hj1 hj2, ha])
  rw [ha, Dir.sign_right, one_mul] at hkey
  have hw : rightEnd i - leftEnd i = 1 / (n : ℝ) := rightEnd_sub_leftEnd i
  linarith

/-- The mirror image: crossing leftward costs just as much. -/
theorem time_advance_of_crossing_left {c : Config n} (hn : 0 < n) {i : Fin n}
    {a m : ℕ}
    (hstart : rightEnd i ≤ (c.run hn a).pos i)
    (hend : (c.run hn (a + m)).pos i ≤ leftEnd i)
    (hconst : ∀ j, a ≤ j → j < a + m → (c.run hn j).dir i = Dir.left)
    (ha : (c.run hn a).dir i = Dir.left) :
    (c.run hn a).time + 1 / (n : ℝ) ≤ (c.run hn (a + m)).time := by
  have hkey := pos_sub_eq_of_dirConst hn i a m
    (fun j hj1 hj2 => by rw [hconst j hj1 hj2, ha])
  rw [ha, Dir.sign_left] at hkey
  have hw : rightEnd i - leftEnd i = 1 / (n : ℝ) := rightEnd_sub_leftEnd i
  linarith

end Config

end DPSS
