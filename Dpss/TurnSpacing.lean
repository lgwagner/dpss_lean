/-
# DPSS — turns of one drone are spaced out in time

**A3** of the work package, and the last geometric ingredient of non-Zeno.

`Turning.lean` established *where* a drone may turn: rightward drones reverse
only at or beyond their right endpoint, leftward drones only at or before their
left endpoint. `NonZeno.lean` established that crossing between those two
points costs at least `1/n` of time. This file joins them along a run:

> **between two consecutive turns of the same drone, at least `1/n` of time
> elapses.**

Together with `someDroneTurns_step` — every step reverses somebody — this is
everything non-Zeno needs except the counting argument itself: `k` steps force
`k` turns spread over only `n` drones, so some drone turns often, and its turns
are spaced, so the clock must have advanced.

## Reference

Avigad–van Doorn, arXiv:2008.04262 §2.
-/

import Dpss.EventsTurn

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-- Drone `i` reverses during step `k`. -/
def TurnsAt (c : Config n) (hn : 0 < n) (i : Fin n) (k : ℕ) : Prop :=
  (c.run hn (k + 1)).dir i ≠ (c.run hn k).dir i

/-- A drone that does not turn keeps its heading — so across a stretch with no
turns, the heading is constant. -/
theorem dir_const_of_no_turns {c : Config n} (hn : 0 < n) (i : Fin n) {a m : ℕ}
    (hmid : ∀ j, a ≤ j → j < a + m → ¬ TurnsAt c hn i j) :
    ∀ j, a ≤ j → j ≤ a + m → (c.run hn j).dir i = (c.run hn a).dir i := by
  have key : ∀ p : ℕ, p ≤ m → (c.run hn (a + p)).dir i = (c.run hn a).dir i := by
    intro p
    induction p with
    | zero => intro _; rfl
    | succ p ih =>
      intro hp
      have hprev := ih (by omega)
      have hnt : ¬ TurnsAt c hn i (a + p) := hmid (a + p) (by omega) (by omega)
      unfold TurnsAt at hnt
      simp only [not_not] at hnt
      rw [show a + (p + 1) = (a + p) + 1 from rfl, hnt, hprev]
  intro j hj1 hj2
  obtain ⟨p, rfl⟩ : ∃ p, j = a + p := ⟨j - a, by omega⟩
  exact key p (by omega)

/-- **Consecutive turns of one drone are at least `1/n` apart in time.**

Between them the drone holds a single heading and crosses its whole assigned
interval — from one endpoint to the other — because that is the only place it
is allowed to reverse. At unit speed that crossing costs `1/n`. -/
theorem time_gap_of_consecutive_turns {c : Config n} (hn : 0 < n) (i : Fin n)
    {a b : ℕ} (hab : a < b) (ha : TurnsAt c hn i a) (hb : TurnsAt c hn i b)
    (hmid : ∀ j, a < j → j < b → ¬ TurnsAt c hn i j) :
    (c.run hn (a + 1)).time + 1 / (n : ℝ) ≤ (c.run hn (b + 1)).time := by
  -- the heading is fixed from just after the first turn to the second
  -- no turn strictly between them, so the heading is fixed on `[a+1, b]`
  have hmid' : ∀ j, a + 1 ≤ j → j < (a + 1) + (b - a - 1) → ¬ TurnsAt c hn i j := by
    intro j hj1 hj2
    exact hmid j (by omega) (by omega)
  have hconst' := dir_const_of_no_turns hn i hmid'
  have hconst : ∀ j, a + 1 ≤ j → j ≤ b →
      (c.run hn j).dir i = (c.run hn (a + 1)).dir i := by
    intro j hj1 hj2
    exact hconst' j hj1 (by omega)
  have hb1 : (a + 1) + (b - a) = b + 1 := by omega
  rcases Dir.eq_left_or_right ((c.run hn (a + 1)).dir i) with hL | hR
  · -- it left the first turn heading left, so it is crossing leftward
    have hstart : rightEnd i ≤ (c.run hn (a + 1)).pos i := by
      refine rightEnd_le_pos_of_turnsLeftAt hn ⟨?_, hL⟩
      rcases Dir.eq_left_or_right ((c.run hn a).dir i) with hx | hx
      · exact absurd (by rw [hL, hx]) ha
      · exact hx
    have hend : (c.run hn (b + 1)).pos i ≤ leftEnd i := by
      refine pos_le_leftEnd_of_turnsRightAt hn ⟨?_, ?_⟩
      · rw [hconst b (by omega) (by omega), hL]
      · rcases Dir.eq_left_or_right ((c.run hn (b + 1)).dir i) with hx | hx
        · exact absurd (by rw [hx, hconst b (by omega) (by omega), hL]) hb
        · exact hx
    have := time_advance_of_crossing_left hn (a := a + 1) (m := b - a)
      (by rw [hb1] at *; exact hstart) (by rw [hb1]; exact hend)
      (fun j hj1 hj2 => by rw [hconst j hj1 (by omega), hL]) hL
    rw [hb1] at this
    exact this
  · -- or heading right, and crossing rightward
    have hstart : (c.run hn (a + 1)).pos i ≤ leftEnd i := by
      refine pos_le_leftEnd_of_turnsRightAt hn ⟨?_, hR⟩
      rcases Dir.eq_left_or_right ((c.run hn a).dir i) with hx | hx
      · exact hx
      · exact absurd (by rw [hR, hx]) ha
    have hend : rightEnd i ≤ (c.run hn (b + 1)).pos i := by
      refine rightEnd_le_pos_of_turnsLeftAt hn ⟨?_, ?_⟩
      · rw [hconst b (by omega) (by omega), hR]
      · rcases Dir.eq_left_or_right ((c.run hn (b + 1)).dir i) with hx | hx
        · exact hx
        · exact absurd (by rw [hx, hconst b (by omega) (by omega), hR]) hb
    have := time_advance_of_crossing hn (a := a + 1) (m := b - a)
      hstart (by rw [hb1]; exact hend)
      (fun j hj1 hj2 => by rw [hconst j hj1 (by omega), hR]) hR
    rw [hb1] at this
    exact this

end Config

end DPSS
