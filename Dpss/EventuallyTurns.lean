/-
# DPSS — every drone eventually turns around

A step towards **Lemma 3.5** (*every adjacent pair has met by time 1*). Its
proof opens with *"eventually `j` turns around at or before it reaches 0, and
`j+1` turns around at or before it reaches 1"* — taken for granted, as it
should be on paper.

Formally it needs an argument, and it is a satisfying one because it is where
**non-Zeno** finally pays for itself beyond being a headline result:

* A drone that never turned would hold one heading forever. Position then
  tracks elapsed time exactly (`pos_sub_eq_of_dirConst`).
* Non-Zeno says elapsed time is **unbounded**.
* So the drone would leave the perimeter — which `onPerimeter_run` forbids.

Without non-Zeno the clock could stall and the drone sit still forever, never
turning and never leaving `[0,1]`. So this is not a lemma that could have been
proved earlier.

## Reference

Avigad–van Doorn, arXiv:2008.04262, Lemma 3.5.
-/

import Dpss.Reachable

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-- **A drone heading left must eventually head right.** Otherwise it would
walk off the left end of the perimeter, since the clock does not stall. -/
theorem exists_dir_right_of_dir_left {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {k : ℕ}
    (hL : (c.run hn k).dir i = Dir.left) :
    ∃ m, k ≤ m ∧ (c.run hn m).dir i = Dir.right := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hall : ∀ m, k ≤ m → (c.run hn m).dir i = Dir.left := by
    intro m hm
    rcases Dir.eq_left_or_right ((c.run hn m).dir i) with hx | hx
    · exact hx
    · exact absurd hx (hcon m hm)
  obtain ⟨q, hq⟩ := nonZeno hn hi ((c.run hn k).time + 1)
  have hqk : k ≤ q := by
    by_contra hlt
    have hle : q ≤ k := by omega
    have := time_mono_run' hn hi hle
    linarith
  obtain ⟨p, rfl⟩ : ∃ p, q = k + p := ⟨q - k, by omega⟩
  have hconst : ∀ j, k ≤ j → j < k + p → (c.run hn j).dir i = (c.run hn k).dir i := by
    intro j hj1 _
    rw [hall j hj1, hL]
  have hkey := pos_sub_eq_of_dirConst hn i k p hconst
  rw [hL, Dir.sign_left] at hkey
  have hp0 : 0 ≤ (c.run hn (k + p)).pos i := (onPerimeter_run hn hi (k + p) i).1
  have hp1 : (c.run hn k).pos i ≤ 1 := (onPerimeter_run hn hi k i).2
  linarith

/-- **And a drone heading right must eventually head left**, or it would walk
off the right end. -/
theorem exists_dir_left_of_dir_right {c : Config n} (hn : 0 < n)
    (hi : c.Invariant) {i : Fin n} {k : ℕ}
    (hR : (c.run hn k).dir i = Dir.right) :
    ∃ m, k ≤ m ∧ (c.run hn m).dir i = Dir.left := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hall : ∀ m, k ≤ m → (c.run hn m).dir i = Dir.right := by
    intro m hm
    rcases Dir.eq_left_or_right ((c.run hn m).dir i) with hx | hx
    · exact absurd hx (hcon m hm)
    · exact hx
  obtain ⟨q, hq⟩ := nonZeno hn hi ((c.run hn k).time + 1)
  have hqk : k ≤ q := by
    by_contra hlt
    have hle : q ≤ k := by omega
    have := time_mono_run' hn hi hle
    linarith
  obtain ⟨p, rfl⟩ : ∃ p, q = k + p := ⟨q - k, by omega⟩
  have hconst : ∀ j, k ≤ j → j < k + p → (c.run hn j).dir i = (c.run hn k).dir i := by
    intro j hj1 _
    rw [hall j hj1, hR]
  have hkey := pos_sub_eq_of_dirConst hn i k p hconst
  rw [hR, Dir.sign_right] at hkey
  have hp1 : (c.run hn (k + p)).pos i ≤ 1 := (onPerimeter_run hn hi (k + p) i).2
  have hp0 : 0 ≤ (c.run hn k).pos i := (onPerimeter_run hn hi k i).1
  linarith

/-- **Every drone turns, whichever way it starts.** -/
theorem exists_turn {c : Config n} (hn : 0 < n) (hi : c.Invariant) (i : Fin n)
    (k : ℕ) : ∃ m, k ≤ m ∧ (c.run hn m).dir i ≠ (c.run hn k).dir i := by
  rcases Dir.eq_left_or_right ((c.run hn k).dir i) with hL | hR
  · obtain ⟨m, hm, hd⟩ := exists_dir_right_of_dir_left hn hi hL
    exact ⟨m, hm, by rw [hd, hL]; exact fun hc => Dir.noConfusion hc⟩
  · obtain ⟨m, hm, hd⟩ := exists_dir_left_of_dir_right hn hi hR
    exact ⟨m, hm, by rw [hd, hR]; exact fun hc => Dir.noConfusion hc⟩

/-- **A drone heading left reaches its turning point within the time it takes
to walk to the left border.** The bound Lemma 3.5 needs: the drone cannot be
heading left for longer than its distance to `0`. -/
theorem time_bound_of_dir_left {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {k m : ℕ} (hkm : k ≤ m)
    (hall : ∀ j, k ≤ j → j ≤ m → (c.run hn j).dir i = Dir.left) :
    (c.run hn m).time ≤ (c.run hn k).time + (c.run hn k).pos i := by
  obtain ⟨p, rfl⟩ : ∃ p, m = k + p := ⟨m - k, by omega⟩
  have hconst : ∀ j, k ≤ j → j < k + p → (c.run hn j).dir i = (c.run hn k).dir i := by
    intro j hj1 hj2
    rw [hall j hj1 (by omega), hall k (le_refl k) (by omega)]
  have hkey := pos_sub_eq_of_dirConst hn i k p hconst
  rw [hall k (le_refl k) (by omega), Dir.sign_left] at hkey
  have hp0 : 0 ≤ (c.run hn (k + p)).pos i := (onPerimeter_run hn hi (k + p) i).1
  linarith

/-- Symmetrically, a drone heading right cannot do so for longer than its
distance to the right border. -/
theorem time_bound_of_dir_right {c : Config n} (hn : 0 < n) (hi : c.Invariant)
    {i : Fin n} {k m : ℕ} (hkm : k ≤ m)
    (hall : ∀ j, k ≤ j → j ≤ m → (c.run hn j).dir i = Dir.right) :
    (c.run hn m).time ≤ (c.run hn k).time + (1 - (c.run hn k).pos i) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = k + p := ⟨m - k, by omega⟩
  have hconst : ∀ j, k ≤ j → j < k + p → (c.run hn j).dir i = (c.run hn k).dir i := by
    intro j hj1 hj2
    rw [hall j hj1 (by omega), hall k (le_refl k) (by omega)]
  have hkey := pos_sub_eq_of_dirConst hn i k p hconst
  rw [hall k (le_refl k) (by omega), Dir.sign_right] at hkey
  have hp1 : (c.run hn (k + p)).pos i ≤ 1 := (onPerimeter_run hn hi (k + p) i).2
  linarith

end Config

end DPSS
