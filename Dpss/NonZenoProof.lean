/-
# DPSS — non-Zeno, proved

**A4**, and the headline of the whole development: the system cannot pack
infinitely many events into a finite stretch of time.

This is the property the existing ACL2 mechanization could not establish. Its
event-stepper was admitted as a *partial* function and
`(step-time-always-terminates)` is carried as an unproved hypothesis into its
top-level convergence theorem. Avigad–van Doorn give an argument for it but
never mechanize it.

## The argument

Not the paper's. Theirs rests on a claim about consecutive left turns
propagating between neighbours that I could not reconstruct (see
`Turning.lean`). This one is self-contained and counts instead:

* **Every step turns at least one drone** (`someDroneTurns_step`).
* **Consecutive turns of one drone are `1/n` apart in time**
  (`time_gap_of_consecutive_turns`).
* So among any `n+1` consecutive steps, some drone must turn **twice** — there
  are only `n` drones — and those two turns cost `1/n` of time.

Hence `n+1` steps buy `1/n` of clock, every time, and the clock grows without
bound.

The only non-DPSS ingredient is the pigeonhole.
-/

import Dpss.TurnSpacing

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

namespace Config

/-! ## Running a run from partway along -/

/-- Stepping `k` then `j` times is stepping `k + j` times. -/
theorem run_add (c : Config n) (hn : 0 < n) (k j : ℕ) :
    c.run hn (k + j) = (c.run hn k).run hn j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show k + (j + 1) = (k + j) + 1 from rfl, run_succ, ih, run_succ]

/-- The clock never runs backwards, over any stretch. -/
theorem time_mono_run' {c : Config n} (hn : 0 < n) (hi : c.Invariant) {k j : ℕ}
    (hkj : k ≤ j) : (c.run hn k).time ≤ (c.run hn j).time := by
  obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    refine le_trans (ih (by omega)) ?_
    rw [show k + (m + 1) = (k + m) + 1 from rfl]
    exact time_mono_run hn hi (k + m)

/-! ## Finding two turns with nothing between them -/

/-- If a drone turns at `b`, it has a *first* turn after any earlier index, and
nothing turns it in between. -/
theorem exists_first_turn_after {c : Config n} (hn : 0 < n) (i : Fin n)
    {a b : ℕ} (hab : a < b) (hb : TurnsAt c hn i b) :
    ∃ b', a < b' ∧ b' ≤ b ∧ TurnsAt c hn i b' ∧
      ∀ j, a < j → j < b' → ¬ TurnsAt c hn i j := by
  classical
  have hex : ∃ m : ℕ, TurnsAt c hn i (a + 1 + m) :=
    ⟨b - a - 1, by rw [show a + 1 + (b - a - 1) = b by omega]; exact hb⟩
  have hle : Nat.find hex ≤ b - a - 1 :=
    Nat.find_le (by rw [show a + 1 + (b - a - 1) = b by omega]; exact hb)
  refine ⟨a + 1 + Nat.find hex, by omega, by omega, Nat.find_spec hex, ?_⟩
  intro j hj1 hj2
  obtain ⟨m, rfl⟩ : ∃ m, j = a + 1 + m := ⟨j - a - 1, by omega⟩
  exact Nat.find_min hex (by omega)

/-! ## `n+1` steps buy `1/n` of clock -/

/-- **Among any `n+1` consecutive steps, the clock advances by at least `1/n`.**

Every step turns some drone, there are only `n` drones, so over `n+1` steps one
of them turns twice — and two turns of one drone are `1/n` apart. -/
theorem time_advance_of_steps {c : Config n} (hn : 0 < n) (hi : c.Invariant) :
    c.time + 1 / (n : ℝ) ≤ (c.run hn (n + 1)).time := by
  classical
  -- every step turns somebody; name a witness for each
  have hturn : ∀ j : Fin (n + 1), ∃ i : Fin n, TurnsAt c hn i j.val :=
    fun j => someDroneTurns_run hn j.val
  choose f hf using hturn
  -- with only `n` drones and `n+1` steps, one drone turns twice
  obtain ⟨x, y, hxy, hfxy⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  -- the argument, given the earlier of the two indices
  have main : ∀ x y : Fin (n + 1), x.val < y.val → f x = f y →
      c.time + 1 / (n : ℝ) ≤ (c.run hn (n + 1)).time := by
    intro x y hlt hfeq
    have hbx : TurnsAt c hn (f x) x.val := hf x
    have hby : TurnsAt c hn (f x) y.val := by rw [hfeq]; exact hf y
    obtain ⟨b', hb1, hb2, hb3, hb4⟩ :=
      exists_first_turn_after hn (f x) hlt hby
    have hgap := time_gap_of_consecutive_turns hn (f x) hb1 hbx hb3 hb4
    have hstart : c.time ≤ (c.run hn (x.val + 1)).time := by
      have := time_mono_run' hn hi (k := 0) (j := x.val + 1) (by omega)
      simpa using this
    have hend : (c.run hn (b' + 1)).time ≤ (c.run hn (n + 1)).time := by
      refine time_mono_run' hn hi ?_
      have := y.isLt
      omega
    linarith
  rcases lt_or_gt_of_ne (fun hv => hxy (Fin.ext hv)) with hlt | hgt
  · exact main x y hlt hfxy
  · exact main y x hgt hfxy.symm

/-! ## Non-Zeno -/

/-- **The system is free of Zeno behaviour.**

Every instant is eventually passed: the times along a run grow without bound.
`n+1` steps buy `1/n` of clock, so `m(n+1)` steps buy `m/n`, and `m` can be
taken as large as we like.

This is the obligation the ACL2 development carries as an unproved
hypothesis. -/
theorem nonZeno {c : Config n} (hn : 0 < n) (hi : c.Invariant) :
    NonZeno c hn := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- `m` blocks of `n+1` steps buy `m/n` of clock
  have key : ∀ m : ℕ, c.time + (m : ℝ) / (n : ℝ)
      ≤ (c.run hn (m * (n + 1))).time := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsplit : c.run hn ((m + 1) * (n + 1))
          = (c.run hn (m * (n + 1))).run hn (n + 1) := by
        rw [← run_add]
        congr 1
        ring
      have hstep := time_advance_of_steps hn (invariant_run hn hi (m * (n + 1)))
      rw [hsplit]
      have : ((m : ℝ) + 1) / (n : ℝ) = (m : ℝ) / (n : ℝ) + 1 / (n : ℝ) := by
        field_simp
      push_cast
      rw [this]
      linarith
  intro T
  obtain ⟨m, hm⟩ := exists_nat_gt ((T - c.time) * (n : ℝ))
  refine ⟨m * (n + 1), ?_⟩
  have hkey := key m
  have : T - c.time < (m : ℝ) / (n : ℝ) := by
    rw [lt_div_iff₀ hnR]
    exact hm
  linarith

end Config

end DPSS
