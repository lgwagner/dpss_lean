/-
# DPSS — S6a: the fence at `ℤ`, in the shape the Rust has

`Dpss/Fence.lean` proves the fence over an arbitrary ordered ring.
`rust/src/fence.rs` proves it in Verus over `int`. This file is the bridge a
reader walks across: the Verus statements, transliterated into Lean at `α := ℤ`,
each proved by *instantiating* the general theorem rather than by repeating its
argument.

## What this closes, and what it does not

What it closes is the **`ℝ`/`ℤ` gap**. Before this file, the Lean fence was a
statement about real numbers and the Verus fence a statement about mathematical
integers, and a reader comparing them had to satisfy themselves that nothing had
been lost in between — as it happens nothing had, because the fence contract is
stated in *displacement per sample*, which is a length (`INSIGHTS.md` §20), but
that was a fact to be checked rather than one the files made evident. Now the
Lean theorems hold at `ℤ` itself and the two developments quantify over the same
integers. There is no scaling argument here, unlike `Dpss/IntModel.lean`, and
nothing to be inexact about.

What it does **not** close is statement-level correspondence. Nothing mechanical
checks that `legOk` below says what `leg_ok` says in `rust/src/fence.rs`; that is
still a human read. What this file does is make that read *short* — the
definitions sit one screen apart, in the same order, with the same argument
lists and the same names.

## The packaging difference, and why it is kept

Verus has `Vehicle` as three plain integers with a separate `wf` predicate;
Lean's `Fence.Vehicle` carries its three non-negativity proofs as fields,
because that is how a Lean structure is normally built and it keeps the
hypothesis off every theorem statement. Rather than change either, this file
**mirrors the Rust packaging** — unbundled `Vehicle`, separate `wf` — and
`Vehicle.toFence` is the one-line map between them. So the correspondence a
reader has to check is between two files that look alike, and the repackaging is
visible in one definition instead of being spread across ten statements.
-/

import Dpss.Fence

set_option linter.style.header false

namespace DPSS
namespace FenceInt

/-! ## The vehicle

`rust/src/fence.rs`, `struct Vehicle` and `Vehicle::wf`. -/

/-- What the proof needs to know about the airframe, unbundled as in the Rust:
three integers, with well-formedness a separate predicate. -/
structure Vehicle where
  /-- The furthest the drone travels in one sample period. -/
  dmax : ℤ
  /-- Overshoot allowance for a commanded reversal. -/
  turn : ℤ
  /-- Position sensing error bound. -/
  eps : ℤ
deriving DecidableEq, Repr

namespace Vehicle

/-- `rust/src/fence.rs`, `Vehicle::wf`. -/
def wf (v : Vehicle) : Prop := 0 ≤ v.dmax ∧ 0 ≤ v.turn ∧ 0 ≤ v.eps

instance (v : Vehicle) : Decidable v.wf := by unfold wf; infer_instance

/-- The clearance a drone must hold from the fence, given its heading.
`rust/src/fence.rs`, `Vehicle::clearance`. -/
def clearance (v : Vehicle) (d : Dir) : ℤ :=
  if d = Dir.left then v.dmax + v.turn else v.turn

/-- The map to the bundled vehicle of `Dpss/Fence.lean`. This one definition is
the whole of the repackaging. -/
def toFence (v : Vehicle) (h : v.wf) : Fence.Vehicle ℤ where
  Dmax := v.dmax
  turn := v.turn
  eps := v.eps
  Dmax_nonneg := h.1
  turn_nonneg := h.2.1
  eps_nonneg := h.2.2

@[simp] theorem toFence_Dmax (v : Vehicle) (h : v.wf) : (v.toFence h).Dmax = v.dmax := rfl
@[simp] theorem toFence_turn (v : Vehicle) (h : v.wf) : (v.toFence h).turn = v.turn := rfl
@[simp] theorem toFence_eps (v : Vehicle) (h : v.wf) : (v.toFence h).eps = v.eps := rfl

/-- The two spellings of the clearance agree. -/
@[simp] theorem clearance_eq (v : Vehicle) (h : v.wf) (d : Dir) :
    v.clearance d = (v.toFence h).margin d := by
  cases d <;> simp [clearance, Fence.Vehicle.margin]

end Vehicle

/-! ## The controller, the invariant, and one leg

`rust/src/fence.rs`: `fence_dir`, `safe`, `leg_ok`, `obs_ok`. Each is followed
by the proof that it is the corresponding object of `Dpss/Fence.lean`, and every
one of those proofs is `rfl` or a case split on `Dir`. -/

/-- `rust/src/fence.rs`, `fence_dir`. -/
def fenceDir (margin phat : ℤ) (req : Dir) : Dir :=
  if phat ≤ margin then Dir.right else req

theorem fenceDir_eq (margin phat : ℤ) (req : Dir) :
    fenceDir margin phat req = Fence.fenceDir margin phat req := rfl

/-- `rust/src/fence.rs`, `safe`. -/
def safe (v : Vehicle) (p : ℤ) (d : Dir) : Prop := v.clearance d ≤ p

instance (v : Vehicle) (p : ℤ) (d : Dir) : Decidable (safe v p d) := by
  unfold safe; infer_instance

/-- `rust/src/fence.rs`, `leg_ok`. -/
def legOk (v : Vehicle) (p : ℤ) (d : Dir) (low pNext : ℤ) : Prop :=
  low ≤ p ∧ low ≤ pNext ∧
    (d = Dir.left → p - v.dmax ≤ low) ∧
    (d = Dir.right → p - v.turn ≤ low) ∧
    (d = Dir.right → p ≤ pNext)

instance (v : Vehicle) (p : ℤ) (d : Dir) (low pNext : ℤ) :
    Decidable (legOk v p d low pNext) := by unfold legOk; infer_instance

/-- `rust/src/fence.rs`, `obs_ok`. -/
def obsOk (v : Vehicle) (obs p : ℤ) : Prop := -v.eps ≤ obs - p ∧ obs - p ≤ v.eps

instance (v : Vehicle) (obs p : ℤ) : Decidable (obsOk v obs p) := by
  unfold obsOk; infer_instance

theorem safe_iff (v : Vehicle) (h : v.wf) (p : ℤ) (d : Dir) :
    safe v p d ↔ (v.toFence h).margin d ≤ p := by
  unfold safe; rw [Vehicle.clearance_eq v h]

theorem legOk_iff (v : Vehicle) (h : v.wf) (p : ℤ) (d : Dir) (low pNext : ℤ) :
    legOk v p d low pNext ↔ Fence.LegOk (v.toFence h) p d low pNext := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩

theorem obsOk_iff (v : Vehicle) (h : v.wf) (obs p : ℤ) :
    obsOk v obs p ↔ Fence.ObsOk (v.toFence h) obs p := Iff.rfl

/-! ## A trajectory

`rust/src/fence.rs`, `traj_ok` — five functions of the sample index, with the
three obligations quantified over `k`. Infinite, as in Lean and as in the Verus:
`spec_fn(nat)` there, `ℕ → ℤ` here. -/

/-- `rust/src/fence.rs`, `traj_ok`. -/
def trajOk (v : Vehicle) (margin : ℤ) (p : ℕ → ℤ) (d : ℕ → Dir)
    (low obs : ℕ → ℤ) (req : ℕ → Dir) : Prop :=
  (∀ k, obsOk v (obs k) (p k)) ∧
    (∀ k, d k = fenceDir margin (obs k) (req k)) ∧
    (∀ k, legOk v (p k) (d k) (low k) (p (k + 1)))

/-- A `trajOk` is a `Fence.Traj`. Field for field, with no arithmetic. -/
def toTraj {v : Vehicle} (h : v.wf) {margin : ℤ} {p : ℕ → ℤ} {d : ℕ → Dir}
    {low obs : ℕ → ℤ} {req : ℕ → Dir} (ht : trajOk v margin p d low obs req) :
    Fence.Traj (v.toFence h) margin where
  p := p
  d := d
  low := low
  obs := obs
  req := req
  obs_close := fun k => abs_le.mpr ((obsOk_iff v h _ _).mp (ht.1 k))
  control := ht.2.1
  low_le_pos := fun k => (ht.2.2 k).1
  low_le_next := fun k => (ht.2.2 k).2.1
  left_leg := fun k => (ht.2.2 k).2.2.1
  turn_leg := fun k => (ht.2.2 k).2.2.2.1
  hold_leg := fun k => (ht.2.2 k).2.2.2.2

/-! ## The theorems

The five `proof fn`s of `rust/src/fence.rs`, argument for argument. Each proof
below is an application of the corresponding theorem of `Dpss/Fence.lean`: no
induction is repeated and no arithmetic is redone, because there is nothing here
that the general statement did not already prove. -/

/-- **A safe sample leaves at least the turn allowance at the next one.**
`rust/src/fence.rs`, `turn_le_next`. -/
theorem turn_le_next (v : Vehicle) (p : ℤ) (d : Dir) (low pNext : ℤ)
    (hwf : v.wf) (hs : safe v p d) (hl : legOk v p d low pNext) :
    v.turn ≤ pNext :=
  Fence.turn_le_next ((safe_iff v hwf p d).mp hs) ((legOk_iff v hwf p d low pNext).mp hl)

/-- **The drone is on the safe side of the fence for the whole leg.**
`rust/src/fence.rs`, `low_nonneg`. -/
theorem low_nonneg (v : Vehicle) (p : ℤ) (d : Dir) (low pNext : ℤ)
    (hwf : v.wf) (hs : safe v p d) (hl : legOk v p d low pNext) :
    0 ≤ low :=
  Fence.low_nonneg_leg ((safe_iff v hwf p d).mp hs)
    ((legOk_iff v hwf p d low pNext).mp hl)

/-- **One sample preserves the invariant.**
`rust/src/fence.rs`, `safe_step`. -/
theorem safe_step (v : Vehicle) (margin p : ℤ) (d : Dir) (low pNext obs : ℤ)
    (req : Dir) (hwf : v.wf) (hM : v.dmax + v.turn + v.eps ≤ margin)
    (hs : safe v p d) (hl : legOk v p d low pNext) (ho : obsOk v obs pNext) :
    safe v pNext (fenceDir margin obs req) := by
  rw [safe_iff v hwf, fenceDir_eq]
  exact Fence.safe_step (by simpa using hM) ((safe_iff v hwf p d).mp hs)
    ((legOk_iff v hwf p d low pNext).mp hl) ((obsOk_iff v hwf obs pNext).mp ho)

/-- **The invariant holds at every sample.**
`rust/src/fence.rs`, `safe_at`. -/
theorem safe_at (v : Vehicle) (margin : ℤ) (p : ℕ → ℤ) (d : ℕ → Dir)
    (low obs : ℕ → ℤ) (req : ℕ → Dir) (k : ℕ) (hwf : v.wf)
    (hM : v.dmax + v.turn + v.eps ≤ margin)
    (ht : trajOk v margin p d low obs req) (h0 : safe v (p 0) (d 0)) :
    safe v (p k) (d k) := by
  rw [safe_iff v hwf]
  exact Fence.Traj.safe_all (T := toTraj hwf ht) (by simpa using hM)
    ((safe_iff v hwf (p 0) (d 0)).mp h0) k

/-- **The drone never crosses the fence**, at any instant — `low` is the lowest
position of an entire leg, so this covers the time between samples.
`rust/src/fence.rs`, `low_nonneg_at`. -/
theorem low_nonneg_at (v : Vehicle) (margin : ℤ) (p : ℕ → ℤ) (d : ℕ → Dir)
    (low obs : ℕ → ℤ) (req : ℕ → Dir) (k : ℕ) (hwf : v.wf)
    (hM : v.dmax + v.turn + v.eps ≤ margin)
    (ht : trajOk v margin p d low obs req) (h0 : safe v (p 0) (d 0)) :
    0 ≤ low k ∧ 0 ≤ p k := by
  have hM' : (v.toFence hwf).Dmax + (v.toFence hwf).turn + (v.toFence hwf).eps ≤ margin := by
    simpa using hM
  have h0' := (safe_iff v hwf (p 0) (d 0)).mp h0
  exact ⟨Fence.Traj.low_nonneg (T := toTraj hwf ht) hM' h0' k,
    Fence.Traj.pos_nonneg (T := toTraj hwf ht) hM' h0' k⟩

/-! ## Sharpness, over the integers

`Fence.margin_sharp` stays over `ℝ`, because it halves the deficiency to build
its witness and so needs a field. The *construction* it uses is general, so a
sharpness witness at `ℤ` costs nothing beyond naming the numbers — and the
numbers worth naming are the ones in `rust/traces.expected`, where the verified
controller is driven with a margin one `eps` short and breaches.

This is the same trajectory the binary flies, except in the last sample's
`obs` column: `Fence.Sharp` reads the sensor *low* once the fence is behind the
drone, which is what makes the general construction unconditional, while the
trace harness reads high throughout. Both satisfy the sensing bound, both
command the same headings, and both reach `low = -1`. -/

/-- The vehicle of the recorded traces: `dmax = 10`, `turn = 3`, `eps = 2`. -/
def traceVehicle : Vehicle := ⟨10, 3, 2⟩

theorem traceVehicle_wf : traceVehicle.wf := by decide

/-- **The short margin breaches, and Lean says so about the integers the binary
uses.** With `margin = 13`, one `eps` below `10 + 3 + 2`, a drone starting at
`42` with the whole vehicle contract satisfied and the invariant holding at the
first sample is below the fence on its fifth leg, at `low = -1` — which is what
`rust/traces.expected` records the verified controller doing. -/
theorem trace_breach :
    ∃ T : Fence.Traj (traceVehicle.toFence traceVehicle_wf) 13,
      T.Safe 0 ∧ T.low 4 = -1 := by
  refine ⟨Fence.Sharp.traj (V := traceVehicle.toFence traceVehicle_wf) (p0 := 42)
    (m := 4) 13 (by omega) (by decide) (by decide), ?_, ?_⟩
  · show Fence.Vehicle.margin _ (Fence.Sharp.dir 4 0) ≤ Fence.Sharp.pos _ 42 4 0
    decide
  · show Fence.Sharp.low (traceVehicle.toFence traceVehicle_wf) 42 4 4 = -1
    decide

end FenceInt
end DPSS
