/-
# DPSS — S6c: the safety traces, from Lean

`rust/traces.expected` records what the verified binary does. Two of its blocks
are checked against Lean and the rest were, until this file, only recorded from
the binary — a regression test rather than a differential one, which
`rust/traces.sh` has said in as many words since they were written.

The obstruction was never the mathematics. It was that `Fence.Traj` was a
structure over `ℕ → ℝ` and did not execute. S6a removed that: the fence is over
an ordered ring, `ℤ` is an instance, and nothing in it is `noncomputable` any
more. So the adversary the harness flies can be *defined* in Lean, proved to
satisfy the vehicle contract, and evaluated.

## One adversary, six blocks

The six safety blocks looked like three different experiments — a drone against
a wall, a pair closing on each other, a pair across a stale link — each in its
own vocabulary, twice over for the sufficient and the deficient margin. They are
all the same trajectory:

> fly at the fence, full displacement every leg, sensor reading high by the
> whole sensing allowance, the surveillance algorithm asking to keep going, and
> a reversal that holds station and no more.

`Sim` is that, and the separation and stale-link blocks are it in the
coordinates `Dpss/Separation.lean` and `Dpss/Comms.lean` already establish: the
excess separation `g - d` under the doubled vehicle, and under the doubled
vehicle with staleness folded into its sensing term. The adversary does not
change — the *vehicle* does. Six blocks, six lines of definition, one theorem.

## What is proved here

`Sim.trajOk` says the adversary satisfies the whole vehicle contract, for **any**
well-formed vehicle and **any** margin. It is not a fact about the recorded
numbers, so it cannot be invalidated by changing them; it is what makes the
recorded numbers a trajectory the fence theorem applies to rather than six
columns of arithmetic.

Everything after it is `decide`, on the concrete integers the binary prints.
-/

import Dpss.FenceInt

set_option linter.style.header false

namespace DPSS
namespace FenceInt

/-! ## The adversary -/

/-- The worst case the trace harness flies: a drone heading for the fence, with
its sensor reading high by the whole sensing allowance.

`rust/src/main.rs`, `fence_trace` — and, in the shifted coordinates, `pair_trace`
and `comms_trace`. -/
structure Sim where
  /-- The vehicle. For the pair blocks this is the *doubled* vehicle, and for the
  stale-link blocks the doubled vehicle with `age · dmax` in its sensing term. -/
  V : Vehicle
  /-- The margin the controller is given. -/
  M : ℤ
  /-- Where the drone starts. -/
  p0 : ℤ
deriving DecidableEq, Repr

namespace Sim

/-- What the controller commands at a drone standing at `x`. Adverse sensing:
the observation reads `eps` high, which at a *left* fence is the choice that
delays the reversal as long as possible. -/
def dirOf (S : Sim) (x : ℤ) : Dir := fenceDir S.M (x + S.V.eps) Dir.left

/-- Position at each sample. A leftward leg spends the whole displacement
allowance; a reversal holds station and gains nothing. -/
def p (S : Sim) : ℕ → ℤ
  | 0 => S.p0
  | k + 1 => if S.dirOf (S.p k) = Dir.left then S.p k - S.V.dmax else S.p k

/-- What the sensor reports. -/
def obs (S : Sim) (k : ℕ) : ℤ := S.p k + S.V.eps

/-- What the controller commands. -/
def dir (S : Sim) (k : ℕ) : Dir := S.dirOf (S.p k)

/-- The lowest position of the leg: a full `dmax` heading for the fence, the
full turn allowance on the reversal. -/
def low (S : Sim) (k : ℕ) : ℤ :=
  if S.dir k = Dir.left then S.p k - S.V.dmax else S.p k - S.V.turn

/-- What the surveillance algorithm asks for: keep going, at every sample. -/
def req (_ : Sim) (_ : ℕ) : Dir := Dir.left

@[simp] theorem obs_eq (S : Sim) (k : ℕ) : S.obs k = S.p k + S.V.eps := rfl

@[simp] theorem dir_eq (S : Sim) (k : ℕ) :
    S.dir k = fenceDir S.M (S.obs k) (S.req k) := rfl

theorem p_succ (S : Sim) (k : ℕ) :
    S.p (k + 1) = if S.dir k = Dir.left then S.p k - S.V.dmax else S.p k := rfl

theorem not_left_of_right {S : Sim} {k : ℕ} (h : S.dir k = Dir.right) :
    ¬ S.dir k = Dir.left := by rw [h]; exact fun h => Dir.noConfusion h

theorem low_of_left {S : Sim} {k : ℕ} (h : S.dir k = Dir.left) :
    S.low k = S.p k - S.V.dmax := by unfold Sim.low; rw [if_pos h]

theorem low_of_right {S : Sim} {k : ℕ} (h : S.dir k = Dir.right) :
    S.low k = S.p k - S.V.turn := by unfold Sim.low; rw [if_neg (not_left_of_right h)]

theorem p_succ_of_left {S : Sim} {k : ℕ} (h : S.dir k = Dir.left) :
    S.p (k + 1) = S.p k - S.V.dmax := by rw [p_succ, if_pos h]

theorem p_succ_of_right {S : Sim} {k : ℕ} (h : S.dir k = Dir.right) :
    S.p (k + 1) = S.p k := by rw [p_succ, if_neg (not_left_of_right h)]

/-- **The adversary obeys the vehicle contract.**

For every well-formed vehicle and every margin — the recorded numbers play no
part. Each clause is one branch of one `if`: the displacement bound and the turn
allowance hold with equality because the adversary spends the whole of each, and
`hold_leg` holds because its reversal gains nothing rather than losing ground.

`rust/src/fence.rs`, `traj_ok`. -/
theorem trajOk (S : Sim) (hwf : S.V.wf) :
    FenceInt.trajOk S.V S.M S.p S.dir S.low S.obs S.req := by
  obtain ⟨hd, ht, he⟩ := hwf
  refine ⟨fun k => ?_, fun k => rfl, fun k => ?_⟩
  · -- the sensor reads exactly `eps` high
    constructor
    · simp; linarith
    · simp
  · -- the five clauses of `leg_ok`, one branch of one `if` each
    unfold FenceInt.legOk
    cases hk : S.dir k with
    | left =>
      rw [low_of_left hk, p_succ_of_left hk]
      exact ⟨by linarith, le_refl _, fun _ => le_refl _,
        fun h => absurd h (fun h => Dir.noConfusion h),
        fun h => absurd h (fun h => Dir.noConfusion h)⟩
    | right =>
      rw [low_of_right hk, p_succ_of_right hk]
      exact ⟨by linarith, by linarith, fun h => absurd h (fun h => Dir.noConfusion h),
        fun _ => le_refl _, fun _ => le_refl _⟩

/-- And therefore it is a `Fence.Traj`, so every theorem of `Dpss/Fence.lean`
applies to it. -/
def toTraj (S : Sim) (hwf : S.V.wf) : Fence.Traj (S.V.toFence hwf) S.M :=
  FenceInt.toTraj hwf (S.trajOk hwf)

/-- **The fence theorem, about the recorded adversary.** When the margin covers
the three terms and the drone starts with the clearance the invariant asks for,
the whole trace stays clear of the fence — at every sample and between them. -/
theorem low_nonneg (S : Sim) (hwf : S.V.wf)
    (hM : S.V.dmax + S.V.turn + S.V.eps ≤ S.M)
    (h0 : safe S.V (S.p 0) (S.dir 0)) (k : ℕ) : 0 ≤ S.low k :=
  (FenceInt.low_nonneg_at S.V S.M S.p S.dir S.low S.obs S.req k hwf hM
    (S.trajOk hwf) h0).1

end Sim

/-! ## The six blocks

Each is one `Sim`. The fence blocks are it directly; the separation blocks are
it in the excess-separation coordinate `g - d` with the **doubled** vehicle
(`Dpss/Separation.lean`); the stale-link blocks are it with the doubled vehicle
carrying `age · dmax` more sensing error (`Dpss/Comms.lean`). The numbers below
are `rust/src/main.rs`'s arguments, transported into those coordinates — nothing
else differs between the blocks. -/

/-- The airframe of every safety block: `dmax = 10`, `turn = 3`, `eps = 2`. -/
def traceV : Vehicle := traceVehicle

/-- The doubled vehicle a pair faces. `Dpss/Separation.lean`, `Vehicle.pair`. -/
def tracePairV : Vehicle := ⟨2 * traceV.dmax, 2 * traceV.turn, 2 * traceV.eps⟩

/-- The doubled vehicle across a link `a` samples stale.
`Dpss/Comms.lean`, `Vehicle.commsPair`. -/
def traceCommsV (a : ℤ) : Vehicle :=
  ⟨2 * traceV.dmax, 2 * traceV.turn, 2 * traceV.eps + a * traceV.dmax⟩

/-- The standoff the pair blocks hold. -/
def traceD : ℤ := 5

/-- `fence (margin=15)` — the margin covers `10 + 3 + 2`. -/
def fenceOk : Sim := ⟨traceV, 15, 44⟩
/-- `fence, margin short by eps (margin=13)`. -/
def fenceShort : Sim := ⟨traceV, 13, 42⟩
/-- `separation (margin=30)`, in the excess-separation coordinate: `52 - 5`. -/
def sepOk : Sim := ⟨tracePairV, 30, 47⟩
/-- `separation, margin short by 2*eps (margin=26)`: `48 - 5`. -/
def sepShort : Sim := ⟨tracePairV, 26, 43⟩
/-- `stale link (age=2, margin=50)`: `52 - 5`, against the degraded vehicle. -/
def linkOk : Sim := ⟨traceCommsV 2, 50, 47⟩
/-- `stale link on the fresh margin (margin=30)` — one the margin does not
cover, and the gap goes negative. -/
def linkShort : Sim := ⟨traceCommsV 2, 30, 47⟩

theorem traceV_wf : traceV.wf := by decide
theorem tracePairV_wf : tracePairV.wf := by decide
theorem traceCommsV_wf (a : ℤ) (ha : 0 ≤ a) : (traceCommsV a).wf := by
  have h : (0 : ℤ) ≤ a * 10 := mul_nonneg ha (by norm_num)
  unfold Vehicle.wf traceCommsV traceV traceVehicle
  exact ⟨by norm_num, by norm_num, by simpa using by linarith⟩

/-! ## The blocks with a sufficient margin stay clear, and Lean says so

Not by evaluating the trace — by `Sim.low_nonneg`, which is the fence theorem.
The `decide` is only for the initial condition. -/

theorem fenceOk_clear (k : ℕ) : 0 ≤ fenceOk.low k :=
  fenceOk.low_nonneg traceV_wf (by decide) (by decide) k

theorem sepOk_clear (k : ℕ) : 0 ≤ sepOk.low k :=
  sepOk.low_nonneg tracePairV_wf (by decide) (by decide) k

theorem linkOk_clear (k : ℕ) : 0 ≤ linkOk.low k :=
  linkOk.low_nonneg (traceCommsV_wf 2 (by decide)) (by decide) (by decide) k

/-! ## And the deficient ones breach, at the sample the binary prints

These are the negative controls, and they are why the margin condition in
`Sim.low_nonneg` is not slack. -/

theorem fenceShort_breach : fenceShort.low 4 = -1 := by decide
theorem sepShort_breach : sepShort.low 2 + traceD = 2 := by decide
theorem linkShort_breach : linkShort.low 3 + traceD = -14 := by decide

/-! ## The recorded columns

Each theorem below is the block as `rust/traces.expected` prints it, in the
coordinate the block is printed in: position for the fence, gap for the pair.
`decide` on integers — the point being that these are now *theorems about a
trajectory Lean has proved obeys the vehicle contract*, not numbers read off a
program. -/

/-- Sample `k` of a block, as printed: position (or gap), observation, heading,
low-water mark. `shift` is `0` for the fence blocks and the standoff `d` for the
pair blocks, which print gaps. -/
def row (S : Sim) (shift : ℤ) (k : ℕ) : ℤ × ℤ × Dir × ℤ :=
  (S.p k + shift, S.obs k + shift, S.dir k, S.low k + shift)

def rows (S : Sim) (shift : ℤ) (n : ℕ) : List (ℤ × ℤ × Dir × ℤ) :=
  (List.range n).map (row S shift)

theorem fenceOk_rows : rows fenceOk 0 6 =
    [(44, 46, Dir.left, 34), (34, 36, Dir.left, 24), (24, 26, Dir.left, 14),
     (14, 16, Dir.left, 4), (4, 6, Dir.right, 1), (4, 6, Dir.right, 1)] := by decide

theorem fenceShort_rows : rows fenceShort 0 6 =
    [(42, 44, Dir.left, 32), (32, 34, Dir.left, 22), (22, 24, Dir.left, 12),
     (12, 14, Dir.left, 2), (2, 4, Dir.right, -1), (2, 4, Dir.right, -1)] := by decide

theorem sepOk_rows : rows sepOk traceD 4 =
    [(52, 56, Dir.left, 32), (32, 36, Dir.left, 12), (12, 16, Dir.right, 6),
     (12, 16, Dir.right, 6)] := by decide

theorem sepShort_rows : rows sepShort traceD 4 =
    [(48, 52, Dir.left, 28), (28, 32, Dir.left, 8), (8, 12, Dir.right, 2),
     (8, 12, Dir.right, 2)] := by decide

theorem linkOk_rows : rows linkOk traceD 4 =
    [(52, 76, Dir.left, 32), (32, 56, Dir.left, 12), (12, 36, Dir.right, 6),
     (12, 36, Dir.right, 6)] := by decide

theorem linkShort_rows : rows linkShort traceD 4 =
    [(52, 76, Dir.left, 32), (32, 56, Dir.left, 12), (12, 36, Dir.left, -8),
     (-8, 16, Dir.right, -14)] := by decide

/-! ## The link block

`link_ok` is about two drones and a message, not about one trajectory, so it
needs its own witness — and the worst-case gap blocks cannot supply one, because
they apply the steady-state staleness from the first sample, which is a bound
rather than a history. Here is the history: own drone moving right by `dmax` a
sample, the neighbour whatever the gap requires, and a report `a` samples old. -/

/-- Own position: moving right by `dmax` a sample. -/
def linkOwn (k : ℕ) : ℤ := (k : ℤ) * traceV.dmax

/-- The neighbour, from the gap the adversary produces. -/
def linkNbr (k : ℕ) : ℤ := linkOwn k + (linkOk.p k + traceD)

/-- The sample the held report was taken at: `a` back, clamped at the start. -/
def linkSrc (a k : ℕ) : ℕ := k - a

/-- The report: the neighbour's position when taken, read `eps` high. -/
def linkRep (a k : ℕ) : ℤ := linkNbr (linkSrc a k) + traceV.eps

def linkRows (a : ℕ) (n : ℕ) : List (ℤ × ℤ × ℤ × ℕ × ℤ) :=
  (List.range n).map fun k =>
    (linkOwn k, linkNbr k, linkOk.p k + traceD, linkSrc a k, linkRep a k)

theorem link_rows : linkRows 2 4 =
    [(0, 52, 52, 0, 54), (10, 42, 32, 0, 54), (20, 32, 12, 0, 54),
     (30, 42, 12, 1, 44)] := by decide

/-- **The link witness satisfies `link_ok`'s per-sample clauses**, at each of the
samples the block prints. `rust/src/comms.rs`, `link_step_ok`. -/
theorem link_step_ok_rows :
    ∀ k ∈ List.range 4,
      linkSrc 2 k ≤ k ∧ k - linkSrc 2 k ≤ 2 ∧
        -traceV.eps ≤ linkRep 2 k - linkNbr (linkSrc 2 k) ∧
          linkRep 2 k - linkNbr (linkSrc 2 k) ≤ traceV.eps := by decide

/-- **And the neighbour never moves faster than `dmax` a sample**, over every
pair of samples in the block. `rust/src/comms.rs`, `drift_ok`. -/
theorem link_drift_rows :
    ∀ k ∈ List.range 4, ∀ j ∈ List.range (k + 1),
      -(((k - j : ℕ) : ℤ) * traceV.dmax) ≤ linkNbr k - linkNbr j ∧
        linkNbr k - linkNbr j ≤ ((k - j : ℕ) : ℤ) * traceV.dmax := by decide

/-! ## The negative control

`rust/traces.expected`'s last block is a drone whose reversal loses ground,
which the executable specification of S6b rejects. Lean rejects it too, and at
the same sample: the leg from `k = 4` violates `leg_ok`. -/

/-- The violating trajectory: the same drone, but a reversal that slips back by
the turn allowance instead of holding station. -/
def badP : ℕ → ℤ
  | 0 => 44
  | k + 1 =>
    if fenceOk.dirOf (badP k) = Dir.left then badP k - traceV.dmax
    else badP k - traceV.turn

def badDir (k : ℕ) : Dir := fenceOk.dirOf (badP k)

def badLow (k : ℕ) : ℤ :=
  if badDir k = Dir.left then badP k - traceV.dmax else badP k - traceV.turn

theorem bad_rows : (List.range 6).map (fun k => (badP k, badDir k, badLow k)) =
    [(44, Dir.left, 34), (34, Dir.left, 24), (24, Dir.left, 14), (14, Dir.left, 4),
     (4, Dir.right, 1), (1, Dir.right, -2)] := by decide

/-- **The leg from sample 4 breaks the contract**, because a reversal that loses
ground is what `hold_leg` forbids. -/
theorem bad_leg_4 : ¬ legOk traceV (badP 4) (badDir 4) (badLow 4) (badP 5) := by decide

/-- So no `trajOk` holds of it — which is what the binary's `FAILS first at k=4`
reports, computed there by a function Verus proves equal to the specification. -/
theorem bad_not_trajOk (obs : ℕ → ℤ) (req : ℕ → Dir) (margin : ℤ) :
    ¬ trajOk traceV margin badP badDir badLow obs req := by
  intro h
  exact bad_leg_4 (h.2.2 4)

end FenceInt
end DPSS
