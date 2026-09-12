/-
# DPSS — S5: safety when the network degrades

Everything on this track so far has assumed a drone knows what it needs to know.
`Dpss/Fence.lean` assumes it senses its own position; `Dpss/Separation.lean`
assumes it knows the gap to its neighbour. The first assumption is local and
survives any network. The second does not: a gap is a fact about two drones, and
one of them has to be told.

This file asks what the separation guarantee costs when the telling is late,
lost, or stops altogether. There are three answers and they are quite different
in character.

## 1. The fence needs no network at all

Worth saying once, loudly, because it is structural rather than a theorem:
**nothing in `Fence.Traj` mentions another drone.** The controller reads one
number — its own observed position — and the guarantee `0 ≤ p` is preserved by
one drone's own dynamics. A total communications failure does not weaken the
fence by an epsilon. Whatever else degrades, the drones stay on the perimeter.

## 2. Staleness is sensing error

This is the reduction that makes bounded delay cheap. A drone holding a report
of its neighbour taken `a` samples ago knows that neighbour's position to within

    eps  +  a · Dmax

— the error when the report was taken, plus the furthest the neighbour can have
moved since. Adding its own sensing error gives a gap estimate good to
`2·eps + a·Dmax`, and the separation margin inflates by exactly `A · Dmax` where
`A` bounds the age:

    M  ≥  2·(Dmax + turn + eps)  +  A · Dmax.

**Delay and loss are the same phenomenon**, because both are bounded by an age:
a message lost is a message not yet arrived. `Vehicle.commsPair` is the degraded
vehicle this produces, and `Vehicle.pair` — S3's — is the case `A = 0`.

So the whole of §2 is another instance of the pattern in `INSIGHTS.md` §22: a
map into a structure that is already proved, not a new induction.

## 3. After convergence, separation is free

The third answer is the interesting one, and it falls out of results that were
built for other reasons.

`Dpss/Standoff.lean` proves two things that compose. `sConvergesBy` says every
drone is inside its own respaced segment from `(2 − 1/n)·(1 − (n−1)d)` onwards.
`standoff_tiles` says consecutive segments are separated by a buffer of exactly
`d`. Put them together and

> **two drones in their own segments are `d` apart — with no observation, no
> message, and no controller.**

`separated_of_segments` is that statement and its proof is one `linarith`.
`gap_ge_of_converged` applies it to a converged run.

The consequence is the useful one for a system designer: **the communication
requirement is transient.** A margin inflated by `A · Dmax` is the price of
coordinating *before* the team has synchronized. Afterwards the invariant is
maintained by geometry, and a drone that has lost contact permanently is still
safe provided it stays in its own segment — which is exactly what the algorithm
has already converged to doing.

That also settles what the fallback should be, which was the open design
question: **the safe degraded mode is "hold to your own segment"**, and it needs
no new mechanism, because it is the steady state.

## What this does not claim

* **Nothing here is about convergence.** A team that has lost coordination stays
  *safe*; whether it stays synchronized, or re-synchronizes, is a question about
  Algorithm B and estimate propagation, and is Track B.
* **`A` is a hypothesis.** Bounding message age is the network's job, exactly as
  bounding displacement is the airframe's. What is proved here is the exchange
  rate between the two: one sample of staleness costs one `Dmax` of margin.
-/

import Dpss.Separation
import Dpss.Standoff

set_option linter.style.header false

namespace DPSS
namespace Fence

/-! ## The degraded vehicle -/

/-- The vehicle a *pair* faces when one of them is working from a report at most
`A` samples old. Everything doubles as in `Vehicle.pair` — both drones move,
both turn, both are sensed — and the sensing term carries `A · Dmax` more,
because the neighbour may have moved that far since the report was taken. -/
noncomputable def Vehicle.commsPair (V : Vehicle) (A : ℕ) : Vehicle where
  Dmax := 2 * V.Dmax
  turn := 2 * V.turn
  eps := 2 * V.eps + (A : ℝ) * V.Dmax
  Dmax_nonneg := by have := V.Dmax_nonneg; linarith
  turn_nonneg := by have := V.turn_nonneg; linarith
  eps_nonneg := by
    have h1 := V.eps_nonneg
    have h2 : 0 ≤ (A : ℝ) * V.Dmax := mul_nonneg (Nat.cast_nonneg A) V.Dmax_nonneg
    linarith

@[simp] theorem Vehicle.commsPair_Dmax (V : Vehicle) (A : ℕ) :
    (V.commsPair A).Dmax = 2 * V.Dmax := rfl

@[simp] theorem Vehicle.commsPair_turn (V : Vehicle) (A : ℕ) :
    (V.commsPair A).turn = 2 * V.turn := rfl

@[simp] theorem Vehicle.commsPair_eps (V : Vehicle) (A : ℕ) :
    (V.commsPair A).eps = 2 * V.eps + (A : ℝ) * V.Dmax := rfl

/-- **A fresh link is S3.** With zero staleness the degraded vehicle is the one
`Dpss/Separation.lean` already uses, so this file generalizes that result rather
than sitting beside it. -/
theorem Vehicle.commsPair_zero (V : Vehicle) :
    (V.commsPair 0).Dmax = V.pair.Dmax ∧ (V.commsPair 0).turn = V.pair.turn ∧
      (V.commsPair 0).eps = V.pair.eps := by
  refine ⟨rfl, rfl, ?_⟩
  simp

/-! ## A pair across a link -/

/-- One adjacent pair, with the controlling drone working from a report of its
neighbour that may be stale.

`mode k = Dir.left` means **closing**, as in `PairTraj`. The fields split into
three groups: what the pair is physically doing, what the drone knows, and what
the controller does with it. -/
structure CommsPair (V : Vehicle) (A : ℕ) (d M : ℝ) where
  /-- Own position at each sample. -/
  p : ℕ → ℝ
  /-- The neighbour's true position at each sample. -/
  q : ℕ → ℝ
  /-- The gap, and the least gap on each leg. -/
  gap : ℕ → ℝ
  low : ℕ → ℝ
  /-- Whether the pair is closing on each leg. -/
  mode : ℕ → Dir
  /-- What the surveillance algorithm asked for. -/
  req : ℕ → Dir
  /-- Own position as sensed. -/
  phat : ℕ → ℝ
  /-- The neighbour's position, as last reported. -/
  rep : ℕ → ℝ
  /-- The sample at which that report was taken. -/
  src : ℕ → ℕ
  gap_def : ∀ k, gap k = q k - p k
  src_le : ∀ k, src k ≤ k
  /-- **The network's obligation**: no report is older than `A` samples. A lost
  message is a message not yet arrived, so loss and delay are one hypothesis. -/
  fresh : ∀ k, k - src k ≤ A
  /-- The report was accurate when it was taken. -/
  rep_close : ∀ k, |rep k - q (src k)| ≤ V.eps
  /-- Own sensing. -/
  phat_close : ∀ k, |phat k - p k| ≤ V.eps
  /-- **The airframe's obligation**, applied to the neighbour: it cannot have
  moved more than `Dmax` per sample since the report. -/
  drift : ∀ j k : ℕ, j ≤ k → |q k - q j| ≤ ((k - j : ℕ) : ℝ) * V.Dmax
  /-- The controller sees only the estimated excess separation. -/
  control : ∀ k, mode k = fenceDir M (rep k - phat k - d) (req k)
  low_le_gap : ∀ k, low k ≤ gap k
  low_le_next : ∀ k, low k ≤ gap (k + 1)
  close_leg : ∀ k, mode k = Dir.left → gap k - 2 * V.Dmax ≤ low k
  turn_leg : ∀ k, mode k = Dir.right → gap k - 2 * V.turn ≤ low k
  hold_leg : ∀ k, mode k = Dir.right → gap k ≤ gap (k + 1)

namespace CommsPair

variable {V : Vehicle} {A : ℕ} {d M : ℝ}

/-- **Staleness is sensing error.** A report `a` samples old localizes the
neighbour to `eps + a · Dmax`. -/
theorem rep_error (C : CommsPair V A d M) (k : ℕ) :
    |C.rep k - C.q k| ≤ V.eps + (A : ℝ) * V.Dmax := by
  have hsrc := C.src_le k
  have hdrift := C.drift (C.src k) k hsrc
  have hcast : ((k - C.src k : ℕ) : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast C.fresh k
  have hmul : ((k - C.src k : ℕ) : ℝ) * V.Dmax ≤ (A : ℝ) * V.Dmax :=
    mul_le_mul_of_nonneg_right hcast V.Dmax_nonneg
  have hq : |C.q (C.src k) - C.q k| ≤ (A : ℝ) * V.Dmax := by
    rw [abs_sub_comm]
    linarith
  have htri : |C.rep k - C.q k|
      ≤ |C.rep k - C.q (C.src k)| + |C.q (C.src k) - C.q k| :=
    abs_sub_le _ _ _
  have := C.rep_close k
  linarith

/-- And therefore the gap estimate is good to `2·eps + A·Dmax`, which is exactly
the degraded vehicle's sensing term. -/
theorem obs_error (C : CommsPair V A d M) (k : ℕ) :
    |(C.rep k - C.phat k - d) - (C.gap k - d)| ≤ (V.commsPair A).eps := by
  have hg := C.gap_def k
  have hrw : C.rep k - C.phat k - d - (C.gap k - d)
      = (C.rep k - C.q k) - (C.phat k - C.p k) := by rw [hg]; ring
  rw [hrw, Vehicle.commsPair_eps]
  have h1 := C.rep_error k
  have h2 := C.phat_close k
  calc |C.rep k - C.q k - (C.phat k - C.p k)|
      ≤ |C.rep k - C.q k| + |C.phat k - C.p k| := abs_sub _ _
    _ ≤ (V.eps + (A : ℝ) * V.Dmax) + V.eps := by linarith
    _ = 2 * V.eps + (A : ℝ) * V.Dmax := by ring

/-- **The link is a fence problem.** Same map as `PairTraj.toFence`, with the
staleness folded into the vehicle. -/
noncomputable def toFence (C : CommsPair V A d M) : Traj (V.commsPair A) M where
  p := fun k => C.gap k - d
  d := C.mode
  low := fun k => C.low k - d
  obs := fun k => C.rep k - C.phat k - d
  req := C.req
  obs_close := C.obs_error
  control := C.control
  low_le_pos := by intro k; have := C.low_le_gap k; linarith
  low_le_next := by intro k; have := C.low_le_next k; linarith
  left_leg := by
    intro k hm
    have := C.close_leg k hm
    simp only [Vehicle.commsPair_Dmax]
    linarith
  turn_leg := by
    intro k hm
    have := C.turn_leg k hm
    simp only [Vehicle.commsPair_turn]
    linarith
  hold_leg := by
    intro k hm
    have := C.hold_leg k hm
    linarith

/-- The invariant, in the degraded vehicle. -/
def Safe (C : CommsPair V A d M) (k : ℕ) : Prop :=
  d + (V.commsPair A).margin (C.mode k) ≤ C.gap k

theorem safe_iff_fence (C : CommsPair V A d M) (k : ℕ) :
    C.Safe k ↔ C.toFence.Safe k := by
  unfold Safe Traj.Safe toFence
  constructor <;> intro h <;> simp only at h ⊢ <;> linarith

/-- **Separation survives a degraded network.**

One extra sample of staleness costs exactly one `Dmax` of margin, and nothing
else changes: no extra hypothesis on the vehicle, no second induction. -/
theorem le_low
    (hM : 2 * (V.Dmax + V.turn + V.eps) + (A : ℝ) * V.Dmax ≤ M)
    {C : CommsPair V A d M} (h0 : C.Safe 0) (k : ℕ) : d ≤ C.low k := by
  have hMv : (V.commsPair A).Dmax + (V.commsPair A).turn + (V.commsPair A).eps ≤ M := by
    simp only [Vehicle.commsPair_Dmax, Vehicle.commsPair_turn, Vehicle.commsPair_eps]
    linarith
  have h := Traj.low_nonneg hMv ((C.safe_iff_fence 0).mp h0) k
  have hlow : C.toFence.low k = C.low k - d := rfl
  rw [hlow] at h
  linarith

/-- And at every sample. -/
theorem le_gap
    (hM : 2 * (V.Dmax + V.turn + V.eps) + (A : ℝ) * V.Dmax ≤ M)
    {C : CommsPair V A d M} (h0 : C.Safe 0) (k : ℕ) : d ≤ C.gap k :=
  le_trans (le_low hM h0 k) (C.low_le_gap k)

/-- **How long a drone may go unheard.**

Reading `le_gap` the other way round: with the margin `M` fixed by the design,
the network may fall behind by up to

    (M − 2·(Dmax + turn + eps)) / Dmax

samples before the separation guarantee is no longer supported. Beyond that the
pair must fall back — and §3 below says what the fallback is. -/
theorem age_within_budget (hD : 0 < V.Dmax)
    (hA : (A : ℝ) ≤ (M - 2 * (V.Dmax + V.turn + V.eps)) / V.Dmax)
    {C : CommsPair V A d M} (h0 : C.Safe 0) (k : ℕ) : d ≤ C.gap k := by
  refine le_gap ?_ h0 k
  rw [le_div_iff₀ hD] at hA
  linarith

end CommsPair

end Fence

/-! ## Separation without a network

The third answer, and the one that decides what a drone should do when the
network is gone for good. -/

namespace Config

variable {n : ℕ}

/-- **Two drones in their own segments are separated.**

No observation, no message, no controller — the respaced segments are `d` apart
by construction (`standoff_tiles`), so confinement *is* separation. -/
theorem separated_of_segments {d : ℝ} {n : ℕ} (i : Fin n) (h : i.val + 1 < n)
    {x y : ℝ} (hx : x ≤ standoffRightEnd d i)
    (hy : standoffLeftEnd d (nextIdx i h) ≤ y) : d ≤ y - x := by
  have := standoff_tiles d i h
  linarith

/-- **After convergence, the separation invariant is maintained by geometry.**

Every drone is inside its own respaced segment from
`(2 − 1/n)·(1 − (n−1)d)` onwards (`sConvergesBy`), and consecutive segments are
`d` apart, so every adjacent gap is at least the standoff — for ever, and
without a single message being exchanged.

This is what makes the communication budget of `CommsPair` a **transient** cost:
it buys coordination during phase 1, and after that the algorithm's own steady
state is the fallback. -/
theorem gap_ge_of_converged {d : ℝ} (hL : 0 < usable n d) {c : Config n}
    {hn : 0 < n} (hsi : c.SInvariant d hn) (hab : c.SApartOnBoundaries d)
    (j : ℕ) (ht : c.time + (2 - 1 / (n : ℝ)) * usable n d ≤ (c.sRun d hn j).time)
    (i : Fin n) (h : i.val + 1 < n) : d ≤ (c.sRun d hn j).gap i h := by
  have hcv := sConvergesBy hL hsi hab
  have hi := (hcv i j ht).2
  have hi1 := (hcv (nextIdx i h) j ht).1
  exact separated_of_segments i h hi hi1

/-- **The fallback, and it needs no new mechanism.**

A drone that has lost contact permanently is safe provided it stays inside its
own segment, and that is precisely what the algorithm has converged to doing.
Stated separately from `gap_ge_of_converged` because it is the design conclusion
rather than a consequence of a run: *hold to your own segment* is a rule a drone
can follow with no information about anyone else. -/
theorem gap_ge_of_hold {d : ℝ} {n : ℕ} {c : Config n}
    (hold : ∀ i : Fin n, standoffLeftEnd d i ≤ c.pos i ∧ c.pos i ≤ standoffRightEnd d i)
    (i : Fin n) (h : i.val + 1 < n) : d ≤ c.gap i h :=
  separated_of_segments i h (hold i).2 (hold (nextIdx i h)).1

end Config

end DPSS
