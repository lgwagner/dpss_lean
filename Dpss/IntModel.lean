/-
# DPSS — the model over the integers

**M1 of the Verus work package** (`PLAN.md` E1), and the thing that makes the rest
of it honest.

Verus has no real numbers: `int` and `nat` in specifications, fixed-width integers
in executable code, no rationals and no verified floats. So a Rust implementation
cannot be checked against `Dpss/Basic.lean`'s model directly — the specification has
to be restated over the integers first.

**That restatement loses nothing.** Scale positions and times by `S = 2·K·n`:

* the segment boundaries `i/n` land on the *even* integers `2·K·i`;
* a gap only ever changes by `sepRate · dt`, and `sepRate ∈ {−2, 0, +2}`, so **gap
  parity is invariant**. If the drones start on integer positions all congruent
  mod 2, every adjacent gap is even for ever — and `meetTime = gap / 2` is therefore
  always an integer;
* `borderTime` and `separationTime` are differences of integers, so every candidate
  deadline is an integer, so `dt` is an integer, so positions stay integers. When
  `dt` is odd every drone flips parity at once, which preserves "all congruent
  mod 2".

So the integer runs are a **sublattice of the real runs**, not an approximation of
them, and `convergesBy` applies to each of them unchanged. `K` sets the resolution —
`1/(K·n)` in the original units — and is free.

## Why this file exists rather than a cleverer translator

`scripts/lean_to_verus.py` generates the Verus specification from this file. The
dangerous part of any such translator is a *semantic* transformation done by
untrusted code, and ℝ → ℤ is exactly that. Doing the rescaling here, where it is
proved, leaves the generator with nothing to do but transliterate integer
arithmetic.

## Two deliberate departures from `Config`

**Predicates return `Bool`, not `Prop`.** The real model can afford `Classical` and
`noncomputable`; this one cannot, because `#eval` on it is one of the checks that
the Rust agrees with the Lean. `Bool` is also what a Verus `spec fn` returns, so the
generated code needs no encoding step.

**Bounded existentials become `dite`.** `SepRight i` is `∃ h : i.val + 1 < n, …` in
`Step.lean`; here it is `if h : i.val + 1 < n then … else false`. The two agree by
proof irrelevance, and this one is decidable.

## Reference

`Dpss/Basic.lean`, `Dpss/Dynamics.lean`, `Dpss/Events.lean`, `Dpss/Schedule.lean`,
`Dpss/NextEvent.lean` and `Dpss/Step.lean` are what this mirrors, definition for
definition.
-/

import Dpss.Nondeterminism

set_option linter.style.header false

namespace DPSS

variable {n : ℕ}

/-! ## Velocity as an integer -/

namespace Dir

/-- The velocity, as an integer: `-1` leftward, `+1` rightward. The integer twin of
`Dir.sign`. -/
def isign : Dir → ℤ
  | left => -1
  | right => 1

@[simp] theorem isign_left : isign left = -1 := rfl
@[simp] theorem isign_right : isign right = 1 := rfl

/-- Casting the integer velocity into the reals gives the real one. The one bridge
lemma the whole correspondence rests on. -/
@[simp] theorem cast_isign (d : Dir) : ((d.isign : ℤ) : ℝ) = d.sign := by
  cases d <;> norm_num [isign, sign]

@[simp] theorem isign_mul_self (d : Dir) : d.isign * d.isign = 1 := by
  cases d <;> rfl

theorem isign_ne_zero (d : Dir) : d.isign ≠ 0 := by cases d <;> decide

end Dir

/-! ## The scaled geometry

`K` is the resolution: one unit of the original perimeter is `2·K·n` integer units,
so the finest distance the integer model can express is `1/(2·K·n)`. -/

/-- The right-hand end of the perimeter, scaled. -/
def intPerimeter (K n : ℕ) : ℤ := 2 * (K : ℤ) * (n : ℤ)

/-- The left endpoint of drone `i`'s segment, scaled. Always even. -/
def intLeftEnd (K : ℕ) (i : Fin n) : ℤ := 2 * (K : ℤ) * (i.val : ℤ)

/-- The right endpoint of drone `i`'s segment, scaled. Always even. -/
def intRightEnd (K : ℕ) (i : Fin n) : ℤ := 2 * (K : ℤ) * ((i.val : ℤ) + 1)

/-- The boundary drones `i` and `i+1` share. -/
def intCommonEnd (K : ℕ) (i : Fin n) : ℤ := intRightEnd K i

theorem intRightEnd_sub_intLeftEnd (K : ℕ) (i : Fin n) :
    intRightEnd K i - intLeftEnd K i = 2 * (K : ℤ) := by
  unfold intRightEnd intLeftEnd; ring

/-! ## Configurations -/

/-- A snapshot of the team, with positions and the clock in scaled integer units. -/
structure IntConfig (n : ℕ) where
  /-- The instant, in scaled units. -/
  time : ℤ
  /-- Where each drone is, in scaled units. -/
  pos : Fin n → ℤ
  /-- Which way each drone is heading. -/
  dir : Fin n → Dir

namespace IntConfig

@[ext] theorem ext {c c' : IntConfig n} (ht : c.time = c'.time)
    (hp : c.pos = c'.pos) (hd : c.dir = c'.dir) : c = c' := by
  cases c; cases c'; simp_all

variable (c : IntConfig n)

/-! ## Motion between events -/

/-- Fly the whole team forward by `dt`. -/
def advance (dt : ℤ) : IntConfig n where
  time := c.time + dt
  pos := fun i => c.pos i + (c.dir i).isign * dt
  dir := c.dir

@[simp] theorem advance_time (dt : ℤ) : (c.advance dt).time = c.time + dt := rfl
@[simp] theorem advance_pos (dt : ℤ) (i : Fin n) :
    (c.advance dt).pos i = c.pos i + (c.dir i).isign * dt := rfl
@[simp] theorem advance_dir (dt : ℤ) : (c.advance dt).dir = c.dir := rfl

/-- The signed distance from drone `i` to its right-hand neighbour. -/
def gap (i : Fin n) (h : i.val + 1 < n) : ℤ :=
  c.pos (Config.nextIdx i h) - c.pos i

/-- The rate the gap grows: `-2`, `0` or `+2`. -/
def sepRate (i : Fin n) (h : i.val + 1 < n) : ℤ :=
  (c.dir (Config.nextIdx i h)).isign - (c.dir i).isign

/-- Drone `i` heads right and `i+1` heads left: the one configuration in which a
gap shrinks. -/
def Approaching (i : Fin n) (h : i.val + 1 < n) : Bool :=
  c.dir i == Dir.right && c.dir (Config.nextIdx i h) == Dir.left

/-- Time to collision for an approaching pair: they close at rate 2, so half the
gap. **Exact whenever the gap is even**, which `OnLattice` guarantees. -/
def meetTime (i : Fin n) (h : i.val + 1 < n) : ℤ := c.gap i h / 2

/-! ## The three events -/

def AtLeftBorder (i : Fin n) : Bool :=
  c.pos i == 0 && c.dir i == Dir.left

def AtRightBorder (K : ℕ) (i : Fin n) : Bool :=
  c.pos i == intPerimeter K n && c.dir i == Dir.right

def CoLocated (i : Fin n) (h : i.val + 1 < n) : Bool :=
  c.gap i h == 0

def Escorting (i : Fin n) (h : i.val + 1 < n) : Bool :=
  c.CoLocated i h && c.dir i == c.dir (Config.nextIdx i h)

def AtSeparation (K : ℕ) (i : Fin n) (h : i.val + 1 < n) : Bool :=
  c.CoLocated i h && c.pos i == intCommonEnd K i

/-! ## The schedule -/

def separationTime (K : ℕ) (i : Fin n) : ℤ :=
  (intCommonEnd K i - c.pos i) * (c.dir i).isign

def borderTime (K : ℕ) (i : Fin n) : ℤ :=
  if c.dir i = Dir.left then c.pos i else intPerimeter K n - c.pos i

/-- The earliest deadline for one drone. -/
def droneNextTime (K : ℕ) (i : Fin n) : ℤ :=
  if h : i.val + 1 < n then
    if c.Approaching i h then min (c.borderTime K i) (c.meetTime i h)
    else if c.Escorting i h then min (c.borderTime K i) (c.separationTime K i)
    else c.borderTime K i
  else c.borderTime K i

/-- The earliest deadline across the team. -/
def timeToNextEvent (K : ℕ) (hn : 0 < n) : ℤ :=
  Finset.univ.inf' (Config.univ_fin_nonempty hn) (c.droneNextTime K)

/-! ## Which events are due for a given drone

The bounded existentials of `Step.lean` become `dite`, which is decidable. -/

def SepRight (K : ℕ) (i : Fin n) : Bool :=
  if h : i.val + 1 < n then c.AtSeparation K i h else false

def SepLeft (K : ℕ) (i : Fin n) : Bool :=
  if h : 0 < i.val then
    c.AtSeparation K (Config.prevIdx i h) (Config.prevIdx_lt i h)
  else false

def MeetRight (i : Fin n) : Bool :=
  if h : i.val + 1 < n then c.CoLocated i h && c.Approaching i h else false

def MeetLeft (i : Fin n) : Bool :=
  if h : 0 < i.val then
    c.CoLocated (Config.prevIdx i h) (Config.prevIdx_lt i h) &&
      c.Approaching (Config.prevIdx i h) (Config.prevIdx_lt i h)
  else false

/-! ## The post-event heading -/

/-- The heading a newly met pair adopts: towards the boundary they share. -/
def escortDir (K : ℕ) (i : Fin n) : Dir :=
  if c.pos i < intCommonEnd K i then Dir.right else Dir.left

/-- And when meeting the *left* neighbour: towards this drone's own left endpoint. -/
def escortDirLeft (K : ℕ) (i : Fin n) : Dir :=
  if c.pos i < intLeftEnd K i then Dir.right else Dir.left

/-- **Algorithm A's priority order**: border, then separation, then meet, then
carry on. -/
def newDir (K : ℕ) (i : Fin n) : Dir :=
  if c.AtLeftBorder i then Dir.right
  else if c.AtRightBorder K i then Dir.left
  else if c.SepRight K i then Dir.left
  else if c.SepLeft K i then Dir.right
  else if c.MeetRight i then c.escortDir K i
  else if c.MeetLeft i then c.escortDirLeft K i
  else c.dir i

/-! ## The step, and runs -/

/-- Fly to the next event, then fire everything due. -/
def step (K : ℕ) (hn : 0 < n) : IntConfig n :=
  let c' := c.advance (c.timeToNextEvent K hn)
  { time := c'.time, pos := c'.pos, dir := fun i => c'.newDir K i }

@[simp] theorem step_time (K : ℕ) (hn : 0 < n) :
    (c.step K hn).time = c.time + c.timeToNextEvent K hn := rfl

@[simp] theorem step_pos (K : ℕ) (hn : 0 < n) (i : Fin n) :
    (c.step K hn).pos i = c.pos i + (c.dir i).isign * c.timeToNextEvent K hn := rfl

/-- The configuration after `k` steps. -/
def run (c : IntConfig n) (K : ℕ) (hn : 0 < n) : ℕ → IntConfig n
  | 0 => c
  | k + 1 => (c.run K hn k).step K hn

@[simp] theorem run_zero (K : ℕ) (hn : 0 < n) : c.run K hn 0 = c := rfl

@[simp] theorem run_succ (K : ℕ) (hn : 0 < n) (k : ℕ) :
    c.run K hn (k + 1) = (c.run K hn k).step K hn := rfl

/-! ## The standing conditions, restated -/

def OnPerimeter (K : ℕ) : Prop :=
  ∀ i : Fin n, 0 ≤ c.pos i ∧ c.pos i ≤ intPerimeter K n

def AdjOrdered : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), 0 ≤ c.gap i h

def EscortsCoherent (K : ℕ) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n),
    c.Escorting i h = true → 0 ≤ c.separationTime K i

/-- **The lattice condition.** Every adjacent gap is even — equivalently, all the
drones are congruent mod 2. This is what makes `meetTime` exact, and it is
preserved by a step because a gap only ever changes by `sepRate · dt` with
`sepRate` even. -/
def OnLattice : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n), 2 ∣ c.gap i h

structure Invariant (K : ℕ) : Prop where
  onPerimeter : c.OnPerimeter K
  adjOrdered : c.AdjOrdered
  escortsCoherent : c.EscortsCoherent K
  onLattice : c.OnLattice

end IntConfig

end DPSS
