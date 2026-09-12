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


/-! ## The lattice is closed under a step

The claim the whole integer model rests on. A gap only ever changes by
`sepRate · dt`, and `sepRate` is a difference of two `±1`s, hence even. So an even
gap stays even however long the step is — and `meetTime = gap / 2` is exact for
ever. -/

theorem gap_advance (dt : ℤ) (i : Fin n) (h : i.val + 1 < n) :
    (c.advance dt).gap i h = c.gap i h + c.sepRate i h * dt := by
  unfold gap sepRate
  simp only [advance_pos]
  ring

/-- **The rate a gap changes at is always even** — it is `-2`, `0` or `+2`. -/
theorem two_dvd_sepRate (i : Fin n) (h : i.val + 1 < n) : 2 ∣ c.sepRate i h := by
  unfold sepRate
  rcases Dir.eq_left_or_right (c.dir i) with h1 | h1 <;>
    rcases Dir.eq_left_or_right (c.dir (Config.nextIdx i h)) with h2 | h2 <;>
      rw [h1, h2] <;> decide

/-- Flying preserves the lattice, whatever the step length. -/
theorem onLattice_advance (hL : c.OnLattice) (dt : ℤ) :
    (c.advance dt).OnLattice := by
  intro i h
  rw [gap_advance]
  exact dvd_add (hL i h) (Dvd.dvd.mul_right (c.two_dvd_sepRate i h) dt)

/-- **And so does a step**, because an event changes headings and not positions. -/
theorem onLattice_step (K : ℕ) (hn : 0 < n) (hL : c.OnLattice) :
    (c.step K hn).OnLattice := by
  intro i h
  have hx : (c.step K hn).gap i h
      = (c.advance (c.timeToNextEvent K hn)).gap i h := rfl
  rw [hx]
  exact onLattice_advance c hL _ i h

theorem onLattice_run (K : ℕ) (hn : 0 < n) (hL : c.OnLattice) (k : ℕ) :
    (c.run K hn k).OnLattice := by
  induction k with
  | zero => exact hL
  | succ k ih => exact onLattice_step _ K hn ih

/-- **The payoff: on the lattice, halving a gap is exact.** This is the one place
integer division appears, and this is why it is not lossy. -/
theorem two_mul_meetTime (hL : c.OnLattice) (i : Fin n) (h : i.val + 1 < n) :
    2 * c.meetTime i h = c.gap i h := by
  have hd := hL i h
  unfold meetTime
  omega

end IntConfig

/-! ## The bridge to the real model

Everything above is a self-contained integer system. This section proves it is
*the same system*: dividing every position and time by `S = 2·K·n` turns an integer
run into a real one, step for step. The `2 − 1/n` bound therefore applies to integer
runs without being reproved, which is what lets the Rust inherit it. -/

/-- The scale, as a real. -/
noncomputable def scaleR (K n : ℕ) : ℝ := ((intPerimeter K n : ℤ) : ℝ)

theorem scaleR_eq (K n : ℕ) : scaleR K n = 2 * (K : ℝ) * (n : ℝ) := by
  unfold scaleR intPerimeter; push_cast; ring

theorem scaleR_pos (hK : 0 < K) (hn : 0 < n) : 0 < scaleR K n := by
  rw [scaleR_eq]
  have h1 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  positivity

/-! ### Dividing by a positive constant reflects the order

The three lemmas every correspondence below is built from. -/

theorem div_eq_div_iff_pos {a b S : ℝ} (hS : 0 < S) : a / S = b / S ↔ a = b := by
  have hS' : S ≠ 0 := ne_of_gt hS
  constructor
  · intro h
    field_simp at h
    exact h
  · intro h; rw [h]

theorem div_lt_div_iff_pos {a b S : ℝ} (hS : 0 < S) : a / S < b / S ↔ a < b := by
  have hS' : S ≠ 0 := ne_of_gt hS
  constructor
  · intro h
    have h2 : (a / S) * S < (b / S) * S := mul_lt_mul_of_pos_right h hS
    field_simp at h2
    exact h2
  · intro h
    have h2 : a * S⁻¹ < b * S⁻¹ := mul_lt_mul_of_pos_right h (inv_pos.mpr hS)
    simpa [div_eq_mul_inv] using h2

theorem div_le_div_iff_pos {a b S : ℝ} (hS : 0 < S) : a / S ≤ b / S ↔ a ≤ b := by
  have hS' : S ≠ 0 := ne_of_gt hS
  constructor
  · intro h
    have h2 : (a / S) * S ≤ (b / S) * S :=
      mul_le_mul_of_nonneg_right h (le_of_lt hS)
    field_simp at h2
    exact h2
  · intro h
    have h2 : a * S⁻¹ ≤ b * S⁻¹ :=
      mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hS))
    simpa [div_eq_mul_inv] using h2

namespace IntConfig

variable (c : IntConfig n)

/-- The integer configuration, read as a real one: every position and the clock
divided by the scale, headings untouched. -/
noncomputable def embed (K : ℕ) (c : IntConfig n) : Config n where
  time := (c.time : ℝ) / scaleR K n
  pos := fun i => (c.pos i : ℝ) / scaleR K n
  dir := c.dir

@[simp] theorem embed_time (K : ℕ) : (embed K c).time = (c.time : ℝ) / scaleR K n := rfl
@[simp] theorem embed_pos (K : ℕ) (i : Fin n) :
    (embed K c).pos i = (c.pos i : ℝ) / scaleR K n := rfl
@[simp] theorem embed_dir (K : ℕ) (i : Fin n) : (embed K c).dir i = c.dir i := rfl

/-! ### The geometry lines up -/

theorem embed_leftEnd (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    leftEnd i = ((intLeftEnd K i : ℤ) : ℝ) / scaleR K n := by
  have hK' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold leftEnd intLeftEnd
  rw [scaleR_eq]
  push_cast
  field_simp

theorem embed_rightEnd (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    rightEnd i = ((intRightEnd K i : ℤ) : ℝ) / scaleR K n := by
  have hK' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold rightEnd intRightEnd
  rw [scaleR_eq]
  push_cast
  field_simp

theorem embed_commonEnd (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    commonEnd i = ((intCommonEnd K i : ℤ) : ℝ) / scaleR K n :=
  embed_rightEnd hK hn i

theorem embed_one (hK : 0 < K) (hn : 0 < n) :
    (1 : ℝ) = ((intPerimeter K n : ℤ) : ℝ) / scaleR K n := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  unfold scaleR at hS ⊢
  field_simp

/-! ### Every quantity lines up -/

theorem embed_gap (K : ℕ) (i : Fin n) (h : i.val + 1 < n) :
    (embed K c).gap i h = ((c.gap i h : ℤ) : ℝ) / scaleR K n := by
  unfold Config.gap IntConfig.gap
  simp only [embed_pos]
  push_cast
  ring

theorem embed_sign (K : ℕ) (i : Fin n) :
    ((embed K c).dir i).sign = (((c.dir i).isign : ℤ) : ℝ) := by
  rw [embed_dir, Dir.cast_isign]

/-! ### Every predicate lines up -/

theorem embed_coLocated (hK : 0 < K) (hn : 0 < n) (i : Fin n) (h : i.val + 1 < n) :
    (embed K c).CoLocated i h ↔ c.CoLocated i h = true := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  unfold Config.CoLocated IntConfig.CoLocated
  rw [embed_gap, show (0 : ℝ) = ((0 : ℤ) : ℝ) / scaleR K n by simp,
    div_eq_div_iff_pos hS]
  simp

theorem embed_approaching (K : ℕ) (i : Fin n) (h : i.val + 1 < n) :
    (embed K c).Approaching i h ↔ c.Approaching i h = true := by
  unfold Config.Approaching IntConfig.Approaching
  simp [embed_dir]

theorem embed_escorting (hK : 0 < K) (hn : 0 < n) (i : Fin n) (h : i.val + 1 < n) :
    (embed K c).Escorting i h ↔ c.Escorting i h = true := by
  unfold Config.Escorting IntConfig.Escorting
  rw [Bool.and_eq_true, ← embed_coLocated c hK hn i h]
  simp [embed_dir]

theorem embed_atSeparation (hK : 0 < K) (hn : 0 < n) (i : Fin n)
    (h : i.val + 1 < n) :
    (embed K c).AtSeparation i h ↔ c.AtSeparation K i h = true := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  unfold Config.AtSeparation IntConfig.AtSeparation
  rw [Bool.and_eq_true, ← embed_coLocated c hK hn i h, embed_commonEnd hK hn,
    embed_pos, div_eq_div_iff_pos hS]
  simp

theorem embed_atLeftBorder (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).AtLeftBorder i ↔ c.AtLeftBorder i = true := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  unfold Config.AtLeftBorder IntConfig.AtLeftBorder
  rw [Bool.and_eq_true, embed_pos,
    show (0 : ℝ) = ((0 : ℤ) : ℝ) / scaleR K n by simp, div_eq_div_iff_pos hS]
  simp [embed_dir]

theorem embed_atRightBorder (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).AtRightBorder i ↔ c.AtRightBorder K i = true := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  unfold Config.AtRightBorder IntConfig.AtRightBorder
  rw [Bool.and_eq_true, embed_pos, embed_one hK hn, div_eq_div_iff_pos hS]
  simp [embed_dir]

/-! ### The schedule lines up -/

theorem cast_min_div (hK : 0 < K) (hn : 0 < n) (a b : ℤ) :
    min ((a : ℝ) / scaleR K n) ((b : ℝ) / scaleR K n)
      = ((min a b : ℤ) : ℝ) / scaleR K n := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, min_eq_left ((div_le_div_iff_pos hS).mpr (by exact_mod_cast hab))]
  · rw [min_eq_right hab, min_eq_right ((div_le_div_iff_pos hS).mpr (by exact_mod_cast hab))]

theorem embed_borderTime (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).borderTime i = ((c.borderTime K i : ℤ) : ℝ) / scaleR K n := by
  unfold Config.borderTime IntConfig.borderTime
  by_cases hd : c.dir i = Dir.left
  · rw [if_pos (show (embed K c).dir i = Dir.left from hd), if_pos hd, embed_pos]
  · rw [if_neg (show ¬ (embed K c).dir i = Dir.left from hd), if_neg hd, embed_pos,
      embed_one hK hn]
    push_cast
    ring

theorem embed_separationTime (K : ℕ) (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).separationTime i = ((c.separationTime K i : ℤ) : ℝ) / scaleR K n := by
  unfold Config.separationTime IntConfig.separationTime
  rw [embed_commonEnd hK hn, embed_pos, embed_sign]
  push_cast
  ring

theorem embed_meetTime (hK : 0 < K) (hn : 0 < n) (hL : c.OnLattice) (i : Fin n)
    (h : i.val + 1 < n) :
    (embed K c).meetTime i h = ((c.meetTime i h : ℤ) : ℝ) / scaleR K n := by
  have hx : 2 * c.meetTime i h = c.gap i h := two_mul_meetTime c hL i h
  have hx' : ((c.gap i h : ℤ) : ℝ) = 2 * ((c.meetTime i h : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hx.symm
  unfold Config.meetTime
  rw [embed_gap, hx']
  ring

theorem embed_droneNextTime (hK : 0 < K) (hn : 0 < n) (hL : c.OnLattice) (i : Fin n) :
    (embed K c).droneNextTime i = ((c.droneNextTime K i : ℤ) : ℝ) / scaleR K n := by
  unfold Config.droneNextTime IntConfig.droneNextTime
  by_cases h : i.val + 1 < n
  · rw [dif_pos h, dif_pos h]
    by_cases hA : c.Approaching i h = true
    · rw [if_pos ((embed_approaching c K i h).mpr hA), if_pos hA,
        embed_borderTime c hK hn, embed_meetTime c hK hn hL, cast_min_div hK hn]
    · rw [if_neg (fun hx => hA ((embed_approaching c K i h).mp hx)), if_neg hA]
      by_cases hE : c.Escorting i h = true
      · rw [if_pos ((embed_escorting c hK hn i h).mpr hE), if_pos hE,
          embed_borderTime c hK hn, embed_separationTime c K hK hn,
          cast_min_div hK hn]
      · rw [if_neg (fun hx => hE ((embed_escorting c hK hn i h).mp hx)), if_neg hE,
          embed_borderTime c hK hn]
  · rw [dif_neg h, dif_neg h, embed_borderTime c hK hn]

theorem embed_timeToNextEvent (hK : 0 < K) (hn : 0 < n) (hL : c.OnLattice) :
    (embed K c).timeToNextEvent hn
      = ((c.timeToNextEvent K hn : ℤ) : ℝ) / scaleR K n := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  refine le_antisymm ?_ ?_
  · obtain ⟨j, -, hj⟩ :=
      Finset.exists_mem_eq_inf' (Config.univ_fin_nonempty hn) (c.droneNextTime K)
    calc (embed K c).timeToNextEvent hn
        ≤ (embed K c).droneNextTime j :=
          Finset.inf'_le _ (Finset.mem_univ j)
      _ = ((c.droneNextTime K j : ℤ) : ℝ) / scaleR K n :=
          embed_droneNextTime c hK hn hL j
      _ = ((c.timeToNextEvent K hn : ℤ) : ℝ) / scaleR K n := by
          unfold IntConfig.timeToNextEvent; rw [hj]
  · refine Finset.le_inf' _ _ (fun j _ => ?_)
    rw [embed_droneNextTime c hK hn hL j]
    refine (div_le_div_iff_pos hS).mpr ?_
    exact_mod_cast Finset.inf'_le (c.droneNextTime K) (Finset.mem_univ j)

/-! ### The post-event heading lines up -/

theorem embed_escortDir (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).escortDir i = c.escortDir K i := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  unfold Config.escortDir IntConfig.escortDir
  by_cases hx : c.pos i < intCommonEnd K i
  · rw [if_pos hx, if_pos]
    rw [embed_pos, embed_commonEnd hK hn]
    exact (div_lt_div_iff_pos hS).mpr (by exact_mod_cast hx)
  · rw [if_neg hx, if_neg]
    rw [embed_pos, embed_commonEnd hK hn]
    intro hc
    exact hx (by exact_mod_cast (div_lt_div_iff_pos hS).mp hc)

theorem embed_escortDirLeft (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).escortDirLeft i = c.escortDirLeft K i := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  unfold Config.escortDirLeft IntConfig.escortDirLeft
  by_cases hx : c.pos i < intLeftEnd K i
  · rw [if_pos hx, if_pos]
    rw [embed_pos, embed_leftEnd hK hn]
    exact (div_lt_div_iff_pos hS).mpr (by exact_mod_cast hx)
  · rw [if_neg hx, if_neg]
    rw [embed_pos, embed_leftEnd hK hn]
    intro hc
    exact hx (by exact_mod_cast (div_lt_div_iff_pos hS).mp hc)

/-! ### The four "what is due for me" predicates line up

`Step.lean` phrases them as bounded existentials; here they are `dite`. The two
agree by proof irrelevance. -/

theorem embed_sepRight (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).SepRight i ↔ c.SepRight K i = true := by
  unfold Config.SepRight IntConfig.SepRight
  by_cases h : i.val + 1 < n
  · rw [dif_pos h]
    constructor
    · rintro ⟨h', hs⟩; exact (embed_atSeparation c hK hn i h).mp hs
    · intro hs; exact ⟨h, (embed_atSeparation c hK hn i h).mpr hs⟩
  · rw [dif_neg h]
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨h', -⟩; exact h h'

theorem embed_sepLeft (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).SepLeft i ↔ c.SepLeft K i = true := by
  unfold Config.SepLeft IntConfig.SepLeft
  by_cases h : 0 < i.val
  · rw [dif_pos h]
    constructor
    · rintro ⟨h', hs⟩
      exact (embed_atSeparation c hK hn _ (Config.prevIdx_lt i h)).mp hs
    · intro hs
      exact ⟨h, (embed_atSeparation c hK hn _ (Config.prevIdx_lt i h)).mpr hs⟩
  · rw [dif_neg h]
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨h', -⟩; exact h h'

theorem embed_meetRight (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).MeetRight i ↔ c.MeetRight i = true := by
  unfold Config.MeetRight IntConfig.MeetRight
  by_cases h : i.val + 1 < n
  · rw [dif_pos h, Bool.and_eq_true]
    constructor
    · rintro ⟨h', hco, hA⟩
      exact ⟨(embed_coLocated c hK hn i h).mp hco, (embed_approaching c K i h).mp hA⟩
    · rintro ⟨hco, hA⟩
      exact ⟨h, (embed_coLocated c hK hn i h).mpr hco,
        (embed_approaching c K i h).mpr hA⟩
  · rw [dif_neg h]
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨h', -⟩; exact h h'

theorem embed_meetLeft (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).MeetLeft i ↔ c.MeetLeft i = true := by
  unfold Config.MeetLeft IntConfig.MeetLeft
  by_cases h : 0 < i.val
  · rw [dif_pos h, Bool.and_eq_true]
    constructor
    · rintro ⟨h', hco, hA⟩
      exact ⟨(embed_coLocated c hK hn _ (Config.prevIdx_lt i h)).mp hco,
        (embed_approaching c K _ (Config.prevIdx_lt i h)).mp hA⟩
    · rintro ⟨hco, hA⟩
      exact ⟨h, (embed_coLocated c hK hn _ (Config.prevIdx_lt i h)).mpr hco,
        (embed_approaching c K _ (Config.prevIdx_lt i h)).mpr hA⟩
  · rw [dif_neg h]
    simp only [Bool.false_eq_true, iff_false]
    rintro ⟨h', -⟩; exact h h'

/-! ### And therefore the whole heading update -/

theorem embed_newDir (hK : 0 < K) (hn : 0 < n) (i : Fin n) :
    (embed K c).newDir i = c.newDir K i := by
  unfold Config.newDir IntConfig.newDir
  by_cases h1 : c.AtLeftBorder i = true
  · rw [if_pos ((embed_atLeftBorder c hK hn i).mpr h1), if_pos h1]
  rw [if_neg (fun hx => h1 ((embed_atLeftBorder c hK hn i).mp hx)), if_neg h1]
  by_cases h2 : c.AtRightBorder K i = true
  · rw [if_pos ((embed_atRightBorder c hK hn i).mpr h2), if_pos h2]
  rw [if_neg (fun hx => h2 ((embed_atRightBorder c hK hn i).mp hx)), if_neg h2]
  by_cases h3 : c.SepRight K i = true
  · rw [if_pos ((embed_sepRight c hK hn i).mpr h3), if_pos h3]
  rw [if_neg (fun hx => h3 ((embed_sepRight c hK hn i).mp hx)), if_neg h3]
  by_cases h4 : c.SepLeft K i = true
  · rw [if_pos ((embed_sepLeft c hK hn i).mpr h4), if_pos h4]
  rw [if_neg (fun hx => h4 ((embed_sepLeft c hK hn i).mp hx)), if_neg h4]
  by_cases h5 : c.MeetRight i = true
  · rw [if_pos ((embed_meetRight c hK hn i).mpr h5), if_pos h5,
      embed_escortDir c hK hn]
  rw [if_neg (fun hx => h5 ((embed_meetRight c hK hn i).mp hx)), if_neg h5]
  by_cases h6 : c.MeetLeft i = true
  · rw [if_pos ((embed_meetLeft c hK hn i).mpr h6), if_pos h6,
      embed_escortDirLeft c hK hn]
  rw [if_neg (fun hx => h6 ((embed_meetLeft c hK hn i).mp hx)), if_neg h6, embed_dir]

/-! ## The bridge

One step of the integer system, read as a real configuration, is one step of the
real system. -/

theorem embed_advance (K : ℕ) (dt : ℤ) :
    embed K (c.advance dt) = (embed K c).advance ((dt : ℝ) / scaleR K n) := by
  refine Config.ext ?_ (funext fun i => ?_) rfl
  · show ((c.time + dt : ℤ) : ℝ) / scaleR K n
      = (c.time : ℝ) / scaleR K n + (dt : ℝ) / scaleR K n
    push_cast; ring
  · show ((c.pos i + (c.dir i).isign * dt : ℤ) : ℝ) / scaleR K n
      = (c.pos i : ℝ) / scaleR K n + ((c.dir i).sign) * ((dt : ℝ) / scaleR K n)
    rw [← Dir.cast_isign]
    push_cast; ring

/-- **The step commutes with the embedding.** -/
theorem embed_step (hK : 0 < K) (hn : 0 < n) (hL : c.OnLattice) :
    embed K (c.step K hn) = (embed K c).step hn := by
  have hdt := embed_timeToNextEvent c hK hn hL
  refine Config.ext ?_ (funext fun i => ?_) (funext fun i => ?_)
  · show ((c.time + c.timeToNextEvent K hn : ℤ) : ℝ) / scaleR K n
      = (embed K c).time + (embed K c).timeToNextEvent hn
    rw [hdt, embed_time]; push_cast; ring
  · show ((c.pos i + (c.dir i).isign * c.timeToNextEvent K hn : ℤ) : ℝ) / scaleR K n
      = (embed K c).pos i
        + ((embed K c).dir i).sign * (embed K c).timeToNextEvent hn
    rw [hdt, embed_pos, embed_sign]
    push_cast; ring
  · show (c.advance (c.timeToNextEvent K hn)).newDir K i
      = ((embed K c).advance ((embed K c).timeToNextEvent hn)).newDir i
    rw [hdt, ← embed_advance]
    exact (embed_newDir (c.advance (c.timeToNextEvent K hn)) hK hn i).symm

/-- **And therefore the whole run.** -/
theorem embed_run (hK : 0 < K) (hn : 0 < n) (hL : c.OnLattice) (k : ℕ) :
    embed K (c.run K hn k) = (embed K c).run hn k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [IntConfig.run_succ, Config.run_succ, ← ih,
      embed_step _ hK hn (onLattice_run c K hn hL k)]

/-! ## Theorem 2.1, on the integers

The point of the whole file: an integer run inherits the `2 − 1/n` bound, which in
scaled units is `4·K·n − 2·K`. Nothing is reproved — `Config.convergesBy` is applied
to the embedded run. -/

theorem intRun_converges (hK : 0 < K) (hn : 0 < n) (hL : c.OnLattice)
    (hi : (embed K c).Invariant) (hab : (embed K c).ApartOnBoundaries)
    (i : Fin n) (j : ℕ)
    (hj : c.time + (4 * (K : ℤ) * (n : ℤ) - 2 * (K : ℤ)) ≤ (c.run K hn j).time) :
    intLeftEnd K i ≤ (c.run K hn j).pos i ∧
      (c.run K hn j).pos i ≤ intRightEnd K i := by
  have hS := scaleR_pos (K := K) (n := n) hK hn
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- the scaled deadline, read as a real one, is the paper's `2 − 1/n`
  have hbound : ((4 * (K : ℤ) * (n : ℤ) - 2 * (K : ℤ) : ℤ) : ℝ) / scaleR K n
      = 2 - 1 / (n : ℝ) := by
    rw [scaleR_eq]; push_cast; field_simp; ring
  have hreal : (embed K c).time + (2 - 1 / (n : ℝ))
      ≤ ((embed K c).run hn j).time := by
    rw [← embed_run c hK hn hL j, ← hbound]
    simp only [embed_time]
    have hmono :
        ((c.time + (4 * (K : ℤ) * (n : ℤ) - 2 * (K : ℤ)) : ℤ) : ℝ) / scaleR K n
          ≤ (((c.run K hn j).time : ℤ) : ℝ) / scaleR K n :=
      (div_le_div_iff_pos hS).mpr (by exact_mod_cast hj)
    have hsplit :
        ((c.time + (4 * (K : ℤ) * (n : ℤ) - 2 * (K : ℤ)) : ℤ) : ℝ) / scaleR K n
          = (c.time : ℝ) / scaleR K n
            + ((4 * (K : ℤ) * (n : ℤ) - 2 * (K : ℤ) : ℤ) : ℝ) / scaleR K n := by
      push_cast; ring
    rw [hsplit] at hmono
    exact hmono
  obtain ⟨h1, h2⟩ := Config.convergesBy hn hi hab i j hreal
  rw [← embed_run c hK hn hL j] at h1 h2
  rw [embed_leftEnd hK hn] at h1
  rw [embed_rightEnd hK hn] at h2
  rw [embed_pos] at h1 h2
  exact ⟨by exact_mod_cast (div_le_div_iff_pos hS).mp h1,
    by exact_mod_cast (div_le_div_iff_pos hS).mp h2⟩

end IntConfig

/-! ## A trace, checked against one the real model already proved

`ThreeConverge.lean` proves the run of `cfgS` — three drones on their own left
endpoints, all heading right — step by step, and `Dpss/ThreeConverge.lean` §C2
records where it goes. Scaling by `S = 2·1·3 = 6` turns `0, 1/3, 2/3` into
`0, 2, 4`, and the integer model had better reproduce the same trace.

It does, and the third step is the interesting one: the drones land on `3, 5, 5`,
which are **odd**. Positions do not stay even — what stays even is every *gap*, and
that is exactly what `meetTime = gap / 2` needs. A step of odd length flips every
drone's parity at once, which is why the invariant is "all congruent mod 2" rather
than "all even".

These are `decide`, so the kernel checks them; they are not `#eval` output that
nobody reads. -/

namespace IntExamples

open IntConfig

theorem hn3 : 0 < 3 := by norm_num

/-- The scaled image of `ThreeConverge.cfgS`, at resolution `K = 1`. -/
def cfgSI : IntConfig 3 where
  time := 0
  pos := fun i => 2 * (i.val : ℤ)
  dir := fun _ => Dir.right

/-- It starts on the lattice: every gap is `2`. -/
theorem cfgSI_onLattice : cfgSI.OnLattice := by
  intro i h
  have hg : cfgSI.gap i h = 2 := by
    show 2 * ((Config.nextIdx i h).val : ℤ) - 2 * (i.val : ℤ) = 2
    rw [Config.nextIdx_val]
    push_cast
    ring
  exact ⟨1, by omega⟩

/-- Step 1 — the right drone reaches the far border. Real `t = 1/3`, positions
`1/3, 2/3, 1`; scaled, `t = 2` and `2, 4, 6`. -/
theorem cfgSI_run_1 :
    (cfgSI.run 1 hn3 1).time = 2 ∧
    (cfgSI.run 1 hn3 1).pos = ![2, 4, 6] ∧
    (cfgSI.run 1 hn3 1).dir = ![Dir.right, Dir.right, Dir.left] := by decide

/-- Step 2 — middle and right meet at `5/6` and escort back. Scaled, `t = 3` and
`3, 5, 5`: **odd**, and every gap still even. -/
theorem cfgSI_run_2 :
    (cfgSI.run 1 hn3 2).time = 3 ∧
    (cfgSI.run 1 hn3 2).pos = ![3, 5, 5] ∧
    (cfgSI.run 1 hn3 2).dir = ![Dir.right, Dir.left, Dir.left] := by decide

/-- Step 3 — all three at one point, the three-way meeting. Scaled, `t = 4` and
`4, 4, 4`. -/
theorem cfgSI_run_3 :
    (cfgSI.run 1 hn3 3).time = 4 ∧
    (cfgSI.run 1 hn3 3).pos = ![4, 4, 4] ∧
    (cfgSI.run 1 hn3 3).dir = ![Dir.left, Dir.left, Dir.right] := by decide

/-- Step 4 — the steady state `cfgB`. Real `t = 1`, positions `1/3, 1/3, 1`;
scaled, `t = 6` and `2, 2, 6`. Compare `ThreeConverge.run_cfgS_4`. -/
theorem cfgSI_run_4 :
    (cfgSI.run 1 hn3 4).time = 6 ∧
    (cfgSI.run 1 hn3 4).pos = ![2, 2, 6] ∧
    (cfgSI.run 1 hn3 4).dir = ![Dir.left, Dir.right, Dir.left] := by decide

/-- And the parity claim, at the step that flips it — from the closure theorem
rather than by recomputing, which is the point of having one. -/
theorem cfgSI_lattice_at_2 : (cfgSI.run 1 hn3 2).OnLattice :=
  onLattice_run cfgSI 1 hn3 cfgSI_onLattice 2

end IntExamples

end DPSS
