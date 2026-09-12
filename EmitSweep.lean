/-
# Sweep the state space, from Lean

S7c. `rust/traces.expected` is ten hand-chosen configurations. This is the
generated counterpart: for each `(n, K)` below, **every** position vector in
`[0, 2Kn]^n` and every heading vector is enumerated, filtered to those
satisfying the standing conditions and `ApartOnBoundaries`, run for a fixed
number of steps, and reduced to one line.

Why this is worth having on top of the traces: the hand-chosen blocks exercise
`advance`, `step`, `run` and `timeToNextEvent` — the definitions
`scripts/lean_to_verus.py` refuses to translate, so the Rust hand-writes them —
on two runs. A transcription error surviving *all* of these would have to be
invisible on every reachable configuration of every small team.

The filter is part of the test, not scaffolding around it. Both sides decide
membership with their own implementation of the standing conditions, so if the
two disagree about which configurations are valid, the sweeps have different
lengths and the diff says so before any trajectory is compared.

Each line carries the final state *and* a rolling digest of every intermediate
one, so a divergence that is repaired by the last step still shows. The digest
is deliberately trivial arithmetic over small nonnegative integers: `%` is then
the same operation in Lean's `ℤ` and Rust's `i64`, which it is not in general.

    lake env lean --run EmitSweep.lean
-/

import Dpss.IntModel

open DPSS DPSS.IntConfig

/-- `<`/`>`, as the harness prints a heading. -/
def sarrow : Dir → String
  | Dir.left => "<"
  | Dir.right => ">"

/-- A configuration from literal positions and headings. -/
def mkS (n : ℕ) (ps : List ℤ) (ds : List Dir) : IntConfig n where
  time := 0
  pos := fun i => ps.getD i.val 0
  dir := fun i => ds.getD i.val Dir.right

/-- Every position vector in the box, first coordinate varying slowest. -/
def posVectors : ℕ → ℕ → List (List ℤ)
  | 0,     _    => [[]]
  | m + 1, perim =>
    (List.range (perim + 1)).flatMap fun p =>
      (posVectors m perim).map fun rest => (p : ℤ) :: rest

/-- Every heading vector, bit `i` of the counter giving drone `i`. -/
def dirVectors (n : ℕ) : List (List Dir) :=
  (List.range (2 ^ n)).map fun m =>
    (List.range n).map fun i => if (m >>> i) % 2 == 1 then Dir.left else Dir.right

/-- One state, reduced to a nonnegative integer. Every term is nonnegative, which
is what makes the digest below agree between `ℤ` and `i64`. -/
def rowVal {n : ℕ} (c : IntConfig n) : ℤ :=
  (List.finRange n).foldl
    (fun a i => a + (c.pos i + 1) * (i.val + 1)
      + (match c.dir i with | Dir.left => 1 | Dir.right => 2) * (i.val + 11))
    c.time

/-- The states of the run, in order. `run` recomputes from the start for each
index, which is quadratic and, over a sweep this size, the difference between
seconds and not finishing. -/
def runList {n : ℕ} (c : IntConfig n) (K : ℕ) (hn : 0 < n) (steps : ℕ) :
    List (IntConfig n) :=
  ((List.range steps).foldl
    (fun acc _ => match acc with
      | [] => []
      | s :: rest => s.step K hn :: s :: rest) [c]).reverse

/-- A rolling digest of every state of the run, the last one included. -/
def digest {n : ℕ} (ss : List (IntConfig n)) : ℤ :=
  ss.foldl (fun h s => (h * 131 + rowVal s) % 1000003) 0

def sweepLine {n : ℕ} (c : IntConfig n) (K : ℕ) (hn : 0 < n) (steps : ℕ) : String :=
  let ss := runList c K hn steps
  let e := ss.getLastD c
  let ps := (List.finRange n).map fun i => toString (c.pos i)
  let ds := (List.finRange n).map fun i => sarrow (c.dir i)
  let qs := (List.finRange n).map fun i => toString (e.pos i)
  let es := (List.finRange n).map fun i => sarrow (e.dir i)
  s!"pos=[{",".intercalate ps}] dir=[{",".intercalate ds}] -> " ++
    s!"t={e.time} end=[{",".intercalate qs}] dirs=[{",".intercalate es}] " ++
    s!"h={digest ss}"

def sweepFor (n : ℕ) (hn : 0 < n) (K : ℕ) (steps : ℕ) : List String :=
  let perim := 2 * K * n
  let cfgs := (posVectors n perim).flatMap fun ps =>
    (dirVectors n).filterMap fun ds =>
      let c : IntConfig n := mkS n ps ds
      if c.invariantB K && c.apartOnBoundariesB K then some c else none
  let total := (perim + 1) ^ n * 2 ^ n
  s!"--- sweep n={n} K={K} steps={steps} (valid={cfgs.length} of {total}) ---" ::
    cfgs.map fun c => sweepLine c K hn steps

theorem shn2 : 0 < 2 := by norm_num
theorem shn3 : 0 < 3 := by norm_num
theorem shn4 : 0 < 4 := by norm_num

def sweep : List String :=
  sweepFor 2 shn2 1 6 ++
  sweepFor 2 shn2 2 6 ++
  sweepFor 3 shn3 1 6 ++
  sweepFor 3 shn3 2 6 ++
  sweepFor 4 shn4 1 6

def main : IO Unit := sweep.forM IO.println
