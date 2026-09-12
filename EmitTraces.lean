/-
# Emit **all** of `rust/traces.expected`, from Lean

S6c, completed by S7. `rust/traces.sh` checks the verified binary against
`rust/traces.expected`; this executable checks `rust/traces.expected` against
**Lean**, by printing every block in the binary's own format, from the Lean
definitions. `scripts/check_traces.py` compares the two.

Two halves, two sources, and they are different in kind:

* the **team** blocks (`cfgS`, `spread`) come from `Dpss/IntModel.lean`, run by
  `IntConfig.run` — the integer model whose equivalence to the real-valued model
  is proved there (`embed_step`, `intRun_converges`). Every row is also pinned
  as a `decide`-proved theorem (`cfgSI_run_1` .. `_4`, `spreadI_run_1` .. `_3`),
  so the numbers are attested twice, once by execution and once by proof.
* the **safety** blocks come from `Dpss/FenceTrace.lean`. Those definitions are
  not a transcription of the harness either: `Sim` is proved to satisfy the whole
  vehicle contract (`Sim.trajOk`) for any well-formed vehicle and any margin, the
  blocks with a sufficient margin are proved clear of the fence by the fence
  theorem itself (`Sim.low_nonneg`), and every row is a `decide`-proved theorem.

Why the team blocks matter here specifically: `advance`, `step`, `run` and
`timeToNextEvent` are the four definitions `scripts/lean_to_verus.py` refuses to
translate, so they are hand-written on the Rust side and the generator does not
check them. These two blocks are the only thing that exercises them end to end.

What this cannot attest is the `contract:` lines, which are the *Rust's*
executable specifications evaluated on the trace (S6b). `scripts/check_traces.py`
drops those before comparing, and says so.

    lake exe emit_traces
-/

import Dpss.FenceTrace
import Dpss.IntModel

open DPSS DPSS.FenceInt DPSS.IntExamples

/-- A heading, as the harness prints it. -/
def hdr (name : String) : String := s!"--- {name} ---"

/-- `<` for a drone still heading at the fence, `>` for one that has reversed. -/
def arrow : Dir → String
  | Dir.left => "<"
  | Dir.right => ">"

/-- `closing` / `apart`, padded as the harness pads them. -/
def mode : Dir → String
  | Dir.left => "closing"
  | Dir.right => "apart  "

/-- A team block, in the harness's format: the configuration at each event,
printed from `IntConfig.run`. `render` is the Lean twin of `render` in
`rust/src/main.rs`. -/
def render {n : ℕ} (c : IntConfig n) : String :=
  let ps := (List.finRange n).map fun i => toString (c.pos i)
  let ds := (List.finRange n).map fun i => arrow (c.dir i)
  s!"t={c.time} pos=[{",".intercalate ps}] dir=[{",".intercalate ds}]"

def teamBlock {n : ℕ} (name : String) (c : IntConfig n) (K : ℕ) (hn : 0 < n)
    (steps : ℕ) : List String :=
  hdr name :: (List.range (steps + 1)).map fun k => render (c.run K hn k)

/-! ### The standing conditions

`OnPerimeter`, `AdjOrdered`, `EscortsCoherent` and `OnLattice` are the four
definitions `scripts/lean_to_verus.py` refuses to translate, so the Rust holds
hand-written transcriptions of them; and being Verus `spec fn`s they never
executed, so nothing exercised them either. S7b gave both sides an executable
form — `Dpss/IntModel.lean`'s `Bool` twins here, `rust/src/exec.rs`'s `*_ex`
functions there — and this block is where the two are compared.

Most of the rows below **violate** something on purpose. A block of states that
all satisfy the conditions would not test the transcriptions at all: `repr_ok`
asserts `inv`, so on a valid state a wrong transcription and a right one both
answer `true`. What separates them is which states they reject.

`ord`, `esc` and `lat` print as `-` when `perim` is false. That is not
squeamishness: the Rust may not evaluate the other three until the position
bounds are known, because those bounds are what stop the gap subtraction from
overflowing (`repr_bounded` in `rust/src/exec.rs`). Lean could evaluate them
anyway, and mirrors the gate instead so the two outputs are comparable.

`ApartOnBoundaries` is *not* here. It is stated in `Dpss/InductionStep.lean`
over the real-valued `Config`, not over `IntConfig`, so Lean has nothing to
evaluate; the Rust reports its own on a `contract:` line, which is dropped
before comparison. -/

def tf : Bool → String
  | true => "T"
  | false => "F"

/-- A configuration from literal positions and headings, as the harness builds
one. -/
def mkI (n : ℕ) (ps : List ℤ) (ds : List Dir) : IntConfig n where
  time := 0
  pos := fun i => ps.getD i.val 0
  dir := fun i => ds.getD i.val Dir.right

def condRow (label : String) (n K : ℕ) (ps : List ℤ) (ds : List Dir) : String :=
  let c : IntConfig n := mkI n ps ds
  if c.onPerimeterB K then
    s!"c={label} perim=T ord={tf c.adjOrderedB} esc={tf (c.escortsCoherentB K)} " ++
      s!"lat={tf c.onLatticeB} inv={tf (c.invariantB K)}"
  else
    s!"c={label} perim=F ord=- esc=- lat=- inv=F"

open Dir in
def condBlock : List String :=
  hdr "standing conditions" ::
  [ condRow "cfgS@0"            3 1 [0, 2, 4] [right, right, right]
  , condRow "cfgS@2"            3 1 [3, 5, 5] [right, left,  left ]
  , condRow "spread@1"          2 2 [6, 8]    [right, left ]
  , condRow "off-perimeter"     3 1 [0, 2, 8] [right, right, right]
  , condRow "unordered"         3 1 [0, 4, 2] [right, right, right]
  , condRow "off-lattice"       3 1 [0, 1, 4] [right, right, right]
  , condRow "escort-incoherent" 3 1 [4, 4, 4] [right, right, right]
  , condRow "inv-but-not-apart" 3 1 [3, 3, 5] [left,  right, right] ]

/-- A fence block: position, observation, heading, low-water mark. -/
def fenceBlock (name : String) (S : Sim) (n : ℕ) : List String :=
  let rows := (List.range n).map fun k =>
    s!"k={k} p={S.p k} obs={S.obs k} dir={arrow (S.dir k)} low={S.low k}"
  let lows := (List.range n).map S.low
  let m := lows.foldl min (S.low 0)
  hdr name :: rows ++
    [s!"min low = {m}  ({if m ≥ 0 then "clear of the fence" else "BREACH"})"]

/-- A pair block: the same trajectory, shifted by the standoff and printed as a
gap. -/
def pairBlock (name : String) (S : Sim) (d : ℤ) (n : ℕ) : List String :=
  let rows := (List.range n).map fun k =>
    s!"k={k} gap={S.p k + d} obs={S.obs k + d} mode={mode (S.dir k)} low={S.low k + d}"
  let lows := (List.range n).map fun k => S.low k + d
  let m := lows.foldl min (S.low 0 + d)
  hdr name :: rows ++
    [s!"min low = {m}  (standoff {d}; " ++
      (if m ≥ d then "clear of the standoff)" else "BREACH)")]

/-- The link witness: two positions, the gap between them, and the report held. -/
def linkBlock (name : String) (a n : ℕ) : List String :=
  hdr name :: (List.range n).map fun k =>
    s!"k={k} p={linkOwn k} q={linkNbr k} gap={linkOk.p k + traceD} " ++
      s!"src={linkSrc a k} rep={linkRep a k}"

/-- The negative control: a reversal that loses ground. -/
def badBlock (name : String) (n : ℕ) : List String :=
  hdr name :: (List.range n).map fun k =>
    s!"k={k} p={badP k} obs={badP k + traceV.eps} dir={arrow (badDir k)} low={badLow k}"

def blocks : List String :=
  teamBlock "cfgS  (n=3, K=1)" cfgSI 1 hn3 4 ++
  teamBlock "spread (n=2, K=2)" spreadI 2 hn2 3 ++
  fenceBlock "fence (dmax=10, turn=3, eps=2, margin=15)" fenceOk 6 ++
  fenceBlock "fence, margin short by eps (margin=13 < 10+3+2)" fenceShort 6 ++
  pairBlock "separation (dmax=10, turn=3, eps=2, d=5, margin=30)" sepOk traceD 4 ++
  pairBlock "separation, margin short by 2*eps (margin=26 < 30)" sepShort traceD 4 ++
  pairBlock "stale link (dmax=10, turn=3, eps=2, d=5, age=2, margin=50)" linkOk traceD 4 ++
  pairBlock "stale link on the fresh margin (margin=30 < 2*(10+3+2) + 2*10)"
    linkShort traceD 4 ++
  linkBlock "link (dmax=10, turn=3, eps=2, d=5, age=2, margin=50)" 2 4 ++
  condBlock ++
  badBlock "fence, vehicle contract violated (a reversal that loses ground)" 6

def main : IO Unit := blocks.forM IO.println
