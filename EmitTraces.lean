/-
# Emit the safety blocks of `rust/traces.expected`, from Lean

S6c. `rust/traces.sh` checks the verified binary against
`rust/traces.expected`; this executable checks `rust/traces.expected` against
**Lean**, by printing the six safety blocks — plus the link witness and the
negative control — in the binary's own format, from the definitions of
`Dpss/FenceTrace.lean`.

Those definitions are not a transcription of the harness. `Sim` is proved to
satisfy the whole vehicle contract (`Sim.trajOk`) for any well-formed vehicle
and any margin, the blocks with a sufficient margin are proved clear of the
fence by the fence theorem itself (`Sim.low_nonneg`), and every row printed
below is a `decide`-proved theorem in that file.

What this cannot attest is the `contract:` lines, which are the *Rust's*
executable specifications evaluated on the trace (S6b). `scripts/check_traces.py`
drops those before comparing, and says so.

    lake exe emit_traces
-/

import Dpss.FenceTrace

open DPSS DPSS.FenceInt

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
  fenceBlock "fence (dmax=10, turn=3, eps=2, margin=15)" fenceOk 6 ++
  fenceBlock "fence, margin short by eps (margin=13 < 10+3+2)" fenceShort 6 ++
  pairBlock "separation (dmax=10, turn=3, eps=2, d=5, margin=30)" sepOk traceD 4 ++
  pairBlock "separation, margin short by 2*eps (margin=26 < 30)" sepShort traceD 4 ++
  pairBlock "stale link (dmax=10, turn=3, eps=2, d=5, age=2, margin=50)" linkOk traceD 4 ++
  pairBlock "stale link on the fresh margin (margin=30 < 2*(10+3+2) + 2*10)"
    linkShort traceD 4 ++
  linkBlock "link (dmax=10, turn=3, eps=2, d=5, age=2, margin=50)" 2 4 ++
  badBlock "fence, vehicle contract violated (a reversal that loses ground)" 6

def main : IO Unit := blocks.forM IO.println
