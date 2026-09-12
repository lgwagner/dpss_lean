# E1 — DPSS in Rust, verified with Verus

**The approved build plan for the Rust half**, and the living record of where it has
got to. `PLAN.md` E1 is the one-paragraph version; this is the whole of it.

> Branch: **`rust-verus`**. `main` carries the finished Lean work package and is
> deliberately untouched by this, so the published artefact can be inspected without
> half-built Rust in the way.

## Status

| | Milestone | State |
|---|---|---|
| **M0** | Toolchain, pinned and scripted | ✅ `3 verified, 0 errors` |
| **M1** | The integer model, in Lean | ✅ `embed_step`, `embed_run`, `intRun_converges` |
| **M2** | The generator | ✅ 24 spec fns, fail-loud, CI-checked |
| **M3** | Verus spec and invariants | ✅ both invariants preserved, and along a run |
| **M4** | Executable code and the key equivalence | ✅ `80 verified, 0 errors` |
| **M5** | Differential testing | **next** |
| **M6** | The controller, scoped not built | not started |

**Toolchain, as pinned** (`rust/toolchain-versions.txt`, installed by
`scripts/setup_verus.sh`):

| | | |
|---|---|---|
| verus | `release/0.2026.09.06.8dea4a2` | releases roll weekly — pin, never track |
| rust | `1.98.0-x86_64-unknown-linux-gnu` | the exact toolchain that release requires |
| z3 | `4.16.0` | **not bundled** with the release; the version lives in `tools/common/consts.rs` at the pinned commit, not in `INSTALL.md` |

**Notes as the work lands** — things that were not obvious in advance, recorded here
so a bump or a restart does not rediscover them:

- Z3 is not shipped in the Verus release archive, and the required version is not
  documented where you would look for it. `EXPECTED_Z3_VERSION` in
  `tools/common/consts.rs` is the source of truth.
- `verus --crate-type=lib src/lib.rs` verifies a multi-module crate directly; no
  `cargo-verus` needed so far.
- In `Dpss/IntModel.lean`, a `variable (c : IntConfig n)` binder does **not** resolve
  inside a recursive definition — `run` has to bind `c` explicitly, which is why
  `Config.run` does too.
- The integer traces are `decide`, so the kernel checks them — but `OnLattice` is
  **not** decidable, because the index carries a dependent proof (`∀ i, ∀ h : i+1 < n`).
  Prove it from `onLattice_run` instead of recomputing; that is what the closure
  theorem is for.
- The generator refuses four things by design and they are hand-written instead:
  `advance`/`step`/`run` (structure literals and recursion), `timeToNextEvent` (a
  `Finset.inf'`), the four standing conditions (quantifiers with a dependent proof
  argument), and `Dir` itself. None is arithmetic, which is where a transcription
  error would hide.
- In an `ensures` that also mentions `old(e)`, the final value of a `&mut`
  parameter must be written `*final(e)` — plain `*e` is refused as ambiguous.
- `=~=` is sequence extensionality, not struct equality. For a struct, assert the
  sequence fields with `=~=` and then the struct with `==`.
- The ghost configuration type cannot be called `View`: that shadows `vstd`'s
  `View` trait and `Vec@` silently stops resolving. It is `Snapshot`.
- A `proof { ... }` block establishing a bound must come **before** the arithmetic
  it justifies, not after — Verus checks overflow at the operation.
- **Z3 is better at the exhaustive branch analyses than Lean is.**
  `apart_on_boundaries` preservation took ~90 lines across three lemmas in
  `Dpss/Reachable.lean`; in Verus it went through with no case split written at all,
  once the geometry facts were supplied. The `new_dir` if-chain is exactly what an
  SMT solver is good at. The *opposite* held for the real-valued reasoning, which is
  why the split of labour in this design is the right way round.
- Two things Z3 needs said out loud. The scaled geometry is **nonlinear** —
  `left_end` is `2*k*i`, a product of variables — so `geometry.rs` states the
  endpoint facts once. And multiplying by a heading's velocity is a sign flip, not a
  multiplication: `lemma_times_isign` says so once and every separation-time goal
  afterwards is linear.
- `spec fn`s carry no proof obligations, so a crate of nothing but generated
  specifications verifies **vacuously**. `rust/src/facts.rs` exists so that
  "0 errors" means something.
- `Dpss/IntModel.lean` shadows ~17 model names on purpose (`gap`, `step`, `newDir`,
  …). That broke `scripts/refresh_guide_links.py`, which keyed on bare names and
  silently dropped anything declared twice. It is now namespace-aware — worth
  knowing before adding another parallel model.

---

## Context

`~/dpss_lean` proves Theorem 2.1 — `n` patrol drones synchronize by time `2 − 1/n` —
for a Lean model of DPSS Algorithm A. 594 theorems, `sorry`-free. What it does not have
is a program: the artefact proves things *about* the algorithm, and nobody can run it.

`PLAN.md` E1 proposes closing that: an executable Rust implementation, proved in Verus
to meet the same specification. The goal is that the Lean spec **guides** the Rust — not
that a second, independently-written program happens to agree with it — and that Verus
proves the **key equivalence**: the executable step computes exactly the specified step.

Decisions taken:

| | |
|---|---|
| Artefact | Global event-stepper (what the Lean spec actually is). A per-drone controller is scoped, not built — M6. |
| Lean→Verus link | **Generated**, not hand-transcribed. |
| Proof depth | Invariants + equivalence in Verus. Convergence imported from Lean, not reproved. |

## The constraint that shapes everything

**Verus has no real numbers.** `int`/`nat` (unbounded) in spec code, fixed-width integers
in exec code only; no rationals, no verified floats. The specification must be restated
over integers.

That restatement can be **exact**. Scale positions and times by `S = 2·K·n`:

- segment boundaries `i/n` land on the even integers `2·K·i`;
- a gap only ever changes by `sepRate · dt` with `sepRate ∈ {−2, 0, +2}`, so **gap parity
  is invariant**. If every initial position is an integer and they are all congruent mod 2,
  every adjacent gap is even forever, so `meetTime = gap/2` is always an integer;
- `borderTime` and `separationTime` are integer differences, so `dt` is an integer, so
  positions stay integers. All drones flip parity together when `dt` is odd, which
  preserves "all congruent mod 2".

So there is **no discretization error** — the integer runs are a sublattice of the real
runs, and `convergesBy` applies to each of them unchanged. `K` sets the resolution
(`1/(K·n)` in original units) and is a free parameter.

The convergence bound in integer terms: `2 − 1/n` scaled by `S` is `4·K·n − 2·K`.

## Architecture

```
Dpss/*.lean               real-valued model; convergesBy            [exists]
      │
      │  Dpss/IntModel.lean                                          [M1, Lean]
      │    IntConfig, intStep (computable), embed : IntConfig → Config n
      │    theorem embed_step, theorem intRun_convergesBy
      ▼
scripts/lean_to_verus.py  syntactic translator, restricted subset    [M2]
      ▼
rust/src/spec/*.rs        GENERATED spec fns, provenance-commented   [M3]
rust/src/inv.rs           invariant predicates, hand-written         [M3]
rust/src/exec.rs          executable step/run, hand-written          [M4]
      │   Verus proves:  e@ == spec_step(old(e)@)
      │                  invariants preserved,  no overflow
      ▼
rust/tests/traces.rs      differential test vs Lean-proved traces    [M5]
```

**Why `IntModel.lean` exists.** It keeps the generator *syntactic*. The dangerous part of
a Lean→Verus translator is a semantic transformation — here, ℝ → ℤ — done by untrusted
code. Doing the rescaling in Lean, where it is proved, leaves the generator with nothing
to do but transliterate integer arithmetic. It also makes the spec `#eval`-able in Lean,
which M5 uses.

Everything lives in the existing repo under `rust/`, so one CI run checks both halves.

## Milestones

### M0 — Toolchain

Nothing is installed: no `rustc`, no `cargo`, no `verus`, no `z3`. Network is available.

- `rustup` + the Rust toolchain Verus pins.
- A **pinned** Verus release (rolling, ~weekly; latest is `0.2026.09.06.8dea4a2`). Pin the
  exact tag in `rust/verus-version.txt` — do not track rolling.
- `rust/` cargo crate with `vstd`, one verified `hello` fn.
- `scripts/verify_rust.sh` and a CI job.

**Done when** `scripts/verify_rust.sh` reports `verification results:: N verified, 0 errors`
in CI.

### M1 — The integer model, in Lean

New `Dpss/IntModel.lean`. Mirrors the model with `pos, time : ℤ`, scale `S = 2*K*n`:

- `IntConfig`, `intGap`, `intSepRate`, `intBorderTime`, `intMeetTime` (`gap / 2`,
  exact under evenness), `intSeparationTime`, `intDroneNextTime`, `intTimeToNextEvent`
  (`Finset.inf'` over ℤ — computable), `intNewDir`, `intStep`, `intRun`;
- `OnLattice`: positions integral and all adjacent gaps even;
- `lattice_closed : OnLattice c → OnLattice (intStep c)`;
- `embed : IntConfig → Config n`, and the bridge
  `embed_step : embed (intStep c) = (embed c).step hn`;
- `intRun_convergesBy` — the `2 − 1/n` bound stated on integers as `4*K*n − 2*K`.

Reuses, do not re-derive: `Config`, `step`, `convergesBy`, `Invariant`,
`ApartOnBoundaries`, and the existing traces as test vectors.

**Done when** `lake build` is clean, `scripts/audit.py` passes, and `#eval` on the integer
image of `cfgS` reproduces `run_cfgS_4`.

**Risk.** `Finset.inf'` over ℤ is computable but may need a decidability nudge; if it
fights, replace with an explicit `List.foldl min` and prove it equals the `inf'`.

### M2 — The generator

`scripts/lean_to_verus.py`, deliberately small and **fail-loud**:

- accepts only the restricted subset the integer model uses — `if/then/else`, `+ − *`,
  integer `/` by 2, comparisons, `∀`/`∃` bounded by `n`, and calls to already-translated
  definitions;
- **refuses** anything else with a pointed error rather than guessing;
- emits a provenance comment per definition (`// from Dpss/IntModel.lean:NN`), reusing the
  deep-link machinery already in `scripts/refresh_guide_links.py`;
- CI re-runs it and fails if the checked-in output differs — same discipline as
  `refresh_status.py`.

**Done when** regenerating produces no diff, and deleting a Lean definition breaks the
build rather than silently producing stale Rust.

**Stated plainly:** the generator is trusted code that nothing verifies. The mitigations
are the restricted subset, the fail-loud policy, the freshness check, and M5.

### M3 — Verus spec and invariants

Generated `rust/src/spec/`, plus hand-written `rust/src/inv.rs`:

```rust
spec fn on_perimeter(e: View) -> bool;
spec fn adj_ordered(e: View) -> bool;
spec fn escorts_coherent(e: View) -> bool;
spec fn on_lattice(e: View) -> bool;
spec fn inv(e: View) -> bool;                  // the four above
spec fn apart_on_boundaries(e: View) -> bool;  // SEPARATE - see below
```

`ApartOnBoundaries` is **not** part of `Invariant` in Lean: it is false of arbitrary
well-formed configurations (`Counterexample.lean` exhibits four drones at `3/8`) and is a
*reachability* invariant. So Verus carries two predicates, and only `inv` is a type
invariant.

Then `proof fn`s that `spec_step` preserves each — the analogues of `onPerimeter_step`,
`adjOrdered_step`, `escortsCoherent_step`, `apartOnBoundary_step`.

**Done when** all four preservation lemmas verify.

**Risk, and why it is lower than it looks.** These proofs are linear arithmetic almost
throughout — multiplication appears only by `±1` and by `2` — which is exactly what Z3 is
good at. Expect little `nonlinear_arith`.

### M4 — Executable code and the key equivalence

`rust/src/exec.rs`:

```rust
pub struct Ensemble { n: usize, k: u64, pos: Vec<i64>, dir: Vec<Dir> }

pub exec fn step(e: &mut Ensemble)
    requires inv(old(e)@), apart_on_boundaries(old(e)@)
    ensures  inv(e@), apart_on_boundaries(e@),
             e@ == spec_step(old(e)@);           // <- the key equivalence

pub exec fn run(e: &mut Ensemble, steps: usize)
    requires inv(old(e)@), apart_on_boundaries(old(e)@)
    ensures  inv(e@), e@ == spec_run(old(e)@, steps as int);
```

Two loops carry the work: the min over drones for `timeToNextEvent`, and the per-drone
heading update. Both need loop invariants relating the partial result to the spec
function.

**Overflow.** Positions are bounded by `S`, so `i64` is ample with a proved bound. The
clock is unbounded, so **absolute time is ghost-only** (`int`); exec code computes `dt`
per step and never stores a running total. That removes the only genuine overflow hazard
rather than papering over it.

**Done when** `step` and `run` verify with no `assume`, no `external_body` in the proof
path, and `--rlimit` left at its default.

### M5 — Differential testing

`rust/tests/traces.rs` runs the executable stepper against configurations Lean has
**already proved** the trace of, and requires exact agreement:

| Lean theorem | Rust assertion |
|---|---|
| `run_cfgS_4` | `run(cfgS, 4) == cfgB(1)` |
| `run_spreadE_3` | `run(spreadE(e), 3) == atBoundary(3/2 − e)` |
| `run_cfgB` cycle | period `2/n` at `n = 3` |
| `run_spread_3` | converges at `5/4` |

Plus a randomized lattice-config comparison against `#eval` of `intRun` in Lean.

**Why this is not optional.** `GUIDE.md` §3 records the one bug this project has had: a
wrong *definition* supporting a flawless proof, invisible to 145 theorems because nothing
forced the definitions to be exercised. Porting a specification into a second system is
precisely where that recurs, and a generator moves the risk without removing it. These
traces are the check that the generated spec is the algorithm.

**Done when** all trace tests pass and a deliberately corrupted spec fn fails at least one.

### M6 — The controller, scoped not built

`rust/REFINEMENT.md`: the per-drone controller's specification, and the obligation that
`n` controllers running together realize the global step — stated precisely, sized,
**not** discharged. Names what new Lean would be needed.

## What will and will not be proved

| | |
|---|---|
| **Verus proves** | `e@ == spec_step(old(e)@)`; `on_perimeter`, `adj_ordered`, `escorts_coherent`, `on_lattice`, `apart_on_boundaries` preserved; no arithmetic overflow |
| **Lean proves** | `2 − 1/n`, sharp, for every resolution of the nondeterminism; and (M1) that the integer model refines the real one |
| **Trusted, unverified** | the generator; the Verus toolchain and Z3; the correspondence between `IntModel.lean` and the generated Rust, mitigated by M2's freshness check and M5 |

`converges_by` will be **written down** as a Verus `spec fn` so the property exists in the
Rust artefact's own language, but neither proved nor `assume`d there — an `assume` would
be a silent trust hole and nothing downstream needs it. It is documented as imported, with
the Lean theorem named.

## Verification, end to end

```bash
# Lean half
lake build && python3 scripts/audit.py && python3 scripts/no_sorry.py

# the bridge is fresh
python3 scripts/lean_to_verus.py && git diff --exit-code -- rust/src/spec/

# Rust half
cd rust && ./verify.sh          # expect "N verified, 0 errors"
cargo test                      # the trace tests

# negative controls
#  - corrupt one generated spec fn  -> a trace test must fail
#  - delete a Lean definition       -> the generator must error, not emit stale Rust
#  - remove a loop invariant        -> Verus must fail, not time out
```

## Sequencing

M0 → M1 → M2 → M3 → M4 → M5 → M6. M1 is the only one that could be reordered (M2/M3 could
start against a hand-written integer spec), but doing it first is what keeps the generator
syntactic.

**Suggested first sitting:** M0 and the skeleton of M1, ending with a verified `hello` in
CI and `IntConfig`/`intStep` compiling in Lean. That gets both toolchains proven to work
before any real proof effort is spent.
