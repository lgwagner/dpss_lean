# The assurance argument

**Why this file exists.** `STATUS.md` records what is proved, definition by
definition. This file does something different: it states one top-level claim
about the Rust implementation, decomposes it into the links a reader would have
to believe, names the evidence for each link, and — the part that makes it an
assurance argument rather than a summary — says for each link **what it does not
cover**, and where the next link has to pick that up.

An argument like this is only worth reading if it is falsifiable. So every claim
below cites a file, a theorem, or a command with a number attached, and §5 lists
the residual risks in the order I would attack them. If you want to disagree with
the conclusion, §5 is where to start; if you want to check it, §7 is the
commands.

**The claim is deliberately narrow.** It is about the relationship between two
artefacts in this repository. It is not a claim that DPSS is safe to fly, and
§2's assumptions and §5's D4 and D5 say why not.

---

## 1. The top claim

> **G1.** For every ensemble whose view satisfies the standing conditions,
> `ApartOnBoundaries`, and the machine-integer bounds, the executable Rust in
> `rust/src` computes exactly the configuration that the Lean specification of
> DPSS Algorithm A prescribes — for one step, and hence for any finite run.

Stated in the crate's own language, the load-bearing sentence is the `ensures`
of `step_ex` (`rust/src/exec.rs`):

```rust
requires  repr_ok(*old(e)), apart_on_boundaries(view_of(*old(e)))
ensures   repr_ok(*final(e)),
          apart_on_boundaries(view_of(*final(e))),
          view_of(*final(e)) == spec_step(view_of(*old(e)))
```

and its iterate for runs, `run_ex`, against `spec_run`. This is a statement about
**all** inputs meeting the precondition, discharged by proof, not by testing.

G1 has two halves, and they are assured by different means:

* that the Rust agrees with **the Verus specification** — proof (§3, L3);
* that the Verus specification is **the Lean one** — partly mechanical
  translation (L2), partly proof (L1), and, for a small hand-written residue,
  test (L4).

The whole argument is really about that residue. Everything else is airtight in
a way the residue is not, and §4 exists to show the residue is exactly enumerated
rather than merely small.

---

## 2. Context and assumptions

These are the things G1 rests on that G1 does not argue for. They are
assumptions, stated so a reader can reject one and know precisely what falls.

| | assumption | argued where |
|---|---|---|
| **A1** | The real-valued Lean model is a faithful formalization of Algorithm A as Kingston–Beard–Holt define it. | Not here. `GUIDE.md`, and `STATUS.md` §3–4 — including §3.11's record of a definition that was *wrong* and what caught it. |
| **A2** | Working at integer resolution `K` loses nothing. | Proved, not assumed — see L1. Listed here because it is the step most likely to be mistaken for an assumption. |
| **A3** | The perimeter fits comfortably in `i64`: `0 < n ≤ 10⁶`, `0 < k ≤ 10⁶`, `2kn ≤ 10⁹` (`fits`, `rust/src/exec.rs`). | An explicit hypothesis of every Rust theorem, not a gap. The Lean model is over unbounded `ℤ`; the Rust is correct *within* these bounds and says so. |
| **A4** | The Lean kernel, Mathlib, Verus and Z3 are sound. | Not here. Versions are pinned: `lean-toolchain` (v4.33.1), Mathlib rev v4.33.1, `rust/toolchain-versions.txt` (Verus release/0.2026.09.06.8dea4a2, Rust 1.98.0, Z3 4.16.0). |
| **A5** | The subject is a **centralized event-stepper**, which is what the Lean model specifies. It is not a per-drone controller and would not fly. | `rust/REFINEMENT.md` scopes the missing refinement precisely, and D5 below. |
| **A6** | The trace and sweep harnesses, which are unverified, report faithfully what the verified functions computed. | Mitigated rather than assumed away — D3. |

---

## 3. The argument: five links

```
  Lean, real-valued model  (Dpss/*.lean)
        │  L1  proof: embed_step, embed_run, intRun_converges
        ▼
  Lean, integer model      (Dpss/IntModel.lean)
        │  L2  mechanical translation, CI-checked          ─── 38 spec fns
        │  L4  test: traces + sweep                        ─── the residue
        ▼
  Verus specification      (rust/src/spec/*.rs, inv.rs)
        │  L3  proof, all inputs
        ▼
  Executable Rust          (rust/src/exec.rs, …)

  L5 runs underneath all four: the evidence is not vacuous.
```

### L1 — the integer model is the real-valued model

**Claim.** Reasoning at integer resolution proves the same thing as reasoning
over `ℝ`.

**Evidence.** `Dpss/IntModel.lean`: `embed_step` (`embed K (c.step K hn) =
(embed K c).step hn`), `embed_run` for iterates, and `intRun_converges`, which
carries the paper's `2 − 1/n` bound across the embedding. The family of
`embed_*` lemmas does the same for each predicate — `embed_coLocated`,
`embed_atSeparation`, `embed_apartOnBoundaries`, and the rest.

**What it does not cover.** Whether the real-valued model is the right model —
that is A1. And `embed_step` requires `OnLattice`; off the lattice the
correspondence is not claimed, which is why `OnLattice` is part of the standing
invariant rather than a convenience.

### L2 — the arithmetic specification is generated, not transcribed

**Claim.** No scalar or boolean definition of the specification was typed twice.

**Evidence.** `scripts/lean_to_verus.py` translates `Dpss/IntModel.lean`,
`Dpss/FenceInt.lean` and `Dpss/SeparationInt.lean` into **38** Verus `spec fn`s
(24 + 7 + 7). Each generated file is marked `GENERATED … DO NOT EDIT` and cites
its Lean source line above each function. CI regenerates and fails on drift
(`scripts/lean_to_verus.py --check`). The translator is syntactic only, over a
deliberately small grammar, and **refuses** anything outside it with an error
naming the definition and the token — a translator that guessed would be worse
than none, because the Rust would then verify beautifully against the wrong
specification.

**What it does not cover.** Everything the translator refuses. That residue is
enumerated exhaustively in §4 and is the subject of L4.

### L3 — the Rust computes its specification, for all inputs

**Claim.** Every executable function returns exactly what its `spec fn` says,
and the step preserves both standing conditions.

**Evidence.** `rust/verify.sh` → **133 verified, 0 errors**. The apex obligations
are `step_ex` (above) and `run_ex` against `spec_run`. This is a proof over all
inputs satisfying the precondition, not a finite check.

**What it does not cover.** That the `spec fn`s are the Lean definitions — that
is L2 and L4. A verification can be internally flawless and about the wrong
system; this repository has one recorded instance of exactly that (`GUIDE.md`
§3), which is why the other links exist.

### L4 — the hand-written residue is tested against Lean

**Claim.** The definitions no generator produced agree with Lean wherever they
have been exercised, and they have been exercised broadly.

**Evidence, two tiers.**

*The traces* — `rust/traces.expected`, 11 blocks, **73 lines** compared. The
verified binary is diffed against the file (`rust/traces.sh`); Lean is diffed
against the same file (`scripts/check_traces.py`, running the compiled
`emit_traces`); the two meet on it. Ten of the blocks are hand-chosen worst cases,
including a negative control that must be rejected, and a standing-conditions
block whose ten configurations include six that violate a condition on purpose.

*The sweep* — `rust/sweep.expected`, **1816 configurations** drawn from 125,740
candidates across `(n,K) = (2,1) (2,2) (3,1) (3,2) (4,1)`, each run six steps and
reduced to a final state plus a rolling digest of every intermediate one. Same
two-sided arrangement (`scripts/check_sweep.py`).

Two properties of the sweep matter more than its size:

* **Both sides enumerate independently.** Lean does not hand the Rust a list of
  configurations. Each filters the candidate space with *its own* implementation
  of the standing conditions, so a disagreement about which configurations are
  **valid** changes the line count and is reported before any trajectory is
  compared. The filter is part of the test, not scaffolding around it.
* **The filter is what discharges `step_ex`'s precondition.** The sweep can only
  call the verified stepper legitimately because `inv` and `apart_on_boundaries`
  became executable first.

**Measured detection.** Four corruptions of hand-written definitions, each with
the executable half corrupted to match so that L3 still holds:

| corruption | traces | sweep | Verus |
|---|---|---|---|
| `adj_ordered`: `0 <= gap` → `-2 <= gap` | — | — | 7 errors |
| `adj_ordered`: range `0 <= i` → `1 <= i` | — | — | 6 errors |
| `min_deadline`: base `m <= 1` → `m <= 2` | caught | caught (1238) | caught |
| `min_deadline`: drone 3's deadline skipped | **invisible** | **caught (48)** | caught |

**What it does not cover.** Teams of five or more, resolutions past `K = 2`, runs
longer than six steps. Row 4 is why team size is named first: every recorded
trace has two or three drones, so anything needing a fourth could not appear in
one — a blind spot of the *dimension nobody varied*, which is the failure mode
hand-chosen suites have.

**And the honest reading of that table.** Verus caught all four. The sweep's
coverage is over the **traces**, not over the proofs. `INSIGHTS.md` §29–30 argue
why: `inv` is proved of the stepped configuration and assumed of the current one,
so a strengthening breaks the proofs and a weakening breaks the uses, leaving
little room to be wrong and still verify.

### L5 — the evidence is not vacuous

A count of verified functions is worth only as much as the specifications behind
it, and a proof is worth nothing if it is stubbed.

| check | result |
|---|---|
| `scripts/audit.py` — asks Lean which axioms each theorem depends on | 853 theorems, none depends on `sorryAx`; the only axioms are `propext`, `Classical.choice`, `Quot.sound` |
| `scripts/no_sorry.py` | no `sorry` in 43 files (comments stripped first) |
| `scripts/no_proof_holes.py` | no `assume(...)`, `admit()` or `#[verifier::external_body]` in 19 Rust files — the allow-list is empty |
| `scripts/lean_to_verus.py --check` | all three generated files current |
| negative controls | the contract-violation trace block, and six deliberately invalid rows in the standing-conditions block |

The unverified surface is confined and declared: **19** `#[verifier::external]`
functions, all in `rust/src/main.rs`, the trace and sweep harness. `external`
rather than `external_body` is the point — it gives those functions no
specification at all, so nothing verified can depend on them.

---

## 4. Why the links compose

The risk in a layered argument is not a weak layer; it is a **join** — a
definition that each layer assumes the other covers. This project has now been
bitten by exactly that twice (S7 and S7b, `CHANGELOG.md`), so the residue is
enumerated rather than described:

| hand-written definition | why the generator refuses it | covered by |
|---|---|---|
| `advance`, `spec_step`, `spec_run` | structure literals and recursion | L4 — traces (2 blocks) **and** sweep (1816 configs) |
| `time_to_next_event` / `min_deadline` | Lean uses `Finset.inf'` | L4 — same |
| `on_perimeter`, `adj_ordered`, `escorts_coherent`, `on_lattice` | quantify over `Fin n` with a dependent proof argument | L4 — standing-conditions block, 10 configs, 6 invalid; and as the sweep's filter |
| `apart_on_boundaries` | same | L4 — as the sweep's filter; its Lean counterpart `IntConfig.ApartOnBoundaries` is **derived**, via `embed_apartOnBoundaries`, not transcribed |
| `Dir` | a Rust `enum` | L4 — every block prints headings |

Two of these rows were added by S7 and S7b. Before S7, rows 1–2 were covered by
the traces only in appearance: `check_traces.py` sliced the team blocks off
before comparing. Before S7b, rows 3–4 were covered by **nothing** — the
generator refuses them and a `spec fn` never executes, so no trace could reach
them. Both gaps sat exactly at a join, and both looked closed from either side.

---

## 5. Residual risk, ranked

**D1 — the generator is in the trust base.** `lean_to_verus.py` is a Python
script whose output Verus then treats as the specification. A bug in it produces
a wrong specification that L3 will faithfully verify against. *Mitigations:* it is
syntactic-only over a small grammar; it refuses rather than guesses; its output
is human-readable and cites Lean line numbers; CI regenerates. *Not mitigated:* a
systematic error inside the grammar. This is the single largest item.

**D2 — the residue is covered by test, and tests are finite.** §4's rows are
assured to `n ≤ 4`, `K ≤ 2`, six steps. An error first manifesting at five drones
would not be caught. Row 4 of L4's table shows this is not hypothetical: the same
blind spot existed at four drones until S7c.

**D3 — the harnesses are unverified.** Both sides' harnesses are ordinary code.
A harness bug could mask a real difference. *Mitigation:* they are two
independently written programs in different languages, and a bug would have to
produce identical wrong output in both. This is why the enumeration is duplicated
rather than shared (L4).

**D4 — faithfulness to the paper is assumed, not proved.** A1. The repository
takes this seriously — `GUIDE.md` §3 records a wrong definition that supported a
flawless proof, and `STATUS.md` §3.11 records a bug that 145 passing theorems
missed and one concrete example caught — but it remains an assumption.

**D5 — this is not a controller.** The verified artefact holds the whole ensemble
and computes a global minimum over all drones. A flyable, decentralized
controller is a different artefact and the refinement theorem does not exist in
any form. `rust/REFINEMENT.md` states the three obligations and is candid that
the hard half is Lean, not Rust.

**D6 — toolchain soundness.** A4. Pinned, not verified.

**D7 — a mistranslation coherent across every Rust proof.** The failure mode a
self-consistent verification cannot detect from the inside. This is what L4
exists to catch and the only reason the tests matter where the proofs look
airtight.

**D8 — bounded arithmetic.** A3. Correctness is conditional on `fits`; outside
those bounds nothing is claimed.

---

## 6. What would raise confidence next, in order

1. **Sweep five drones.** Cheapest real gain, directly attacks D2, and four
   drones is where `Dpss/Counterexample.lean` says new phenomena start. The cost
   is the enumeration, which grows as `(2Kn+1)ⁿ · 2ⁿ`.
2. **Shrink D1** by having the generator emit a machine-checkable certificate, or
   by translating a definition twice through independent paths and diffing.
3. **Extend the generator's grammar** to cover `advance`/`step`/`run`, which
   would move §4's first row out of L4 entirely. `Finset.inf'` and the dependent
   quantifiers are the hard cases and may not be worth it.
4. **The controller refinement** (D5). Large, and mostly a Lean problem.

---

## 7. Reproducing the evidence

```sh
PATH=$HOME/.elan/bin:$PATH lake build     # the Lean development
python3 scripts/audit.py                  # 853 theorems, no sorryAx
python3 scripts/no_sorry.py               # 43 files clean
python3 scripts/lean_to_verus.py --check  # the generated spec is current
python3 scripts/no_proof_holes.py         # 19 Rust files, no holes
./rust/verify.sh                          # 133 verified, 0 errors
./rust/traces.sh                          # binary vs file, and file vs Lean,
                                          #   for 11 blocks and 1816 configs
```

`rust/traces.sh` runs the Lean side too when `lake` is on the `PATH`; in CI the
Lean job runs `scripts/check_traces.py` and `scripts/check_sweep.py` and the
Verus job runs the binary, and the two meet on the recorded files. That split is
deliberate: neither CI job needs both toolchains.

Expect the Lean sweep to take about **2m10s** and the Rust one about **22ms**.
That 1000× is why the recorded files exist at all.
