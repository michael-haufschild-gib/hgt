# Formal Lean Agent Instructions

## What This Is

This folder is the Lean 4 proof project.  Every research module belongs to one
of six theorem areas:

| Area | Umbrella | Capstone surface |
|---|---|---|
| RH / Xi / L-function criteria | `GaloisForLFunctions.RHTower` | RH characterizations and their source/constraint bridges |
| General hypertranscendental geometry | `GaloisForLFunctions.HTGeometry` | Reusable differential, constraint, value-relation, moment, and operator geometry |
| Hurwitz | `GaloisForLFunctions.Hurwitz` | `hurwitz_n2_unconditional` |
| u0_pui | `GaloisForLFunctions.U0` | `U0CardTheorems.u0_phi_independence_all_parameters` |
| q62 Böttcher | `GaloisForLFunctions.Bottcher` | `Bottcher.q62_independence`, `Bottcher.q62_mixed`, `Bottcher.q62_phiMero_norm_gap`, `Bottcher.q62_phiMero_linGap`, `Bottcher.q62_phiMero_linGap_roots`, `Bottcher.q62_phiMero_norm_gap_roots`, `Bottcher.q62_phiMero_mixed_far_roots`, `Bottcher.q62_phiMero_mixed_far_roots_swapped`, `Bottcher.noRelation_phiMero_of_ne` (all nonexceptional parameters, unconditional) |
| Hilbert metrics | `GaloisForLFunctions.HilbertMetric` | finite graded Pluecker partitions and Gaussian feature-determinant laws |

`GaloisForLFunctions.MainTheorems` imports all six, plus three vendored areas
(all Apache-2.0, all read-only — re-sync from upstream instead of editing, and
read the area's `PROVENANCE.md` before touching it):

| Vendored area | Upstream | Contents |
|---|---|---|
| `GaloisForLFunctions.QuantumAlg` | Lean-QuantumAlg | quantum algorithms; uses the Lean module system (`module`, `public import`), ours do not |
| `GaloisForLFunctions.PNTPlus` | PrimeNumberTheoremAnd | prime number theorem with error term, Wiener–Ikehara, Perron/Mellin calculus, Selberg sieve, Brun–Titchmarsh |
| `GaloisForLFunctions.QECLean` | QECLean | quantum error correction: Pauli/symplectic layer, stabilizer framework, toric/surface/Steane/bivariate-bicycle codes |

`PNTPlus` proves the PNT independently of `RHTower/Sieve/ChebyshevPNT.lean`;
both are kept (see `PNTPlus/PROVENANCE.md` for the overlap map).  Parts of
`QECLean` rest on `native_decide` and so depend on `Lean.ofReduceBool` — check
`#print axioms` before citing one of its distance certificates.

## Follow The Whole Prompt, Every Turn

Read the user's prompt in full and follow every rule in it exactly, including the ones that look
like boilerplate.  The rules hold for the entire session, not the first few minutes: re-read this
file at the start of every turn, and before each tool call name the rule that governs it and
confirm the call matches.  Convenience, an earlier plan, and default habits never override a rule.

## Start Here

1. Read `README.md`.
2. Read `LEAN_OVERVIEW.md` for the current map.
3. Search before proving -- the search tool comes before Mathlib and before `rg`/`grep`:
   `../scripts/formal_tools.py research "<query>"`
   Run it directly; do not run `--help` or read the search code first. It searches keywords and
   meaning together over this project's Lean and Markdown and the formalized pipeline cards;
   edits are indexed automatically.
   - A name or part of one: `research inverseClockK`; `--mode lexical` for a sub-second lookup.
   - A result or a proof technique: describe it in words, then read `Candidate lemmas` first.
   - Mathlib, only after our corpus: `--scope mathlib`, keyword-only -- query Lean names and terms.
   - "Local Qdrant unavailable": run `../launch.sh` and retry.
   Details: "How Search Works Here" in `README.md`.
4. Only after the search tool has named the declarations and modules, use `rg` for exact
   source-text confirmation (a literal name's spelling, a tactic string, an import line):
   `rg "<name-or-concept>" GaloisForLFunctions`
   Never research the corpus with `rg`/`grep` instead of the search tool.

## Build And Check

**NEVER run `lake build`** -- not for a module, an umbrella, a single file or a dependency.  It
recompiles thousands of modules and blocks the whole machine.  Every compile is one of the two
commands below, run from `formal/`.  `--old` is a *lake* flag and goes before `env` (`lean`
rejects it); it makes lake reuse every existing olean instead of rebuilding it.

Check a file (writes no olean; this is also the final audit):

```bash
lake --old env lean GaloisForLFunctions/<Path>/<Module>.lean
```

Build the olean of one module (your own file when another file you write imports it, or a
dependency whose olean is missing):

```bash
lake --old env lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/<Path>/<Module>.olean \
  -i .lake/build/lib/lean/GaloisForLFunctions/<Path>/<Module>.ilean \
  GaloisForLFunctions/<Path>/<Module>.lean
```

Rules that are not negotiable:

- Foreground only -- never backgrounded.
- One build process per agent/chat session at a time.
- Build only the olean of your own file, and only when another file needs it.
- A missing `.olean` (`object file '.../GaloisForLFunctions/X/Y/Z.olean' ... does not exist`):
  build exactly that one module's olean with the second command, then retry the original file.
  If the retry names another missing olean, build that one, and so on -- one by one.  Build
  nothing else, and never rebuild an olean that already exists.
- No full builds, no umbrella builds, no large aggregate targets.  Wire a finished module into
  its area umbrella with an import line, but do not build the umbrella to check it.

Linting is separate and cheap:

```bash
../scripts/formal_tools.py lint --check-generated
```

## Keep It Organized

- Put RH-, Xi-, critical-line-, Weil-, Li-, or L-function-specific research in
  `GaloisForLFunctions/RHTower/`.
- Put reusable hypertranscendence, differential algebra, constraint geometry,
  value-relation, analytic, moment, and operator infrastructure in
  `GaloisForLFunctions/HTGeometry/`.
- Put theorem-program-specific work for the three toy problems only in
  `GaloisForLFunctions/U0/`, `GaloisForLFunctions/Bottcher/`, or
  `GaloisForLFunctions/Hurwitz/`.
- Do not add research leaf modules directly under `GaloisForLFunctions/`.
  That level is reserved for `Core.lean`, the six area umbrellas,
  `MainTheorems.lean`, and the two cross-area aggregators
  `FullyProvenNewTargets.lean` and `KummerRootApplications.lean`.
- **Every result must be unconditional: no added hypotheses or premises.** No `sorry`, `admit`,
  `axiom`, `opaque`, `unsafe` or `native_decide`; no assumption binder added to make a proof go
  through; no `Prop`-valued interface standing in for an analytic input the proof needs. Only the
  genuine typing side-conditions of the objects involved belong in a statement.
- **Comments are mathematics, not diary.** No references to research docs, task numbers,
  sessions, dates, or process notes ("pre-certified", "banked", "round N") — in two days
  nobody can decode them. A Lean project is self-contained: it stands for itself as a
  proof. A docstring states what the declaration says mathematically and, briefly, the
  proof mechanism — nothing else.
- A missing analytic input is not a hypothesis to add: it means the theorem is not ready. Prove
  it, weaken the conclusion until the statement is unconditional, or record the gap on the
  pipeline card.
- Verify mathlib names in `/tmp` scratch files before using them.
- Prefer the narrowest import that contains the needed declarations.
- Keep Lean implementation files below 1500 lines where practical; split by proof phase.
- **Optimize proofs; never raise a budget to make one compile.** No `set_option maxHeartbeats`
  (raised or `0`), `maxRecDepth`, or `synthInstance.maxHeartbeats`/`maxSize` bumps. A timeout is a
  badly written proof: give `nlinarith` exactly the products it needs, prefer `simp only [...]`
  over bare `simp`, split a long proof into cheap named lemmas, and prove a rewrite lemma once
  rather than unfolding a definition repeatedly.
- Regenerate indexes after moving, adding, or renaming declarations:
  `../scripts/formal_tools.py index`.
- Update umbrella imports when adding modules.
- Keep `CLAUDE.md` and `AGENTS.md` in this folder in sync.
