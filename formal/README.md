# Formal Project Guide

This Lean project has six owned theorem areas:

| Area | Umbrella import | Current capstone surface |
|---|---|---|
| RH / Xi / L-function criteria | `GaloisForLFunctions.RHTower` | RH characterizations and their source, reflection, positivity, value-relation, and Real-corona cyclic bridges |
| General hypertranscendental geometry | `GaloisForLFunctions.HTGeometry` | Differential/constraint geometry and reusable analytic, moment, value-relation, and operator infrastructure |
| Hurwitz | `GaloisForLFunctions.Hurwitz` | `hurwitz_n2_unconditional` |
| u0_pui | `GaloisForLFunctions.U0` | `U0PhiIndep.u0_phi_independence`, `U0CardTheorems.u0_phi_independence_all_parameters` |
| q62 Böttcher | `GaloisForLFunctions.Bottcher` | `Bottcher.q62_independence`, `Bottcher.q62_mixed`, `Bottcher.q62_phiMero_norm_gap`, `Bottcher.q62_phiMero_linGap`, `Bottcher.q62_phiMero_linGap_roots`, `Bottcher.q62_phiMero_norm_gap_roots`, `Bottcher.q62_phiMero_mixed_far_roots`, `Bottcher.q62_phiMero_mixed_far_roots_swapped` |
| Hilbert metrics | `GaloisForLFunctions.HilbertMetric` | finite graded Pluecker partitions, Gaussian centroid gauge, corrected-determinant scale laws, self-commutator Fano defects, and transverse-degree graph laws with exact symmetric-power charge, positive limiting log curvature, order-ten coherent-collision jets, matrix-curvature persistence, and determinant 2-jet differentiation |

`GaloisForLFunctions.MainTheorems` imports all six areas.  The root module
`GaloisForLFunctions` imports only `MainTheorems`, so the default Lake build
follows the same ownership map without a second hand-maintained module list.

## Module Ownership

Research leaf modules never live directly under `GaloisForLFunctions/`:

- RH-, Xi-, critical-line-, Weil-, Li-, or L-function-specific research belongs
  in `RHTower/`.
- Reusable hypertranscendence, differential algebra, constraint geometry,
  value-relation, analytic, moment, and operator work belongs in `HTGeometry/`.
- Work specific to the three toy theorem programs belongs in `U0/`,
  `Bottcher/`, or `Hurwitz/`.
- Source-independent Hilbert-space, finite-metric, Gaussian-kernel, and feature-volume
  laws belong in `HilbertMetric/`; they must not depend on `HTGeometry` or `RHTower`.

The package root is reserved for `Core.lean`, the six area umbrellas,
`MainTheorems.lean`, `FullyProvenNewTargets.lean`, and
`KummerRootApplications.lean`.  Every area umbrella imports its complete area
inventory, so building or scanning an umbrella does not silently omit leaf
modules.

Local agent entrypoints:

| File | Purpose |
|---|---|
| `CLAUDE.md` | Short Claude-oriented formal workflow instructions. |
| `AGENTS.md` | Same instructions for non-Claude agents. |

For a quick local overview, run:

```bash
../scripts/formal_tools.py status
```

## Böttcher q62 Agent Scan Path

Use `GaloisForLFunctions.Bottcher` as the umbrella import for q62.  It imports
`GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance`, so the
current connected-case countable-avoidance infrastructure is registered through
the theorem-area umbrella and appears in the generated API.

When working on the current connected `hRigid`/countable-avoidance lane, start
with these generated-index queries:

```bash
../scripts/formal_tools.py research "exists_not_countable_local_commonComponentFrontierSlice"
../scripts/formal_tools.py research "LocalTipEveryRadiusComponentSaturation"
../scripts/formal_tools.py research "BaseLocalTipLocalLoopOrderCode"
../scripts/formal_tools.py research "PreconnectedNotCountable"
```

The active implementation file is large by design:
`GaloisForLFunctions/Bottcher/RelativeRigidityCountableAvoidance.lean`.
For cheap iteration, run only:

```bash
lake env lean GaloisForLFunctions/Bottcher/RelativeRigidityCountableAvoidance.lean
```

Regenerate `LEAN_API.md`, `LEAN_GAPS.md`, and `LEAN_OVERVIEW.md` after adding
or renaming q62-facing declarations; otherwise agents will miss the newest
bridges.

## Required Local Workflow

Before proving a new lemma:

1. Search the generated API:
   `../scripts/formal_tools.py research "<keyword>"`
2. Search the source when exact syntax matters:
   `rg "<name-or-concept>" GaloisForLFunctions`
3. Check the area status file when one exists:
   `GaloisForLFunctions/Bottcher/STATUS.md` or
   `GaloisForLFunctions/Hurwitz/STATUS.md`
4. Prefer the narrowest import that contains the needed declarations.

Before claiming a Lean change is clean:

1. Run the target module:
   `lake env lean GaloisForLFunctions/<path>.lean`
2. Run the theorem-area build:
   `lake build +GaloisForLFunctions.<Area>`
3. Run the project lint:
   `../scripts/formal_tools.py lint --check-generated`

The full lint gate treats Lake build warnings as failures:
`../scripts/formal_tools.py lint --check-generated --build --build-target GaloisForLFunctions.MainTheorems`.

Regenerate agent-facing indexes after adding, moving, or renaming declarations:

```bash
../scripts/formal_tools.py index
```

## How Search Works Here

`research` searches extracted declaration names, full adjacent docstrings,
module names, and gap markers in `GaloisForLFunctions/`. The SQLite FTS5 cache
is `formal/.lean_search-<fingerprint>.db` (git-ignored and derivable).
Schema/extractor upgrades get separate database generations, so an agent
using the previous version retains its own database and WAL files.

### What keeps it current

Nothing watches the filesystem and no hook has to fire.  Every `research`
invocation re-syncs before it searches:

1. One `os.scandir` walk of `GaloisForLFunctions/` stamps every `.lean` and
   `.md` file with `(size, mtime_ns)`.
2. Those stamps are compared against the index's `file` table.  A file whose
   stamp differs, or that has no row, is **changed**; a row with no file on disk
   is **removed**.
3. With nothing changed — the normal case — the query runs immediately.  No
   write, no lock taken.
4. Otherwise the changed files are reparsed and rewritten in batches of 512, and
   removed files have their rows dropped.  Only the changed files are read.

So an agent that adds a module or edits a proof sees it in the very next search,
its own or another agent's.  Nothing needs regenerating by hand.

The first query builds a missing generation. For a shared-tool upgrade, prepare
the new generation before switching the entrypoint. A damaged cache is rebuilt;
lock contention never causes deletion of a live database. `--no-refresh` uses
cached contents and reports an error if that generation is empty.

```bash
../scripts/formal_tools.py search-index            # refresh and report
../scripts/formal_tools.py search-index --rebuild  # discard and rebuild
../scripts/formal_tools.py research "<query>" --scan   # bypass the index
```

Spaces mean **AND**: every term or phrase must match. Shell quotes group an
argument; inner double quotes require contiguous words in one indexed field.
`--any` switches to OR, useful for alternatives or broader follow-up searches.
Prefixes expand automatically; `--exact` restricts matches to complete tokens.
Boolean query syntax is rejected with guidance instead of being searched as text.

```bash
../scripts/formal_tools.py research "spectral gap coercivity"
../scripts/formal_tools.py research '"critical line" zero'
../scripts/formal_tools.py research "coercivity positivity" --any
../scripts/formal_tools.py research "carry" --module IntegerCarryTransport --per-module 0
../scripts/formal_tools.py research "prolate ladder" --offset 20 --explore 0
```

BM25 weights declaration names and split identifier words above docstrings and
split module names; exact identifiers receive a boost. Two declarations per
module are shown by default. The cap is applied across all matches before
paging; `--per-module 0` disables it. Results report raw match counts, module
counts, and how many remain after the cap. `--json` includes those counts,
the effective MATCH expression, filters, and separate result lists.

Five appended exploration hits use the **same query and filters**, exclude
modules on the main page, and favor less represented filename families across
all matching modules. Family means directory plus the first two CamelCase
filename words: a heuristic for discovery, not a mathematical classification
or a measure of novelty. `--explore 0` disables it; `--exclude-module` removes
a literal module substring and can be repeated. Results are deterministic.

Use `rg` for theorem statements, types, proof bodies, mathlib, and pipeline
cards: they are outside this metadata index. Extraction is source-based, not
Lean elaboration, and cannot detect mathematical equivalence. The scan fallback
uses the same extraction and AND/OR/phrase/filter rules, with approximate token
ranking. Gap markers are text mentions, not verified open obligations.

Many agents share one index, and the design assumes it.  Readers never block.
Writers take the lock only for a batch at a time, and re-check each file's stamp
inside the lock, so when several agents notice the same new module at once only
the first one parses it.  A refresh that loses the lock leaves the query running
against the last committed state and says so on stderr rather than blocking.

This writes:

| File | Purpose |
|---|---|
| `LEAN_OVERVIEW.md` | Generated quick map of theorem areas, wiring, commands, and largest Lean files. |
| `LEAN_API.md` | Generated declaration catalog with module, location, kind, and docstring summary. |
| `LEAN_GAPS.md` | Generated proof-debt, large-file, and gap-marker report. |

## Proof-Debt Policy

The formal tree should have no active `sorry`, `admit`, `axiom`, `opaque`, or
`unsafe` declaration unless the project explicitly chooses to allow one.  The
current local lint gate treats all such findings as errors.

When a hard analytic input is not yet proven, expose it as an explicit
hypothesis or `Prop` interface.  Do not hide it behind a placeholder proof.

## File-Size Policy

The lint tool warns above 1500 lines.  A warning is not a failed build, but a
file above that threshold should have one of these dispositions:

| Disposition | Use when |
|---|---|
| Split now | The file contains independent phases or reusable sub-APIs. |
| Keep temporarily | A contiguous proof is actively moving and splitting would create merge churn. |
| Add an index | The file is intentionally large but has stable internal sections. |

`Bottcher/Brolin.lean` is now a public aggregator.  Its proof chapters live in
`Bottcher/Brolin/`, with each Lean implementation file below the lint warning
threshold.  Keep that structure when extending the Brolin/Riesz stack: add a
new chapter module instead of rebuilding a monolith.
