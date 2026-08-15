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

`research` is a ranked search, not a grep.  It is backed by a SQLite FTS5 index
at `formal/.lean_search.db` (git-ignored, derivable from the tree) holding every
declaration name, docstring, module and gap marker in
`GaloisForLFunctions/`.  A query costs about 130 ms; a full rebuild, which you
should never need, about 17 s.

### What keeps it current

Nothing watches the filesystem and no hook has to fire.  Every `research`
invocation re-syncs before it searches:

1. One `os.scandir` walk of `GaloisForLFunctions/` stamps every `.lean` and
   `.md` file with `(size, mtime_ns)` — 18.7k files in ~60 ms.
2. Those stamps are compared against the index's `file` table.  A file whose
   stamp differs, or that has no row, is **changed**; a row with no file on disk
   is **removed**.
3. With nothing changed — the normal case — the query runs immediately.  No
   write, no lock taken.
4. Otherwise the changed files are reparsed and rewritten in batches of 512, and
   removed files have their rows dropped.  Only the changed files are read.

So an agent that adds a module or edits a proof sees it in the very next search,
its own or another agent's.  Nothing needs regenerating by hand.

The index rebuilds itself automatically if the schema changes (it is fingerprinted,
not hand-versioned) or if the database file is damaged.

```bash
../scripts/formal_tools.py search-index            # refresh and report
../scripts/formal_tools.py search-index --rebuild  # discard and rebuild
../scripts/formal_tools.py research "<query>" --scan   # bypass the index
```

Ranking is BM25 over name, exploded identifier components, docstring and module,
so `research "measured clock inverse"` finds
`evalJet_measuredClockInverseOperator_difference` and a query that is itself an
identifier puts that declaration first.  Terms are OR-ed and prefix-matched;
quote a phrase (`research '"critical line" zero'`) to require it verbatim.

Use `rg` instead when the target is proof-body text rather than a declaration —
raw regex over the whole tree is fast and the index only covers declaration
metadata and gap markers.

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
