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

From this directory, start the local search services with `../launch.sh`.
Use `../launch.sh --restart` to restart or `../launch.sh --stop` to stop them.
Docker Desktop starts automatically when needed. The launcher runs Qdrant,
the shared local inference worker, background indexing and unfinished local
GPU-result receivers. Remote Runpod jobs continue independently.

Default hybrid search combines lexical matches with Qdrant vector retrieval
across declaration names, docstrings, statements, proofs and the Markdown in
`formal/` and the formalized pipeline cards in
`docs/drafts/pipeline/3-formalized`, then reranks. The rest of `docs/` and
hidden directories are not indexed.
Scope defaults to this project; `--scope mathlib` or `--scope all` reaches the
installed dependencies, which are lexically indexed but carry no vectors.
`--mode lexical` uses lexical search alone. The default request budget is
300 seconds; change it with `--budget-seconds`.

Output sections: `Declarations` (keyword hits in this project), `Candidate
lemmas` (meaning and keyword, reranked; Mathlib hits appear only here),
`Source arguments` (proofs whose method matches), `Markdown notes` and
`Source passages` (whole-file Lean chunks). `--json` names them
`declarations`, `candidate_lemmas`, `source_arguments`, `prose` and
`source_passages`.

### What keeps it current

While services run, the indexer scans for added, edited and deleted sources
every 2 seconds; an edit is searchable by meaning within about 10 seconds.
Changed content is reparsed and queued for embedding; Qdrant updates resume
after interruptions. Searches are served first and never cancel queued
indexing, so both make progress while agents work. Work is prioritized RHTower, then
HTGeometry, then the remaining corpus. New content can be found lexically
before its embeddings are ready. A lagging index or partial search is reported
as a warning in the results. No Lean builds run in the background.

`--no-refresh` searches cached content. Ordinary searches also refresh the
lexical index when needed. No manual reindex is needed for normal edits.

```bash
../scripts/formal_tools.py research "<query>"
../scripts/formal_tools.py research "<query>" --scope all --budget-seconds 300
../scripts/formal_tools.py research "<query>" --mode lexical
../scripts/formal_tools.py search-index --corpus   # explicitly refresh source content
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

The `Declarations` list comes from this metadata index of names, docstrings
and modules; statements, proof bodies and Mathlib are searched by the sections
below it. Use `rg` only to confirm exact text the search surfaced. Extraction is source-based, not
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
