# Formal Project Guide

This Lean project has six owned theorem areas:

| Area | Umbrella import | Current capstone surface |
|---|---|---|
| RH / Xi / L-function criteria | `GaloisForLFunctions.RHTower` | RH characterizations and their source, reflection, positivity, and value-relation bridges |
| General hypertranscendental geometry | `GaloisForLFunctions.HTGeometry` | Differential/constraint geometry and reusable analytic, moment, value-relation, and operator infrastructure |
| Hurwitz | `GaloisForLFunctions.Hurwitz` | `hurwitz_n2_unconditional` |
| u0_pui | `GaloisForLFunctions.U0` | `U0PhiIndep.u0_phi_independence`, `U0CardTheorems.u0_phi_independence_all_parameters` |
| q62 Böttcher | `GaloisForLFunctions.Bottcher` | `Bottcher.q62_independence`, `Bottcher.q62_mixed`, `Bottcher.q62_phiMero_norm_gap`, `Bottcher.q62_phiMero_linGap`, `Bottcher.q62_phiMero_linGap_roots`, `Bottcher.q62_phiMero_norm_gap_roots`, `Bottcher.q62_phiMero_mixed_far_roots`, `Bottcher.q62_phiMero_mixed_far_roots_swapped` |
| Hilbert metrics | `GaloisForLFunctions.HilbertMetric` | finite graded Pluecker partitions, Gaussian centroid gauge, corrected-determinant scale laws, self-commutator Fano defects, and quadratic graph-completion laws |

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
