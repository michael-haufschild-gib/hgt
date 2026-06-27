# Formal Project Guide

This Lean project has three theorem areas:

| Area | Umbrella import | Current capstone surface |
|---|---|---|
| Hurwitz | `GaloisForLFunctions.Hurwitz` | `hurwitz_n2_unconditional` |
| u0_pui | `GaloisForLFunctions.U0` | `U0PhiIndep.u0_phi_independence`, `U0CardTheorems.u0_phi_independence_all_parameters` |
| q62 Böttcher | `GaloisForLFunctions.Bottcher` | `Bottcher.q62_independence`, `Bottcher.q62_mixed` |

`GaloisForLFunctions.MainTheorems` imports all three areas.  The root module
`GaloisForLFunctions` imports `MainTheorems`, so the default Lake build covers
the shared infrastructure and the three proof programs.

Local agent entrypoints:

| File | Purpose |
|---|---|
| `CLAUDE.md` | Short Claude-oriented formal workflow instructions. |
| `AGENTS.md` | Same instructions for non-Claude agents. |

For a quick local overview, run:

```bash
../scripts/formal_tools.py status
```

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
   `lake build GaloisForLFunctions.<Area>`
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
