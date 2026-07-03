# Formal Lean Agent Instructions

## What This Is

This folder is the Lean 4 proof project.  The three main proof programs are:

| Area | Umbrella | Capstone surface |
|---|---|---|
| Hurwitz | `GaloisForLFunctions.Hurwitz` | `hurwitz_n2_unconditional` |
| u0_pui | `GaloisForLFunctions.U0` | `U0CardTheorems.u0_phi_independence_all_parameters` |
| q62 Böttcher | `GaloisForLFunctions.Bottcher` | `Bottcher.q62_independence`, `Bottcher.q62_mixed`, `Bottcher.q62_phiMero_norm_gap`, `Bottcher.q62_phiMero_linGap` |

`GaloisForLFunctions.MainTheorems` imports all three.

## Start Here

1. Read `README.md`.
2. Read `LEAN_OVERVIEW.md` for the current map.
3. Search before proving:
   `../scripts/formal_tools.py research "<query>"`
4. Use `rg` for exact syntax:
   `rg "<name-or-concept>" GaloisForLFunctions`

## Build And Check

Run from `formal/` unless noted:

```bash
lake env lean GaloisForLFunctions/<path>.lean
lake build GaloisForLFunctions.<Area>
../scripts/formal_tools.py lint --check-generated
```

Full local gate:

```bash
../scripts/formal_tools.py lint --check-generated --build --build-target GaloisForLFunctions.MainTheorems
```

This gate fails on Lean build warnings.

## Keep It Organized

- No active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.
- Represent missing analytic inputs as explicit hypotheses or `Prop` interfaces.
- Verify mathlib names in `/tmp` scratch files before using them.
- Prefer the narrowest import that contains the needed declarations.
- Keep Lean implementation files below 1500 lines where practical; split by proof phase.
- Regenerate indexes after moving, adding, or renaming declarations:
  `../scripts/formal_tools.py index`.
- Update umbrella imports when adding modules.
- Keep `CLAUDE.md` and `AGENTS.md` in this folder in sync.
