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
| q62 Böttcher | `GaloisForLFunctions.Bottcher` | `Bottcher.q62_independence`, `Bottcher.q62_mixed`, `Bottcher.q62_phiMero_norm_gap`, `Bottcher.q62_phiMero_linGap`, `Bottcher.q62_phiMero_linGap_roots`, `Bottcher.q62_phiMero_norm_gap_roots`, `Bottcher.q62_phiMero_mixed_far_roots`, `Bottcher.q62_phiMero_mixed_far_roots_swapped` |
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
lake build +GaloisForLFunctions.<Area>
../scripts/formal_tools.py lint --check-generated
```

Full local gate:

```bash
../scripts/formal_tools.py lint --check-generated --build --build-target GaloisForLFunctions.MainTheorems
```

This gate fails on Lean build warnings.

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
- No active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.
- **Comments are mathematics, not diary.** No references to research docs, task numbers,
  sessions, dates, or process notes ("pre-certified", "banked", "round N") — in two days
  nobody can decode them. A Lean project is self-contained: it stands for itself as a
  proof. A docstring states what the declaration says mathematically and, briefly, the
  proof mechanism — nothing else.
- Represent missing analytic inputs as explicit hypotheses or `Prop` interfaces.
- Verify mathlib names in `/tmp` scratch files before using them.
- Prefer the narrowest import that contains the needed declarations.
- Keep Lean implementation files below 1500 lines where practical; split by proof phase.
- Regenerate indexes after moving, adding, or renaming declarations:
  `../scripts/formal_tools.py index`.
- Update umbrella imports when adding modules.
- Keep `CLAUDE.md` and `AGENTS.md` in this folder in sync.
