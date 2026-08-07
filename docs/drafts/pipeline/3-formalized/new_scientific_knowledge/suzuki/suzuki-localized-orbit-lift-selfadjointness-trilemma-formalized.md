# Localized Suzuki orbit lifts cannot be bounded, covariant, and self-adjoint — Lean certificate

- **ID:** `suzuki-localized-orbit-lift-selfadjointness-trilemma-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-localized-orbit-lift-selfadjointness-trilemma.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/SuzukiLocalizedOrbitLiftTrilemma.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.SuzukiLocalizedOrbitLiftTrilemma`:

```text
GaloisForLFunctions.RHTower.projectivelyTranslationCovariant_summable_normSq_eq_zero
GaloisForLFunctions.RHTower.suzukiProjectivelyCovariantSummableWeight_eq_zero
GaloisForLFunctions.RHTower.translationInvariantNorm_summable_normSq_eq_zero
GaloisForLFunctions.RHTower.translationInvariant_summable_normSq_eq_zero
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 4 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- construct the source-dependent relation `(20)`
- prove its cutoff graph is closed
- prove trace-zero weighted Gamma-domain entry
- prove completed Evans injectivity
- RH

These are research frontier items, not formalization debt.
