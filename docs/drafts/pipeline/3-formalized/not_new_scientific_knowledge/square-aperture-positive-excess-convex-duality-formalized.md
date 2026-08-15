# Square-aperture positive-excess convex duality — Lean formalization

- **ID:** `square-aperture-positive-excess-convex-duality`
- **Stage:** `3-formalized`
- **Type:** `THEOREM (Lean) / EXACT FINITE DUALITY`
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`

Paper proof:
`square-aperture-positive-excess-convex-duality.md`.

Formal module:

```text
GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSquarePositiveExcessDuality
```

Principal declarations:

- `two_mul_mul_sub_sq_le_posPart_sq`;
- `squarePrimeWindowCenteredDeviation_eq_neg_half_sharpSource`;
- `squarePrimeWindowPositiveExcessDualFunctional_eq_sharpSource`;
- `sum_apertureWeight_mul_dyadicWeightedPrimeWindow_square`;
- `squarePrimeWindowPositiveExcessDualFunctional_eq_primePairing`;
- `posPart_sq_sub_two_mul_mul_sub_sq_eq_dualDefect`;
- `two_mul_mul_sub_sq_lt_sq_of_ne`;
- `exists_pos_dualTerm_lt_sq_forall_finset`;
- `squarePrimeWindowPositiveExcessSquareEnergy_sub_dualFunctional_eq_defect`;
- `squarePrimeWindowPositiveExcessDualFunctional_le_energy`;
- `squarePrimeWindowPositiveExcessDualFunctional_optimal_eq_energy`;
- `squarePrimeWindowPositiveExcessSquareEnergy_le_iff_forall_dual_le`;
- `squarePrimeWindowPositiveExcessSquareEnergy_eq_summatory`;
- `four_mul_squarePrimeWindowPositiveExcessSquareEnergy_eq_sharpSourceNegativePart`;
- `SquarePrimeWindowPositiveExcessSquareEnergySubpower`, the exact open source predicate;
- `riemannHypothesis_of_squarePrimeWindowPositiveExcessSquareEnergySubpower`.

The finite duality, optimizer, and conditional consumer are unconditional Lean theorems. No theorem
asserts the open source estimate.

## Audit

- direct module Lean check: pass;
- umbrella import wired;
- targeted module build: pass;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped forbidden-declaration scan and `git diff --check`: pass.
