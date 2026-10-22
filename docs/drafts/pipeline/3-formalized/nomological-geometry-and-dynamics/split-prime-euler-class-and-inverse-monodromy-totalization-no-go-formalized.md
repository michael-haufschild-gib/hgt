# Lean formalization: split-prime Euler class and inverse-monodromy totalization no-go

- **Source card:** `split-prime-euler-class-and-inverse-monodromy-totalization-no-go.md`
- **Formalization date:** 2026-08-28
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NOT RH]`

## Modules

| Module | Formalized content |
|---|---|
| `GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCofiniteDivisorSplitting` | Fixed-prime direct summand, section defect, Euler factor/cocycle/class vanishing, coefficient pushforward |
| `GaloisForLFunctions.HTGeometry.ParachainConnesComparisonLaw` | Inverse-monodromy mate cancellation without trivial monodromy |
| `GaloisForLFunctions.HTGeometry.BoundedLogarithmicPrimeInfinityShear` | Abstract, real `Lᵖ`, and real `c₀` bounded-shear splitting |
| `GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CoframeAnomalyRank` | Normalized valuation coframes and preserved independence |
| `GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CoframeExtensionNonerasure` | Homology nonerasure, connecting-range obstruction, split connecting-map vanishing, hostile flat/split counterexample |

All modules are reachable from corresponding project umbrellas.

## Paper-to-Lean map

- Theorem 1.1 and Corollary 1.2:
  `deningerFixedPrimeSplitting`, `fixedPrimeKernelEquivInt`,
  `fixedPrimeSectionDefect_eq_zero`, `fixedPrimeEulerFactor_eq_zero`,
  `fixedPrimeEulerCocycle_eq_zero`, `fixedPrimeEulerClass_eq_zero`,
  `fixedPrimeEulerClass_pushforward_eq_zero`.
- Theorem 2.1:
  `scalarMonodromy_comp_inverse`, `scalarMonodromy_factors_nontrivial`.
- Counterexample 3.1:
  `flatSplitPrimeConnection_flat`, `flatSplitPrimeBoundary_surjective`,
  `flatSplitPrimeBasis_mem_boundary`, `flatSplitPrimeCombination_mem_boundary`.
- Theorem 3.2 and Corollary 3.2a:
  `coframeExtension_nonerasure`, `coframeExtension_quotient_linearIndependent`,
  `connectingRange_inf_finitePrimeSpan_eq_bot`, `connectingMap_eq_zero_of_retraction`.
- Theorem 3.3:
  bounded logarithmic shear split declarations in
  `BoundedLogarithmicPrimeInfinityShear`.

## Verification

- Direct `lake env lean` elaboration passed for the new leaf.
- Targeted `lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CoframeExtensionNonerasure`
  passed; no umbrella build was run.
- One axiom audit covered all new theorem declarations. Dependencies are limited to
  `propext`, `Classical.choice`, and `Quot.sound`.
- Pre-existing declarations were not redundantly axiom-checked.

The HGT local-to-global duality cone, literal Kummer/Bockstein comparison, and any Xi/RH-bearing
source realization remain explicit design targets outside this formalization claim.
