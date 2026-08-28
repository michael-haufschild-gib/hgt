# Lean formalization: polarized exactness horizon and relative Connes phase

- **Source card:** `polarized-exactness-horizon-and-relative-connes-phase-law.md`
- **Formalization date:** 2026-08-28
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NOT RH]`

## Modules

| Module | Formalized content |
|---|---|
| `GaloisForLFunctions.HTGeometry.PolarizedExactnessHorizonRelativeConnesPhaseLaw` | Oriented/doubled horizon, phase fibres, finite matrix factorizations, relative Connes class |
| `GaloisForLFunctions.HTGeometry.ParachainConnesComparisonLaw` | Connes null-homotopy and inverse-monodromy totalization law |
| `GaloisForLFunctions.RHTower.PolarizedExactnessHorizonSourceSpecialization` | Literal Xi source coefficient, residue, zero criterion, positive Stokes energy |

Modules are reachable from corresponding HTGeometry and RHTower umbrellas.

## Paper-to-Lean map

- Theorem 2.1:
  `dualNumberSign_eps`, `dualNumber_eps_ne_zero`, `dualNumber_conormal_fixed_eq_zero`,
  `dualNumber_not_regularLocalRing`, `dualNumber_not_regularRing`,
  `finite_free_X_factorization_smith_classification`,
  `finite_free_X_factorization_contractible`,
  `squareUniformizerFactorization_noncontractible`.
- Corollary 2.2:
  `powerSeriesPhaseEquiv_X`, `powerSeriesPhaseEquiv_X_pow`,
  `phase_fixed_vector_eq_zero`.
- Theorem 3.1:
  `positiveRankOne_phase`, `positiveRankOne_eq_iff_phase`,
  `positiveRankOneDifferential_eq_zero_iff`,
  `exists_executedPhaseLength_pos_of_nonconstant`.
- Theorem 4.1:
  `connesComparison_nullhomotopy`.
- Theorem 4.2:
  `relativeConnesClass`, `connectingClass_eq_neg_sourceDefectClass`,
  `sourceDefectClass_eq_zero_of_relativeConnesClass_eq_zero`.
- Corollary 5.1:
  `polarizedXiSourceCoefficient_ne_zero`,
  `polarizedXiPrimeSourceResidue_eq_sub_one_mul`,
  `polarizedXiPrimeSourceResidue_eq_zero_iff`,
  `polarizedXiPositiveStokesEnergy_eq_square_div`, together with preceding generic horizon and
  relative-Connes theorems.

## Verification

- Direct `lake env lean` elaboration passed for all three leaf files.
- Targeted `lake build` passed for all three modules; no umbrella build was run.
- Declarations pre-existed this promotion, so no redundant axiom audit was repeated.

This formalization proves card's unconditional structural restrictions. It does not assert
vanishing of literal source residue or RH-bearing global source-lift theorem.
