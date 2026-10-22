# Formalization certificate — `ccm-rectangular-subpower-lower-floor-rh-law`

- **Card:** `ccm-rectangular-subpower-lower-floor-rh-law.md`
- **Stage:** 3-formalized / not-new
- **Lean modules:**
  - `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularSubpowerLowerGate.lean`
  - `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularPowerLowerZeroFree.lean`
  - `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularObservablePowerLowerZeroFree.lean`
- **Umbrella:** all three imported from `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 18 audited declarations
- **Hypotheses:** none beyond the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `(8)`–`(9)` bounded remainder absorbed into a power floor | `CCMRectangularObservablePowerLowerZeroFree` |
| `(10)`–`(11)` power-shifted nonnegative Landau coefficient and its continuation | `LSeries_xiRectangularPowerLandauCoefficient_eq_continuation`, `differentiableOn_xiRectangularPowerLandauContinuation_landauBall` |
| `(12)` translated shifted-zeta pole locations, Landau transfer | `exists_xiRectangularPowerLandauCoefficient_summable_left_of_boundary` |
| `(3)`/`(13)` fixed-exponent horizontal zero-free conclusion | `xiRightTransverseSup_le_of_xiRectangularRightPowerLower`, `xiRightCenteredZero_re_le_of_xiRectangularRightPowerLower` |
| `(4)`–`(6)` subpower/polylogarithmic floors suffice for RH | `riemannHypothesis_of_xiRectangularRightSubpowerLower`, `riemannHypothesis_of_xiRectangularWeilTailSubpowerLower` |

The card's remaining open gates (derive one source-defined subpower lower floor; RH) are route
gates, not statements of this card.
