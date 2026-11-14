# Certified window floors and overlap calculus

- **ID:** A162
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1311/obstacles-summary.md`, A162.
- **Statement:** The certified spectral and conditional floors, neutral-orthogonal
  and Green overlap criteria, additive loss law, and uniform binding bound hold.

All modules below belong to `GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow`.

| Result | Lean declaration | Module |
|---|---|---|
| For `R≥1`, `Q≥2`, `1≤J`, `50J≤53R`, the positive ground vector has orthogonal floor `1/5000` | `exists_groundVector_with_floor_of_short` | `ChargeCancellationPreservesTheCertifiedFloor` |
| Every other eigenvalue is at least `1/5000` | `eigenvalue_ge_of_ne_ground_of_short` | same |
| Left conditional floor `1/5000` when `100a≤3R` | `overlapLeftEnergy_floor` | `TheCertifiedFloorsAreAPrioriBoundsForTheGreenMatrixAndTheConditionalEnergies` |
| Right conditional floor `1/5000` when `50b≤3(R+a)` | `overlapRightEnergy_floor` | same |
| Index one iff the form is nonnegative on the neutral-orthogonal complement of the middle | `hermNegIndex_neutralWindow_eq_one_iff_harmonic_nonneg` | `ChargeCancellationPreservesTheCertifiedFloor` |
| Green-channel overlap criterion | `riemannHypothesis_iff_forall_greenForm` | `TheGreenMatrixOfTheDyadicMiddleHasABoundStateChannelAndAPositiveChannel` |
| Below the middle binding energy, coupling loss adds to the common level of the parts | `hermNegIndex_neutralWindow_add_le_one_of_parts` | `TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle` |
| Uniform dyadic binding bound `1<μ_D` for `D≥1` | `one_lt_bindingEnergy` | `TheGreenMatrixOfTheDyadicMiddleHasABoundStateChannelAndAPositiveChannel` |

The spectral and conditional floors follow by canceling charge with the negative
ground vector. Completing the square identifies harmonic vectors with the Schur
complement. Raising its level increases its form at least at unit speed, giving
additive loss. The constant-vector Rayleigh quotient gives the uniform binding bound.

Direct Lean checks and transitive audits passed. The conditional-floor module was
checked from an unchanged source snapshot with appended axiom queries; the new
charge-cancellation module passed its direct project-file check. All listed audits
contain only `propext`, `Classical.choice`, `Quot.sound`. Umbrella imports are present.

The conditional coupling bound needed to prove the first overlap step is a separate
estimate, B194; these floors alone do not provide it.
