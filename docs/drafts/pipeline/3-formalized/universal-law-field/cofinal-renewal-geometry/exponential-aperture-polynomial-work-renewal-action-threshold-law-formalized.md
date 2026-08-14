# Exponential Aperture / Polynomial Work Renewal-Action Threshold Law — Lean certificate

## Status

- **ID:** ULF-CRG-1-LEAN
- **Paper parent:** `exponential-aperture-polynomial-work-renewal-action-threshold-law.md`
- **Stage:** 3 — formalized in Lean 4
- **Closure:** FULL for every dependency-closed theorem and corollary on the paper card
- **Claim boundary:** renewal geometry and exact source-horizontal examples only; no Riemann-hypothesis or canonical-arithmetic-renewal claim

## Formal modules

- `GaloisForLFunctions.HTGeometry.ConstitutiveLocalRenewalActionThreshold`
- `GaloisForLFunctions.HTGeometry.ConstitutiveExtendedRenewalActionThreshold`
- `GaloisForLFunctions.HTGeometry.ConstitutiveApertureInformationProjection`
- `GaloisForLFunctions.HTGeometry.ConstitutiveLocalRenewalSharpness`
- `GaloisForLFunctions.HTGeometry.ConstitutiveSourceHorizontalRenewalPrice`
- Umbrella: `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Theorem coverage

Paper theorem CRG.1–CRG.2 is formalized by:

- `aperture_klDiv_eq_binary_add_cond`: exact aperture binary-KL plus conditional-KL disintegration.
- `aperture_binary_klDiv_le`: data-processing lower bound.
- `aperture_binary_klDiv_eq_iff`: equality exactly when both conditional laws agree.

Paper theorem CRG.3 is formalized without an existence surrogate by:

- `apertureProjectionDensity` and `apertureProjection`: literal piecewise Radon–Nikodym density and projected probability measure.
- `rnDeriv_apertureProjection`, `llr_apertureProjection`, and `integrable_llr_apertureProjection`: exact density, log-likelihood ratio, and integrability.
- `klDiv_apertureProjection_eq_bernoulli`: exact projected cost.
- `klDiv_apertureProjection_le`: genuine information-projection minimality.

Paper theorem CRG.4–CRG.7 is formalized by:

- `exponentialAperture_localAction_lower` and `polynomialCurrent_scaledAction_lower`: exact local and scaled lower bounds.
- `exponentialAperture_polynomialCurrent_action_liminf_ennreal`: extended-real sharp liminf coefficient, retaining infinite KL coordinates.
- `exponentialAperture_polynomialCurrent_action_eq_top_of_degree_le_two`: unconditional divergence for polynomial degree at most two, including schedules with infinite coordinates.

Paper theorem CRG.8–CRG.11 is formalized by:

- `lowerSemicontinuous_binaryRenewalAction`.
- `isClosed_binaryRenewalActionSublevel` and `isCompact_binaryRenewalActionSublevel`.
- `isClosed_persistentCurrentLocus` and `isCompact_binaryRenewalActionSublevel_inter_persistentCurrentLocus`.
- `binaryRenewalActionSublevel_inter_persistentCurrentLocus_eq_empty`: subcritical finite-action exclusion.
- `exponentialPolynomialBinaryRenewal_sharp`: exact superquadratic two-point witness with persistent current and finite action.
- `exponentialPolynomialBinaryRenewal_enters_finiteActionSublevel`: explicit entrance into a compact finite-action sublevel.

Paper theorem CRG.12–CRG.13 and Corollary 5.1 are formalized by:

- `sourceHorizontalForward_orientationRenewalPrice`: exact forward coefficient `c(2-a)/(2a)` and divergent total KL cost.
- `sourceHorizontalReverse_orientationRenewalPrice`: exact reverse coefficient `c/a` and divergent total KL cost.

## Closure and kernel audit

- All capstone declarations are closed Lean theorems; no project axiom, premise surrogate, `sorry`, `admit`, `opaque`, or `unsafe` declaration is used.
- Scoped forbidden-token scan over all five modules is clean, including computation tactics prohibited by the card workflow.
- `#print axioms` on disintegration, equality, projection, liminf, divergence, compactness, sharpness, entrance, and both source-horizontal capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Direct source checks passed for all five modules and the `UniversalLawField` umbrella.
- Targeted module builds passed for all five modules. No full build was run.
- Global formal lint was run. Its failures were confined to unrelated concurrent shared-tree work (unreachable `RHTower`/other HTGeometry modules and an unrelated `sorry` in `HighFrequencyTransportBound.lean`); none names these modules or this umbrella wiring.

## Verification commands

```text
lake env lean formal/GaloisForLFunctions/HTGeometry/ConstitutiveLocalRenewalActionThreshold.lean
lake env lean formal/GaloisForLFunctions/HTGeometry/ConstitutiveExtendedRenewalActionThreshold.lean
lake env lean formal/GaloisForLFunctions/HTGeometry/ConstitutiveApertureInformationProjection.lean
lake env lean formal/GaloisForLFunctions/HTGeometry/ConstitutiveLocalRenewalSharpness.lean
lake env lean formal/GaloisForLFunctions/HTGeometry/ConstitutiveSourceHorizontalRenewalPrice.lean
lake env lean formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveLocalRenewalActionThreshold
lake build GaloisForLFunctions.HTGeometry.ConstitutiveExtendedRenewalActionThreshold
lake build GaloisForLFunctions.HTGeometry.ConstitutiveApertureInformationProjection
lake build GaloisForLFunctions.HTGeometry.ConstitutiveLocalRenewalSharpness
lake build GaloisForLFunctions.HTGeometry.ConstitutiveSourceHorizontalRenewalPrice
```
