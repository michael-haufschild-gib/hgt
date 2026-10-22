# Suzuki aperture-dressed wall light completion — formalized certificate

## Status

`[LEAN-PROVED] [UNCONDITIONAL] [SOURCE-SPECIFIC] [NO RH PREMISE] [NO COMPUTATION]`

## Paper source

`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-aperture-dressed-wall-light-completion.md`

## Lean source

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiApertureDressedWallLightCompletion.lean`

## Formal theorem surface

- `summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime`: actual critical
  Gamma/innovation source is square summable over all primes and valuation depths.
- `suzukiCriticalApertureBoundaryAtom_eq_wallField_mul_innovation`: dressing occurs before light
  projection.
- `suzukiCriticalApertureBoundaryAtom_neg_eq_star`: exact FE reflection survives dressing.
- `suzukiCriticalAperturePositiveLightLp_apply_eq_wallLight_mul_innovation` and negative analogue:
  completed vectors transport exact source light legs.
- `suzukiCriticalAperturePositiveLightKernel_sub_negative_eq_reflected` and
  `suzukiCriticalApertureReflectedCurrentKernel_add_negative_eq_positive`: exact global Ward laws.
- `suzukiCriticalAperturePositiveLightMatrix_posSemidef` and negative analogue: every finite height
  section is a literal completed Gram.
- `suzukiCriticalApertureBoundaryFieldKernel_diagonal_height_independent`: exact obstruction to
  claiming this carrier alone proves RH.

## Scientific status

All-prime pre-split Hilbert existence and forced light completion are closed.  Height-flat theorem
falsifies direct Ward-defect discharge.  Remaining RH-bearing theorem is actual restricted-Weil
resolvent/marked Robin/Gamma/holonomy rectangular transfer with bounded negative channel.

## Verification

- Direct Lean check: passed.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration and whitespace scans: clean.
- Final targeted build passed:
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` (`9461/9461`).
- Repository lint reaches new module; remains red on 21 unrelated concurrently unreachable
  modules.
