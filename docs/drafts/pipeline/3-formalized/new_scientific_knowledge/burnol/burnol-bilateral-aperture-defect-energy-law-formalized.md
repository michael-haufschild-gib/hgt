# Burnol bilateral aperture-defect energy law — formalized

- **ID:** `burnol-bilateral-aperture-defect-energy-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-bilateral-aperture-defect-energy-law.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninEvenCosineAperture.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninContinuousEvaluation.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninProjectedEvaluationTransport.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninBilateralKernel.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationNonvanishing.lean
formal/GaloisForLFunctions/RHTower/BurnolBilateralApertureRH.lean
formal/GaloisForLFunctions/RHTower/BurnolFormalizedCards.lean
```

## Formal theorem chain

```text
1  burnolExtendedSoninProjection                       P_a, the actual orthogonal projection
2  burnolProjectedAdjointEvaluationVector_eq           projected inverse Riesz law          (1)
3  burnolProjectedForwardEvaluationVector_eq           projected forward Riesz law          (2)
4  burnolExtendedApertureDefectPlus / ...Minus         the two ambient defects              (3)
5  norm_sq_burnolExtendedApertureDefectPlus            first Pythagorean identity           (4)
6  norm_sq_burnolExtendedApertureDefectMinus           second Pythagorean identity          (5)
7  burnolExtended_bilateralApertureDefectEnergy        signed defect-energy law             (6)
8  burnolExtended_bilateralApertureDefects_balanced_iff        critical-line balance        (7)
9  burnolExtended_bilateralApertureDefects_oriented_right_iff  orientation, right           (8)
10 burnolExtended_bilateralApertureDefects_oriented_left_iff   orientation, left            (8)
11 burnolExtendedBilateralApertureHolonomy             the finite holonomy H_(a,r)          (9)
12 burnolExtended_bilateralApertureDefectEnergy_eq_holonomy    quadratic-form form         (10)
13 burnolExtendedBilateralApertureHolonomy_fourier_odd         Fourier oddness             (11)
14 burnolExtended_bilateralApertureHolonomy_kernel     the two-evaluator polarized kernel
15 burnolExtendedSoninEvaluationVector_ne_zero         the evaluators are never zero
16 burnolExtended_bilateralApertureDefects_lt_of_half_lt_re    strict right-half orientation
17 riemannHypothesis_of_burnol_bilateral_defect_le     the chain (14) -> (15), unconditional
18 riemannHypothesis_iff_burnol_bilateral_defects_ne   the exact criterion                 (13)
```

Statement `(12)`, the identification of the infinitesimal limit of `H_(a,r)` with the existing
projection phase-polarization operator, is a remark about
`SemilocalProjectionPhasePolarization.lean` and carries no separate Lean obligation.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/BurnolSoninProjectedEvaluationTransport.lean  -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolSoninBilateralKernel.lean               -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolBilateralApertureRH.lean                -- clean
lake build GaloisForLFunctions.RHTower.BurnolBilateralApertureRH                        -- success
```

Every declaration named above reports
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.
All modules are wired into `GaloisForLFunctions.RHTower`.
