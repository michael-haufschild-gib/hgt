# Integral relative-reflection complex fusion law — Lean certification

- **ID:** `ULF-IRRCF-1`
- **Paper card:**
  `completion-index-transgression-mechanics/integral-relative-reflection-complex-fusion-law.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.IntegralRelativeReflectionComplexFusion`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `deningerIntegralRelativeReflectionDifferential`: universal integral matrix with Laurent arrows
  `T-1` and `T^-1-1`.
- `deningerIntegralRelativeReflectionDifferential_evaluation`: physical Gamma evaluation is
  exactly the curved relative-reflection suspension.
- `det_deningerIntegralRelativeReflectionDifferential`: determinant is minus the integral
  Hermitian quadratic ghost.
- `deningerIntegralRelativeReflectionDifferential_sq`: exact source Clifford law
  `C_T^2=kappa I`.
- `deningerIntegralRelativeReflection_determinant_evaluation`: determinant evaluation is positive
  paired Gamma curvature.

## Verification

```text
lake env lean /tmp/integral_relative_reflection_scratch.lean
lake env lean GaloisForLFunctions/RHTower/IntegralRelativeReflectionComplexFusion.lean
lake build GaloisForLFunctions.RHTower.IntegralRelativeReflectionComplexFusion
lake env lean /tmp/integral_relative_reflection_axioms.lean
```

Scratch, direct module check, targeted module build, and axiom audit passed. Every certified
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into
universal-law umbrella; no umbrella build was run.

## Exact field consequence

Integral Laurent formation, functional-equation reflection, and Gamma curvature now share one
literal source object and one exact conservation identity. Remaining RH gate is no longer fusion:
it is finite integral landing of this object on existing canonical Xi jet layers.
