# Integral cofinal Tate Gamma base-change law — formalization certificate

- **Paper theorem:** `ULF-ICTGBC-1`
- **Lean module:**
  `GaloisForLFunctions.RHTower.IntegralCofinalTateGammaBaseChange`
- **Targeted build:** passed
- **Axiom audit:** only `propext`, `Classical.choice`, `Quot.sound`

## Certified declarations

- `deningerIntegralGammaEvaluationComplex_mulVec`
- `deningerIntegralCofinalRelativeReflectionOperator_gamma_natural`
- `deningerPhysicalCofinalRelativeReflectionOperator_sq`

They prove coefficientwise Gamma evaluation intertwines the global integral curved Tate operator
with its physical reciprocal-reflection realization and that the latter squares to paired negative
Gamma curvature. No Xi comparison, integral physical landing, or RH conclusion is used.
