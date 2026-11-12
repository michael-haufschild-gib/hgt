# The critical half-line Laplace transform is zero-free in the right half-plane

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** B104; complex factorization of the actual critical-state line.
- **Statement:** Every actual critical half-line state F at a finite global window threshold has `∫ exp(zu) F(u) du ≠ 0` whenever `Re z>0`.
- **Status:** Lean verified; imports wired.

## Proof

At a nonreal zero, reflect at that zero and its conjugate. Conjugation and
commutation give a real representative; cancellation of both exponential
tails preserves negative-half-line support. The paired reflection preserves
all six fields of the actual energy domain, every translated correlation,
the prime sum, Gamma energy and the opposite half-pole moment product.

Only exponential mass changes. Its exact loss is a positive coefficient
times the sum of the two weighted resolvent energies. Global-threshold
nonnegativity and zero ground-state energy force the first resolvent to
vanish. Resolvent injectivity then contradicts the state's unit norm.
The verified real-reflection theorem handles positive real zeros.

## Lean

Owner: `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/`.
Final module: `TheCriticalHalfLineStateHasNoRightHalfPlaneLaplaceZero`.

- `ae_eq_zero_of_fullEnergy_zero_of_complex_laplace_zero`: every actual zero-energy profile with such a zero vanishes almost everywhere.
- `criticalHalfLineGroundState_complexLaplace_ne_zero`: actual-state nonvanishing throughout the open right half-plane.
- `riemannHypothesis_or_exists_complexLaplaceZeroFree_criticalHalfLineGroundState`: unconditional RH dichotomy.

No state-positivity or polar-threshold-equality premise is used. Imaginary-axis
nonvanishing, outer factorization and the arithmetic polar charge remain open.
