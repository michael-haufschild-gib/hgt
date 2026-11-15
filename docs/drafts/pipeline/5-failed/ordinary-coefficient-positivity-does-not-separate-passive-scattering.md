# Ordinary coefficient positivity does not separate passive scattering

- **Stage:** 5-failed
- **Route:** select ζ from passive reciprocal Euler deformations using positive bounded multiplicative coefficients and any prescribed finite coefficient prefix.

**Counterexample:** for every prefix and every `1/2<σ<1`, a degree-one extended Selberg series has all these arithmetic properties, an entire reflection-symmetric completion, holomorphic contractive reduced scattering, unitary continuous-spectrum scattering, and a zero at real part σ. Lean: `PositiveEulerHorizon.exists_positive_passive_twin` in `BlackHoleRingdown/ThePositiveEulerTwinsArePassive.lean`.

**Positive survivor:** no nonnegative logarithmic Dirichlet series represents these twins; their two ordinary coefficients satisfy `a(p)²>2a(p²)`. More generally every real reciprocal quadratic fails a logarithmic count test at one of `p²,p⁴,p⁶,p⁸`, while ζ's values are `1/k>0`. Lean: `not_exists_nonnegative_logarithm`, `two_mul_coeff_prime_sq_lt_sq_coeff_prime`, and `PositiveFiniteEuler.exists_negative_even_eulerLogCoeff`.

Paper proofs and Lean formalizations complete: [passive twins](../3-formalized/positive-euler-twins-passive-horizons.md), [finite separator](../3-formalized/reciprocal-quadratics-fail-a-finite-logarithmic-count-test.md). Modules passed `lake --old env lean` and are umbrella-wired. Axiom checks skipped. One integrated contribution; no separate count for this failed route.
