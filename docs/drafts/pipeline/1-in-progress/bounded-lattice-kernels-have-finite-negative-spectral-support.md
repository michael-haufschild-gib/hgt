# Bounded lattice kernels and finite negative spectral support

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** route-obstacles B9, converse Krein–Langer without a zero configuration.
- **Statement:** A bounded Hermitian kernel on a finite-rank integer lattice has
  finite negative index iff it is a positive-definite kernel minus a finite
  positive combination of unitary characters. The least number of distinct
  negative characters equals its negative index.

## Proposed bridge

Split each lattice Toeplitz section into its positive and negative matrix
parts. Its negative trace is at most `κ·dim(section)·‖k‖∞`.
The Fejér measures of those two parts therefore have uniformly bounded masses
`a_N⁺,a_N⁻`, with `a_N⁺−a_N⁻=k(0)`. Their difference has Fourier coefficients
`fejerWeight N m · k(m)`, tending to `k(m)` by
`ArithmeticPositiveDuality.tendsto_fejerWeight`.

For a common mass bound `C>0`, pad each normalized measure to a probability:
`ρ_N±=ν_N±/C+(1−a_N±/C)δ₀`. Then
`ν_N⁺−ν_N⁻=C(ρ_N⁺−ρ_N⁻)+k(0)δ₀`. Compactness of torus probabilities
gives a signed spectral measure for `k`.

`HeckeKreinToeplitz.exists_pontryagin_decomposition` supplies finitely many
correction functions in the translate span. Under the signed representation,
these are bounded linear functionals on `L²(|μ|)`. Torus polynomial density
(`HTGeometry.exists_torusTrigPoly_approx`) extends the corrected positivity
to `L²(|μ|)`. The negative spectral subspace injects into the correction space,
so has dimension at most `κ`. Disjoint positive-mass sets then force the
negative measure to have at most `κ` atoms. Localization at these atoms gives
the reverse index bound and the exact character decomposition.

## Unclosed steps

1. Stationary signed-measure representation from boundedness and finite index.
2. Negative-index equality for a finite signed torus measure, including its
   nonatomic part.
3. Exact character decomposition and transitive Lean audit.

No paper proof or formal theorem claimed. Unbounded kernels require additional
structure and are outside this statement.
