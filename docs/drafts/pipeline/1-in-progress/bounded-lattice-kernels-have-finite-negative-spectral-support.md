# Bounded lattice kernels and finite negative spectral support

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** route-obstacles B9, converse Krein–Langer without a zero configuration.
- **Statement:** A bounded Hermitian kernel on a countable free abelian group has
  finite negative index iff it is a positive-definite kernel minus a finite
  positive combination of unitary characters. The least number of distinct
  negative characters equals its negative index.
  This includes the Hecke lattice of positive rationals.

## Proposed bridge

The Pontryagin decomposition supplies corrections `φ_i`, each a finite
linear combination of translates of the bounded kernel. Thus every `φ_i`
is bounded. Add the Fejér density
`q_N = |F_N|⁻¹ Σ_i |Σ_{x∈F_N} φ_i(x) χ_x|²` to the kernel's signed
Fejér density. Both resulting densities are nonnegative. Character
orthogonality bounds the correction mass by `Σ_i ‖φ_i‖∞²`, independently
of the window and its rank. The two measures have uniformly bounded masses
`a_N⁺,a_N⁻`, with `a_N⁺−a_N⁻=k(0)`. Their difference has Fourier coefficients
`fejerWeight N m · k(m)`, tending to `k(m)` by
`ArithmeticPositiveDuality.tendsto_fejerWeight`.

For a common mass bound `C>0`, pad each normalized measure to a probability:
`ρ_N±=ν_N±/C+(1−a_N±/C)δ₀`. Then
`ν_N⁺−ν_N⁻=C(ρ_N⁺−ρ_N⁻)+k(0)δ₀`. Compactness of torus probabilities
gives a signed spectral measure for `k`. Exhausting the generators extends
the construction to a countable free lattice: the same mass bound holds on
every finite-rank head, and each fixed character eventually belongs to a head.

`HeckeKreinToeplitz.exists_pontryagin_decomposition` supplies finitely many
correction functions in the translate span. Under the signed representation,
these are bounded linear functionals on `L²(|μ|)`. Torus polynomial density
(`HTGeometry.exists_torusTrigPoly_approx` on finite tori,
`HTGeometry.span_torusCharacter_closure_eq_top` on countable tori) extends the corrected positivity
to `L²(|μ|)`. The negative spectral subspace injects into the correction space,
so has dimension at most `κ`. Disjoint positive-mass sets then force the
negative measure to have at most `κ` atoms. Those atoms provide that many
character-square corrections, giving the reverse index bound and equality.

A direct finiteness argument uses the bounded correction densities `q_i`.
Testing the extended inequality on an indicator in the negative Hahn set
gives `ν(A) ≤ (Σ_i ‖q_i‖∞²)ν(A)²`. Every positive subset therefore has a
fixed positive mass floor. Neighborhoods of a support point give the same
floor for its singleton, so finite total mass forces finite support.
On those atoms the correction map is injective; hence their number is at
most `κ`. Atomic character-square corrections give the reverse inequality.

## Unclosed steps

1. Stationary signed-measure representation from boundedness and finite index.
2. Negative-index equality for a finite signed torus measure, including its
   nonatomic part.
3. Exact character decomposition and transitive Lean audit.

No paper proof or formal theorem claimed. Unbounded kernels require additional
structure and are outside this statement.
