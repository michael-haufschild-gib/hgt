# Arbitrary prime support is detected by finitely many scalar jets

- **ID:** arbitrary-prime-support-is-detected-by-finitely-many-scalar-jets
- **Stage:** 3-formalized
- **Target:** Every nonzero finite auxiliary on arbitrary prime-exponent
  vectors has a nonzero scalar derivative below its support cardinality at
  every complex base point. No algebraicity of coefficients is needed.

## Argument

Unique factorization makes `primeProduct` injective. Positivity of these
integers makes their real logarithms injective. Thus the actual friable
auxiliary has distinct exponential frequencies. The proved exponential-sum
Vandermonde theorem gives a nonzero derivative of order below support size.
A finite reindexing transfers this to the original exponent-vector source.
Explicitly, index the support by `Fin n`, put `μ_j=−log(primeProduct j)`
and `c_j=P j`. If the first `n` jets vanished, the Vandermonde matrix on
the distinct `μ_j` would annihilate `c_j exp(s μ_j)`. Its invertibility and
nonvanishing of the exponential would give `P=0`, a contradiction.

This supplies finite scalar-jet recovery for every finite prime family.
It does not identify scalar multiplicity with multivariate multiplicity at
identical order; that sharper converse needs homogeneous-log independence.

## Inputs

`primeProduct_injective`, `primeProduct_pos`,
`exponentialSum_has_nonzero_iteratedDeriv_lt_card`,
`friableExponentDirichletExp`.

## Verification

`ArithmeticHarmonicAnalysis/FiniteScalarJetsDetectArbitraryPrimeSupport.lean`:
`friableExponentDirichletExp_has_nonzero_jet` and
`friableExponentDirichletExp_initial_jets_zero_iff`.
Direct `lake --old env lean` check passed. Transitive axioms:
`propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.
