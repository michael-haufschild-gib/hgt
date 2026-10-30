# The actual upward source is uniform on bounded overlap

- **ID:** the-actual-upward-source-is-uniform-on-bounded-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** one-horizon-makes-every-bounded-overlap-positive

## Statement

For a nonzero compact `C²` unit profile and fixed conductor, the normalized
literal upward prime-power residual tends uniformly to zero for `1≤c≤K`.
Every prime power and both actual horizon cutoffs are retained.

## Proof [PROVED HERE]

Put `M=∫φ²`, `G=φ⋆φ`, `B=⌈K exp K⌉`. The exact offset identity confines
all actual upward products to offsets at most `B`. Let `L` be a global
Lipschitz constant of `G` and set `A=K exp K+2K+1`. Whenever either the
logarithmic or reciprocal kernel is active, integer separation gives
`N≤AT` and `N≤Aj`. For `N≥2AB`, the proved logarithm and square-root
estimates therefore give a common kernel error `C/N`, with
`C=4LA²B²+ABM`; the factor `1/c` is at most one. Summing the literal
prime-power source bounds its coefficient error by
`D mertensSum(N+B)/N`, where `D=2Bϕ(m)C/M`. This tends to zero and its
squared harmonic row norm does too.

Moving the two horizon cutoffs to `kn≤N` costs at most
`4Bϕ(m) primeIndexBoundaryMass(B,⌊N/n⌋)`. This boundary mass tends to zero;
the harmonic quotient theorem gives one vanishing squared norm majorant.
Monotonicity in `B` makes the estimate valid for every smaller actual strip.

The remaining reciprocal source is exactly half the sum of the positive
and reflected affine shell corrections. Their signed means agree. The
uniform weighted-source theorem and its harmonic majorant give a common
vanishing norm for both corrections. Finally, the square of the sum of
these three errors is at most three times the sum of their squares.
The exact residual norm identity completes the uniform limit.

## Lean formalization

`CriticalArithmeticCorrelationTheory/TheActualUpwardSourceIsUniformOnBoundedOverlap.lean`:

- `exists_logPrimeKernel_uniform_overlap_bound`
- `eventually_actualUpwardRowError_sq_uniform_overlap`
- `eventually_normalizedUpwardPrimeResidual_norm_uniform_overlap`
- `eventually_tiltedUnitSpline_normalizedUpwardPrimeResidual_norm_uniform_overlap`

Direct Lean audit passed. All three transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Supporting source theorem;
no separate contribution count.
