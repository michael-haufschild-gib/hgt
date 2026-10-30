# Bounded-overlap shell errors vanish uniformly in norm

- **ID:** bounded-overlap-shell-errors-vanish-uniformly-in-norm
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** one-horizon-makes-every-bounded-overlap-positive

## Statement

For fixed conductor, nonzero compact `C²` unit profile and `K≥1`, the
normalized reciprocal-shell residual tends to zero in Euclidean norm
uniformly over `1≤c≤K` and every family of shell shifts. Thus both overlap
and shifts may move arbitrarily with the integer horizon.

## Proof [PROVED HERE]

Write `R(X,c,b,n)` for the unnormalized signed source error. The common
weighted-source horizon makes `R→0` uniformly in all three parameters.
Its actual finite reading has absolute value at most
`2ϕ(m)⌈K⌉·mertensSum(⌊X⌋)`.
Choose one endpoint `Y` where every source error has size at most one.
The reading at `Y` then bounds every signed mean. For `X≤Y`, monotonicity
of the nonnegative Mertens sum bounds the source, while for `X≥Y` uniform
convergence applies. Hence `R` is bounded on the entire parameter space.

Its tail supremum `F(J)=sup_(X≥J,c,b,n)|R(X,c,b,n)|` is finite, nonnegative,
and tends to zero. Since `⌊N/n⌋≤N/n`, every reciprocal row error is bounded
by `F(⌊N/n⌋)/√n`, with the same majorant for every parameter choice.
The proved harmonic-quotient theorem gives

`Σ_(1≤n≤N) F(⌊N/n⌋)²/n = o(log N)`.

Pointwise domination and the exact normalized residual norm identity prove
the uniform norm claim. No interchange of pointwise limits is used.

## Lean formalization

`CriticalArithmeticCorrelationTheory/TheBoundedOverlapShellErrorsVanishUniformlyInNorm.lean`:

- `eventually_shiftedReciprocalUpwardRowError_sq_uniform_overlap`
- `eventually_normalizedShiftedReciprocalUpwardResidual_norm_uniform_overlap`
- `eventually_tiltedUnitSpline_shiftedReciprocalResidual_norm_uniform_overlap`

Direct Lean audit passed. All three transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Supporting estimate;
no separate contribution count.
