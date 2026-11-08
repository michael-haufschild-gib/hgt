# From actual Frobenius traces to signed coefficients

- **ID:** RIAC-truncated-trace-comparison
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Curve orientation counts](riac-curve-orientation-square-root.md)
- **Statement:** Identify the independently constructed degree-`n` orientation discrepancy with the actual reciprocal curve-zeta coefficient, using only Frobenius traces through degree `n`.

## Exact mechanism

Let `Λ` be the diagonal multiset of a Schur triangulation of the actual
point permutation matrix, and let `Α` be the actual reciprocal-root
multiset. For `1≤d≤n`, fixed-point counting gives
`Σ_(λ∈Λ)λ^d + Σ_(α∈Α)α^d = 1+q^d`.
Newton identities therefore identify the elementary symmetric functions
of `Λ+Α` and `{1,q}` through degree `n`; equal multiset cardinalities
are neither available nor required.

Consequently `det(1+tP)∏_(α∈Α)(1+αt)` agrees with `(1+t)(1+qt)`
through degree `n`. Multiplication by the actual inverse root polynomial
preserves this agreement through degree `n`. The determinant realization
then gives

`A_n−B_n = [t^n](1+t)(1+qt)∏_(α∈Α)(1+αt)⁻¹`.

The derived Stepanov root bound must discharge every root-norm input in
the coefficient estimate. No trace or Weil-bound assumption may remain
in the actual curve theorem. A single finite ambient field supplies only
the required finite-degree trace identities, not a global series identity.

## Boundary

The integer target remains `Σ_p index_p(N)=1−M(N)`. This curve
comparison does not supply an integer-height transfer.
