# The positive near-count model preserves the right-half-plane zero set

- **ID:** SPL-positive-model-Euler
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** Identify the actual generalized-integer Dirichlet series and its
  continuation for the odd-prime system with extra norms three and four.

## Proposed statement

For `Re s>1`,

`ζ_B(s)=ζ(s)/((1+2^(−s))(1−3^(−s)))`.

The right side continues the series analytically to `Re s>0`, away from
its pole at one. Its zeros there are exactly the zeros of `ζ`, with the
same multiplicities. This must be linked to `BeurlingSystem.zetaSeriesC`;
defining a quotient alone does not establish the claim for the model.

## Proof to formalize

The actual coordinate bijection gives the odd-integer Dirichlet series
multiplied by the geometric series in `3^(−s)` and `4^(−s)`. The odd series
is `(1−2^(−s))ζ(s)`. Cancelling
`1−4^(−s)=(1−2^(−s))(1+2^(−s))` gives the formula.

Absolute convergence must be proved before factoring the sums. A coarse
actual count bound `N_B(X)≤2X` suffices. For `Re s>0`, each `|q^(−s)|<1`
when `q>1`, so both remaining denominator factors are analytic and nonzero.

## Scope

This would certify a concrete logarithmic-scale count perturbation with
unchanged right-zero data. It supplies no exceptional zero and does not
resolve the minimum distance required to insert one. No Lean result or
external novelty claim is asserted yet.
