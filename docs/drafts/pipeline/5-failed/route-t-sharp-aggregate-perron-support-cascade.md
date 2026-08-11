# Route T sharp aggregate Perron support cascade

## Status

- Route: T
- State: failed/retired
- Date: 2026-08-11
- [x] negative mechanism dependency-closed on paper
- [x] strongest positive survivor dependency-closed in Lean
- [ ] final umbrella build/lint/axiom audit

## Retired target

Apply finite-height sharp Perron to the signed aggregate of exactly those dyadic Heath--Brown boxes
which meet a von-Mangoldt prefix, so signed coefficient cancellation removes every boxwise
truncation error.

## Exact obstruction

The finite Heath--Brown packet equals `Lambda(n)` only inside its algebraic coefficient cutoff.
Selecting boxes whose lower support edge meets a target `N` gives exact cancellation through `N`,
but each selected box extends to a constant multiple of `N`. Immediately above `N`, omitted boxes
with lower edge greater than `N` may contribute, so the selected aggregate is not the full packet
and its coefficients need not equal `Lambda`. Enlarging the selected lower-edge range restores
cancellation only through the enlarged range while extending support by the same multiplicative
factor. Repeating this creates a support cascade. Sharp finite-height Perron samples that artificial
tail, so aggregation alone does not eliminate the truncation error.

This is a structural mismatch, not weak coefficient bookkeeping: truncating the aggregate restores
support but destroys the Dirichlet-product factorization needed by large-values estimates.

## Strongest positive survivor

Compactly supported Mellin smoothing kills the cascade exactly. In
`Sieve/HeathBrownSmoothAggregatePerron.lean`, if the smoothing support lies inside
`X < (L+1)^k`, Lean proves:

1. the finite packet and `Lambda` agree pointwise at every coefficient seen by the weight;
2. every coefficient outside the identity range has zero weight;
3. the full packet L-series is the signed finite sum of literal dyadic factor products;
4. the smoothed von-Mangoldt sum is exactly one vertical integral of that aggregate.
5. subtracting adjacent prefixes gives an exact smooth short-window formula supported in
   `[N,N+2H]` as a difference of aggregate Mellin integrals.

There is no finite-height truncation error or artificial tail. Remaining obstacle is pure structured
large-values control of the aggregate, not Perron support.

## New insight

Signed cancellation and multiplicative factorization are compatible only before a sharp
coefficient truncation. Compact support should be imposed by the test function, not by deleting
Dirichlet-product coefficients. This is the correct aggregation order for Route T.

## Log

- 2026-08-11 — sharp aggregate support cascade isolated; compactly supported smooth aggregate
  replacement formalized and direct-checked.
