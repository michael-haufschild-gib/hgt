# Exact spline cone cancellation with zero exponent of convergence

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** SC2; test whether arbitrarily strong polynomial zero-density bounds suffice.

Strengthen the exact-spline, bounded-local-density quartet model so that
for every `ε>0`, `Σ_i (1+Im z_i)^(-ε)<∞`. Retain exact coefficients
`(sinh z/z)^8`, unit multiplicities, distinct quartets, unattained positive
width, vanishing positive cone moments, and bounded cone coupling.

This would exclude every polynomial upper zero-density estimate as the
missing generic input to SC2, even with exact spline weights. The model
would still not be the actual zeta divisor.

## Candidate proof

The finite interpolation construction already chooses block sizes
`n_k≤U R^k`. Its matched heights satisfy
`H_k^8=n_k exp(4^(s+k))`, hence `H_k≥exp(4^(s+k)/8)`.
For `ε>0`, the inverse-power mass of block k is therefore at most
`U R^k exp(-ε4^(s+k)/8)`, a summable sequence. Actual node heights
are at least `H_k`; quartet reflection preserves ordinate magnitude.

The existing existential schedule theorem discards its geometric size
bound. Retain that bound from the explicit construction, then carry it
through the compatible-prefix nullseries and quartet construction.
No new interpolation or analytic assumption is needed.

## Audit

Corpus search found the existing geometric finite-cost theorem and sparse
exact-spline model, but no zero-exponent conclusion. The size bound and
summability must be formalized for the same final witness; separate
existence statements do not establish their conjunction. External priority
has not been checked. Complete the Gaussian criterion before this extension.
