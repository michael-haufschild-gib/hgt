# Asymmetric Xi heat minors

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** A nonpositive determinant of an ordered asymmetric positive-time Xi heat-trace kernel section falsifies RH.

## Source boundary

`HeatHankelMatrix.not_riemannHypothesis_of_det_submatrix_neg` treats principal moment
minors: its two submatrix selectors are equal. The proposed witness uses independently
ordered row and column time grids in `K(a,b)=trace(a+b)`; positive semidefiniteness
alone does not fix these determinant signs.

## Proposed mechanism

Under RH the actual heat trace is a sum of positive exponentials over positive squared
Xi frequencies. Ordered exponential determinants have a fixed sign. Cauchy–Binet
pairs two such determinants, and Hardy's infinitely many positive real zeros supply
strictly positive terms of every finite order.

`ExponentialKernelTotalPositivity.det_expKernel_neg_div_delta_pos` supplies the
strict exponential determinant sign; `CauchyBinet.factorial_mul_det_mul` supplies
the finite expansion. `FIDHankelTotalPositivity` demonstrates the monotone-truncation
limit mechanism, but its integer-divisor kernel is unconditionally positive and is
not the actual Xi heat trace.

A single fixed injective tuple of actual critical-line nodes supplies a positive
Cauchy–Binet term in every sufficiently large truncation. The factorial-scaled
determinants stay above that same term; entrywise convergence then preserves a
strict lower bound. No zero-spacing estimate or monotonicity of the full determinant
sequence is needed. Row and column parameters need only have positive pairwise sums.

## Open obligations

- Search for an existing asymmetric total-positivity criterion or equivalent endpoint.
- Locate and audit exponential determinant and infinite Cauchy–Binet infrastructure.
- Prove strictness and convergence for actual source data.

No total-positivity theorem or endpoint is yet claimed.
