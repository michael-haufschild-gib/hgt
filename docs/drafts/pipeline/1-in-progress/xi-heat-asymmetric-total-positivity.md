# Asymmetric Xi heat minors

- **Stage:** 1-in-progress
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

## Open obligations

- Search for an existing asymmetric total-positivity criterion or equivalent endpoint.
- Locate and audit exponential determinant and infinite Cauchy–Binet infrastructure.
- Prove strictness and convergence for actual source data.

No total-positivity theorem or endpoint is yet claimed.
