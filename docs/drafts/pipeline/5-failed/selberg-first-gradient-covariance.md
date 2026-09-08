# First-gradient covariance on four boundary channels

- **ID:** SELBERG-FIRST-GRADIENT-COVARIANCE
- **Stage:** 5-failed, for this specific local proposal only.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 6.

## Failed claim

The first-gradient Gram form of the quarter half-densities at boundary points infinity, zero, one, and minus one controls the squared norm of all mean-zero coefficients at the imaginary unit.

## Exact obstruction

The nonzero vector `(1,1,-1,-1)` has zero total coefficient mass and zero first-gradient moment. Its centered squared norm is four. Lean proves the stronger statement that no positive constant yields the proposed lower bound for arbitrary coefficients.

## Positive survivor

The trace-free second directional moment detects exactly the missing alternating channel. First and second moments recover the complete centered coefficient norm by an exact identity. Moreover, first derivatives at two heights recover that same second moment, giving a spatial recovery law using only first derivatives.

The survivor's dependency-closed paper proof and Lean status are recorded in [Boundary moment recovery at two heights](../3-formalized/selberg-boundary-moment-two-height-recovery.md). The module proves actual Frechet derivatives, the exact recovery identities, and the kernel classification. This local failure does not retire automorphic gluing or the full Selberg goal.
