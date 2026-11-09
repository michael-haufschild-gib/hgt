# Orientation counts as actual determinant coefficients

- **ID:** RIAC-orientation-determinant
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Curve orientation counts](riac-curve-orientation-square-root.md)
- **Lean:** [OrientationDeterminant.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/OrientationDeterminant.lean)

## Exact count identity

For a finite point permutation `φ`, let `B_n` count stable permutation
orbits of point tuples and let `A_n` count stable orbits with the sign
orientation label. Both are the original independent finite counts,
including tuples with collisions. If `P_φ` is the actual permutation
matrix, then

`A_n−B_n = [t^n]det(1+tP_φ)`.

Also `Tr(P_φ^d)=#Fix(φ^d)`. All degrees and empty point sets are included;
no simple-spectrum hypothesis is used.

## Proof

The tuple comparison gives `A_n−B_n` as the sum of intrinsic orientations
of invariant `n`-point supports. For an invariant support, its principal
minor is exactly the induced permutation matrix, whose determinant is
its sign. A non-invariant finite support contains a point whose image
leaves the support; that minor has a zero row. The determinant coefficient
formula sums precisely these principal minors.

Permutation matrices reverse multiplication. For powers of one
permutation this still gives `P_φ^d=P_(φ^d)`. Its diagonal counts actual
fixed points, giving the trace identity.

## Lean declarations

`pointSubset_not_invariant`, `permutation_principal_minor`,
`pointOrientationPolynomial_coeff`, `pointTuple_orientationCount_eq_coeff`,
`permutation_power_trace`.

Direct Lean check and five transitive axiom audits: only `propext`,
`Classical.choice`, `Quot.sound`.

## Boundary

For curve Frobenius, the arithmetic trace values are supplied by the
[actual fixed-point theorem](riac-hyperelliptic-fixed-points.md). Their
finite-degree comparison with the curve's rational generating function
is supplied by the [trace-comparison theorem](riac-truncated-trace-comparison.md).
The determinant realization alone gives no square-root estimate and no
bound for the integer sum `1−M(N)`.
