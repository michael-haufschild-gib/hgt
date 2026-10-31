# Complete Weil positivity at growing iterated-logarithmic overlap

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `three-frontier-questions-full-solutions.md`, Q1.
- **Target:** For every `0<α<1/16`, the complete tilted-spline Weil matrix is
  positive definite for all sufficiently large `N`, uniformly over
  `1≤c≤(log log N)^α` and every coefficient vector.

## Mathematical route

Negative vectors have a fixed amount of mass on conductors
`m≤exp(C(c^16+1))+2`. This cutoff is `(log N)^o(1)` in the proposed range.
Uniform residue Mertens estimates already control reciprocal affine shells
for conductors bounded by powers of the logarithmic source scale.

Split complementary quotients at `2c exp(√log N)`. Signed shell transfer
controls the upper range; the linear source envelope controls its complement.
For every fixed `A≥0`, one constant and one eventual horizon control all
`m≤(log N)^A`. The literal upward residual satisfies

`‖U_res‖² ≤ K φ(m)² [c⁵/log N + c¹⁰(log N/N)² + c³/√log N]`.

Every component bound passes Lean with only `propext`, `Classical.choice`,
`Quot.sound`, including `K m⁴ c⁵/log N` for the full downward source.
The combined residual, spectral transfer and final direct audits remain pending.

The common conductor floor is `a/c⁷`. If both conductor cutoff and overlap
are at most `(log N)^(1/100)`, the summed squared residual divided by the
squared floor is at most `K'(log N)^(-21/100)`. The cutoff condition follows
from `16α<1`. Finite Ramanujan coordinate mass then excludes every
nonpositive eigenvector.

## Open inputs

- Lean verification of the combined quartic conductor residual.
- Lean verification of the finite-coordinate spectral transfer and actual Weil conclusion.
- Final direct audits and umbrella imports.

This target does not identify the agreement-shell square completion and does
not settle Q2 or Q3.
