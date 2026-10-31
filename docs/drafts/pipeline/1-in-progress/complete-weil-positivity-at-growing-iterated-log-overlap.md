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

Split complementary quotients `N/n` at `2cY`, with
`Y=exp((log N)^ε)`. Above this threshold use uniform signed shell transfer;
below it retain the crude source bound and its harmonic measure. The latter
cost is polynomial in the conductor and in `log Y`, divided by `log N`.
The kernel, cutoff, downward, center and pole replacements must retain
explicit polynomial conductor costs before spectral assembly.

## Open inputs

- Uniform harmonic comparison for the actual upward source.
- Uniform polynomial conductor costs for every other residual component.
- Combination with the finite-coordinate certificate and conductor floor.

This target does not identify the agreement-shell square completion and does
not settle Q2 or Q3.
