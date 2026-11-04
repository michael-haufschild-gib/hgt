# Polynomial cross-load through the compact interval

- **Stage:** 1-in-progress
- **Type:** FALSIFIED
- **Wall:** Σ6
- **Refuted claim:** The complete profiled fifth even source is positive definite
  for every `x≥0`.

For `P(r)=(1−r²/2)²`, the exact differentiated correction is
`G_P(x)=(1−2x²)²G(x)−8x²(1−2x²)F(x)²`.
The source matrix is `H_P(x)=nativeShiftedMatrix 5 0 x+G_P(x)B`, with
`B=loadMapᵀ paidSevenSchur loadMap`.

[Proved positive regions](../3-formalized/theta-cusp-polynomial-cross-load-positive-regions.md):
origin and scale-eight neighborhoods, and a cofinal ray. The literal weighted
flux preserves every fifth even mixed entry, with index `2(i+j)`.

[Explicit interval](../3-formalized/theta-cusp-polynomial-cross-load-positive-interval.md):
`x≥0`, `1/2≤x²`, `x≤3/4`.
Here the complete slope bound `F'≥−24F` gives
`G_P≥(3/8)(2x²−1)F²≥0`, so native positivity pays the whole source.

At `x₃₂=log(32/π)/2`, both `H_P(x₃₂)` and the literal weighted source for every
`0<a<1/2` fail positive semidefiniteness. Lean:
`ThirtyTwoCrossObstruction.repair_not_posSemidef` and
`weightedRepair_not_posSemidef` in `FifthEvenPolynomialCrossObstruction`.

Positive survivor: the exact scalar-load capacity at this center satisfies
`0<τ<1`, with PD precisely for `t<τ`, PSD precisely for `t≤τ`, and a singular
boundary (`ThirtyTwoCrossCapacity.exact_scaling_capacity`).
The aperture-dependent capacity classification and final audits remain pending;
the route is not yet retired. Global rank-nine positivity remains open.
