# Polynomial cross-load through the compact interval

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** The complete profiled fifth even source is positive definite for
  every `x≥0`.

For `P(r)=(1−r²/2)²`, the exact differentiated correction is
`G_P(x)=(1−2x²)²G(x)−8x²(1−2x²)F(x)²`.
The source matrix is `H_P(x)=nativeShiftedMatrix 5 0 x+G_P(x)B`, with
`B=loadMapᵀ paidSevenSchur loadMap`.

[Proved positive regions](../3-formalized/theta-cusp-polynomial-cross-load-positive-regions.md):
origin and scale-eight neighborhoods, and a cofinal ray. The literal weighted
flux preserves every fifth even mixed entry, with index `2(i+j)`.

Remaining: positivity on the compact complement of those regions.
Neither continuity nor polynomial tail decay proves that compact sign.
Global rank-nine positivity remains open.

Explicit interval under formalization: `x≥0`, `1/2≤x²`, `x≤3/4`.
Here the complete slope bound `F'≥−24F` gives
`G_P≥(3/8)(2x²−1)F²≥0`, so native positivity pays the whole source.
