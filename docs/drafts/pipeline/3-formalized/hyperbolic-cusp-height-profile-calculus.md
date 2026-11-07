# Laplacian of a transformed cusp-height profile

- **ID:** hyperbolic-cusp-height-profile-calculus
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [exterior coercivity](../1-in-progress/cubic-quotient-exterior-coercivity.md)
- **Statement:** For every nonzero complex row and smooth profile on positive heights, the negative hyperbolic Laplacian satisfies `Δ_axis F(h)=h²F″(h)−hF′(h)`. The row height is the actual transformed cusp height.

Write the denominator as
`Q=A(x²+y²+v²)+2(Bx+Cy)+D`, with `AD=B²+C²`.
The identity
`(Ax+B)²+(Ay+C)²+(Av)²=AQ` gives
`v²|∇log(v/Q)|²=1` and `Δ_axis log(v/Q)=−2`.
Apply the second-order chain rule to `F(exp(log h))`. Its second derivative
contributes `h²F″+hF′`, and its first derivative contributes `−2hF′`.
This gives the stated formula. Axis derivatives commute with finite sums
and depend only on the germ in positive half-space.

Lean: `MetaplecticMobiusDescent/HyperbolicLogarithmicHeight.lean` and
`HyperbolicHeightProfiles.lean`, namespace `CubicEisenstein`:

- `heightLog_eikonal`, `heightLog_laplacian`.
- `cosetHeight_upperPoint_rowHeight`.
- `rowProfile_laplacian`.
- `axisLaplacian_finset_sum`, `axisLaplacian_congr_positive`.

Direct source and transitive audits pass with only `propext`,
`Classical.choice`, and `Quot.sound`. The positive Laplacian is the
negative of `Δ_axis`, so it sends height to height. The invariant barrier
and exterior coercivity remain open. Adapted from OpenAI
`CubicSieve/TwistedProfiles.lean`, `QuadraticSieve/SpatialDerivatives.lean`,
and `Eisenstein/SmoothCuspCutoffs.lean`.
