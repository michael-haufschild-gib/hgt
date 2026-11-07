# Smooth atlas of the cubic quotient

- **ID:** cubic-quotient-smooth-atlas
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual cubic-kernel quotient has a smooth three-dimensional atlas, and its hyperbolic covering projection is smooth.

Real horizontal coordinates and positive height identify hyperbolic space
with an open subset of `ℝ³`. Local inverses of the covering projection
supply quotient charts. If two continuous lifts project to the same map,
their values differ by a deck transformation at the base point. Local
injectivity makes this one fixed transformation valid nearby. Chart
transitions therefore agree locally with a Möbius coordinate map. Its
positive denominator makes it smooth. The same argument proves smoothness
of the projection.

Lean: `MetaplecticMobiusDescent/TheCubicQuotientHasASmoothAtlas.lean`,
`kernelSpatialIsManifold` and `kernelProjection_contMDiff`.
Direct source and transitive axiom audits passed; only `propext`,
`Classical.choice`, and `Quot.sound`.

Adapted from OpenAI `CubicSieve/RowCaps.lean`,
`MeanSquare/TransformedColumns.lean`, and `Eisenstein/SmoothTests.lean`.
No invariant energy estimate or spectral continuation is asserted here.

`SmoothTestsOnTheCubicQuotient.lean` proves
`kernelQuotientVolume_fullSupport`, `kernelSmoothTestsToL2_injective`,
and `kernelSmoothTestsToL2_dense`. Translates of any nonempty open
hyperbolic set have a countable subcover; invariant nonzero volume gives
positive mass. Fundamental-domain transport gives quotient full support.
Continuous almost-everywhere equality is then pointwise equality. Finally,
compact continuous approximation and smooth uniform approximation give
`L²` density, since quotient volume is finite. Source and transitive axiom
audits pass with the same standard axioms.
