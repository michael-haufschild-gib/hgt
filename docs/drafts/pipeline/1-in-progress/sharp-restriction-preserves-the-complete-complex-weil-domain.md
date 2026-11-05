# Sharp restriction preserves the complete complex Weil domain

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Restricting any complete aperture form vector to any centered interval gives a vector in that exact interval's complete form domain, without a smoothing collar or positivity assumption.

## Proof route

Decompose the physical complex source into two real arithmetic graph sources.
Apply `sharpIntervalGraph` to each. Its proved exact support admission gives
two graph vectors in the target aperture. Transfer them through
`apertureGraphWeilEquiv` and recombine with coefficients `1` and `i`.
The source identities identify the result with literal sharp restriction;
the choice of open or closed right endpoint is null for Lebesgue measure.

The bounded Gamma crossing operator supplies sharp graph admission. No
unproved boundary regularity is used. The logarithmic/Weil domain identity
then transfers the conclusion to the literal logarithmic Fourier energy.
The complementary collar is the difference from the original vector.

## Lean status

Real-graph inputs are formalized in `RHTower/CHMDSharpSpatialCut.lean` and
`RHTower/CHMDRealApertureDomain.lean`. Complex reconstruction remains to be
formalized. Exact support splitting is an input to the proposed Riesz-kernel
variation law; no variation formula follows from admission alone.
