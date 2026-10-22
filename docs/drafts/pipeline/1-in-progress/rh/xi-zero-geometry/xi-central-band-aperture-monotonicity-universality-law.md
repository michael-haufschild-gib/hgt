# Xi central-band aperture monotonicity universality law

Status: source written; exact Lean audit pending.

## Theorem-first origin

- `XiNormalizedApertureRelativeKrein.hasDerivAt_xiApertureModulusSq` identifies aperture derivative
  with actual Xi-orbit Krein slope.
- `HedenmalmCentralBandGaussianHankel.thetaXiHankelOrbit_kreinForm_nonneg_exactOffLineQuartetBand`
  proves that slope nonnegative for every positive aperture on every exact accretive central band.
- Mean-value monotonicity closes pointwise derivative sign into whole-ray order.

## Universal law

For every exact off-line-quartet accretive band and every frequency in it, squared modulus of actual
theta/Xi Hedenmalm orbit is nondecreasing on entire nonnegative aperture ray.

## Novelty and verification

Corpus scan found derivative identity and Krein positivity in separate terminal modules, with no
aperture monotonicity theorem. External literature audit and exact Lean audit remain pending.
