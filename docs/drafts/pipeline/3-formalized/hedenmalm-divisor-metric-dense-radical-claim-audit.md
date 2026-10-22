# Internal claim audit — Hedenmalm divisor metric no-go paper

This file is an internal verification record. It is not part of the manuscript and supplies no
novelty or significance credit.

## Manuscript-to-theorem trace

| Manuscript claim | Internal theorem surface |
|---|---|
| Normalized theta source is Schwartz and has Fourier transform `Xi` | `ThetaCuspSchwartz.lean`; `thetaCuspFullSource_pos_all`; `fourier_xiThetaSchwartzSource` |
| Positive momentum-symmetric Schwartz forms have a unique positive temperate spectral measure | `SchwartzPositiveMeasureRepresentation.lean`; `existsUnique_temperateSpectralRepresentation` |
| Theta nullity is equivalent to support on the real `Xi` divisor | `universalPositiveForm_thetaNull_iff_canonicalMeasure_support_realDivisor` |
| Canonical measure is purely atomic on the real divisor | `universalPositiveForm_canonicalMeasure_atomic_of_thetaNull` |
| Theta diagonal nullity gives full radical nullity | `universalPositiveForm_theta_leftRadical_of_thetaNull` |
| Ordinary-`L²` radical image is dense, proper, and nonclosed | `universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw`; `xiThetaL2RadicalImage_ne_top`; `not_isClosed_xiThetaL2RadicalImage` |
| Radical cannot equal the one-dimensional source-kernel line | `not_exists_nonzero_universalPositiveForm_thetaNull_exactSourceLineRadical` |
| Fixed-energy ordinary-`L²` null sequence exists | `exists_xiThetaL2Null_constantEnergy_sequence` |
| Sequential ordinary-`L²` closability is equivalent to the zero form | `universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_zero` |
| No nonzero continuous ordinary-`L²` extension exists | `xiThetaSchwartzForm_eq_zero_of_l2_extension`; `not_exists_nonzero_xiThetaSchwartzForm_l2_extension` |
| Eigenprofile diagonal is divisor mass times `‖Xi′‖²`; nonreal profiles are null | `xiDivisorSupportedPolarization_thetaEigen_diagonal`; `xiDivisorSupportedPolarization_thetaEigen_eq_zero_of_not_real` |
| Conservativity implies RH and simplicity; exact converse criterion | `xiThetaMetricConservative_implies_rh_and_simple`; `xiThetaMetricConservative_iff_mass_pos_and_simple` |

## Foreground proof audit

The following files passed separate foreground commands of the required form:

```text
lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspSchwartzFourierXi.lean
lake env lean GaloisForLFunctions/RHTower/XiThetaSchwartzL2Nonclosability.lean
lake env lean GaloisForLFunctions/RHTower/XiThetaSpectralOrientationClassification.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmUniversalPositiveFormClassification.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean
lake env lean GaloisForLFunctions/RHTower/XiDivisorSupportedMetric.lean
```

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for every headline
theorem. No manuscript result depends on a project axiom.

Repository-wide `scripts/formal_tools.py lint` reached an unrelated pre-existing umbrella error:

```text
owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry:
GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacePacketDisjointness
```

No target file failed compilation, and the lint run reported no forbidden declaration in this
paper's theorem surface.

## Final release gate

Both named-module builds completed successfully:

```text
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw
lake build GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
```

The post-build axiom audit addressed the actual compiled source-core no-go theorem and again
reported only `propext`, `Classical.choice`, and `Quot.sound`. A final process check found no
running `lean` or `lake` process.
