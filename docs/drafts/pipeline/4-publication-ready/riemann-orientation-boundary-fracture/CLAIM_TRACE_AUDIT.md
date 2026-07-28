# Claim trace audit

Paper: `main.tex`

Policy: paper never mentions Lean. This internal audit maps every nonclassical mathematical claim
to an unconditional theorem surface. Novelty and significance are audited separately; formal
verification contributes neither.

## Main claim map

| Paper claim | Unconditional theorem surface | Status |
|---|---|---|
| Explicit even Schwartz theta source has Fourier transform `Xi`, and exponential tilt gives the completed xi line | `ThetaCuspFinitePrimeSource.thetaCuspSeed`; `ThetaCuspFinitePrimeSource.thetaCuspFullSource`; `ThetaCuspSchwartzFourierXi.fourier_xiThetaSchwartzSource`; `ThetaCuspFourierLaplace.fourier_thetaCuspTiltedSchwartz_scaled`; `HedenmalmLocalFrameObstruction.fourier_thetaCuspRightLineSource_scaled` | proved |
| Theta center-mixed Fourier current is the zero-safe unsquared derivative `2 |xi|² Re(xi'/xi)` | `ThetaCuspCenterMixedOrientationRankUniversalityLaw.thetaCuspCenterMixedFourierCurrent_eq_normSq_mul_logDeriv`; `..._div_normSq_eq_logDeriv` | proved |
| Actual tilted theta source is Schwartz and transforms to the shifted completed xi line | `ThetaCuspTiltedSchwartz`; `ThetaCuspFourierLaplace`; `HedenmalmLocalFrameObstruction.fourier_thetaCuspRightLineSource_scaled` | proved |
| Current nonnegative at all apertures above `alpha` iff all xi zeros obey the matching half-plane bound | `XiRealTransverseQuartetSurgeryMatroidInvariance.xiThetaNormalOrientationAbove_iff_zeroHalfPlaneBound` | proved |
| Same threshold equals exact projective reflection radius | `...xiThetaNormalOrientationAbove_iff_projectiveReflectionRadius_le` | proved |
| Complete Gaussian-windowed Hedenmalm Hankel tail cone iff the same zero half-plane bound | `HedenmalmGaussianHankelApertureWidthSpectrum.hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound` | proved |
| Hankel threshold is independent of positive Gaussian temperature | `...hedenmalmGaussianHankelTailCone_temperature_iff` | proved |
| No entire Hermitian diagonal multiplier at positive aperture | `XiFiniteLocalSpectralFrameObstruction.no_XiEntireHermitianDiagonalLaw_of_pos` | proved |
| Entire multiplier would propagate every xi zero under a positive real translation, without simplicity | `...xi_zero_shift_of_entireFluxCoboundary`; `...no_XiEntireFluxCoboundary_of_pos` | proved |
| No finite polynomial spectral Gram frame | `...not_XiFiniteLocalPolynomialSpectralFrame_of_pos` | proved |
| No finite constant-coefficient differential autocorrelation frame for actual Hedenmalm theta tangent | `HedenmalmLocalFrameObstruction.no_finitePolynomialAutocorrelationFrame_for_Hedenmalm_tangent` | proved |
| Universal cyclic-null collapse: an ambient-cyclic radical gives an ambient-null sequence of constant energy and forces nonclosability for every nonzero Hermitian form | `CyclicNullFormNonclosability.exists_ambientNull_constantEnergy_sequence_of_cyclic_null`; `...not_isSequentiallyClosableThrough_of_cyclic_null` | proved |
| Every nonnegative momentum-symmetric theta-null Schwartz form has a unique positive temperate Fourier measure supported on the real Xi divisor; the measure is atomic | `HedenmalmUniversalPositiveFormClassification.existsUnique_temperateSpectralRepresentation_supported_realDivisor_of_thetaNull`; `...universalPositiveForm_canonicalMeasure_atomic_of_thetaNull` | proved |
| Every nonzero form in that cone has dense proper nonclosed ordinary-`L²` radical and is nonclosable | `HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw` | proved |
| No nonzero form in that cone can have radical exactly the theta source line or induce a positive-definite form on the full algebraic theta-operator image | `...not_exists_nonzero_universalPositiveForm_thetaNull_exactSourceLineRadical` | proved |
| Real-shift prime sources have exact pointed-collision differential matroid | `XiRealTransverseShiftDefectDifferentialRank.xiRealTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision` | proved |
| Distinct nonzero physical apertures are differentially independent | `...xiPhysicalApertureUpperEndCarrier_differentialIndependent` | proved |
| Quartet gauge preserves FE, Schwarz symmetry, entire regularity, HT, and supplies an off-line factor | `CompactOpenKolchinWardChargeEscape` packaged escape laws and component theorems | proved |
| Canonical `B_n=n+1` quartet family converges compact-open through every holomorphic jet | `...escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly`; multiplicity version | proved |
| Every multiplicity has the same continuum real-aperture matroid | `XiRealTransverseQuartetSurgeryMatroidInvariance.multiplicityEscapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision` | proved |
| No matroid-to-natural classifier can recover quartet multiplicity | `...no_realApertureDifferentialMatroid_quartetMultiplicityClassifier` | proved |
| Unsquared Julia boundary phase defect is nonnegative at every nonnegative aperture | `XiWardInfinitesimalDefectIndexQuantization.xiWardBoundaryPhaseDefect_nonneg` | proved |
| Euler-edge derivative of the Julia phase defect is exactly the Ward density | `...hasDerivAt_xiWardBoundaryPhaseDefect_eulerEdge_zero` | proved |
| Ward density is nonnegative, has mass `8 pi`, and obeys bounded-window estimate | `HypertranscendentalQuartetWardIndex.quartetWardInfinitesimalDensity_nonneg`; `...lintegral_quartetWardInfinitesimalDensity`; `CompactOpenKolchinWardChargeEscape.quartetWardInfinitesimalDensity_window_bound` | proved |
| Multiplicity `N` mass is `N * 8 pi` and is injective in `N` | `CompactOpenKolchinWardChargeEscape.multiplicityEscapingQuartetWardMass_eq`; `XiRealTransverseQuartetSurgeryMatroidInvariance.multiplicityEscapingQuartetWardMass_injective` | proved |
| Fixed-multiplicity Ward density vanishes uniformly on every bounded window as height escapes | `CompactOpenKolchinWardChargeEscape.multiplicityEscapingQuartetWard_window_tendstoUniformly` | proved |
| Marked logarithmic source retains a simple pole; nonzero constant-coefficient differential operators detect it | `...multiplicityEscapingQuartetGauge_logDeriv_addedZero_simplePole`; `...nonzeroDifferentialOperator_detects_simplePole` | proved |
| Common marked mode has exact coefficient-sum/`A_(|I|-1)` kernel and cyclic image | `...commonModeDifferentialCombination_eq_zero_iff_sum_eq_zero`; `...range_commonModeDifferentialCombination_eq`; multiplicity capstone | proved |
| Combined width/local-global carrier/polarity/matroid/boundary fracture | `XiRealTransverseQuartetSurgeryMatroidInvariance.xiOrientationCarrier_fracture_universality`; constituent theorems above | proved |

## Wording corrections made during audit

1. Paper says gauge **contributes** multiplicity `N`; it does not claim total zero multiplicity of
   `G^N xi` is exactly `N`, because a pre-existing xi zero at the chosen point is not excluded.
2. Compact-open all-jet escape is stated for the proved canonical sequence `B_n=n+1`, not an
   unformalized continuous limit over arbitrary real `B`.
3. Common-mode augmentation law is stated for copies of the marked logarithmic mode. It is not
   overextended to arbitrary real-shift defects whose shifted poles could collide.
4. Paper does not claim actual Riemann Ward charge vanishes, actual zero exclusion, RH, or a no-go
   for all Hilbert--Pólya/de Branges/CCM constructions.
5. Paper does not claim compact-open FE perturbation itself is new.
6. Positive Julia orientation is called **defect-counting**, not zero-excluding. Unsquaring
   preserves orientation but does not determine the sign polarity needed for RH.
7. The source-core theorem is restricted to jointly Schwartz-continuous, nonnegative,
   momentum-symmetric extensions. Forms defined only on a finite zero-eigenfunction span remain
   outside its scope.

## Classical facts used

Definitions and elementary results used in paper proofs are also present in the dependency closure:
xi entire/FE/Schwarz symmetry, nontrivial-zero strip, isolated zeros, canonical product/logarithmic
derivative, Fourier autocorrelation, Lorentzian integral, and polynomial-gauge preservation of
hypertranscendence.

## Final audit gates

- [x] Direct foreground check of every new top-level module with `lake env lean <file>`.
- [x] Final foreground `lake build GaloisForLFunctions.RHTower` (13,591 jobs).
- [x] `#print axioms` scratch audit for paper capstones: only `propext`,
      `Classical.choice`, and `Quot.sound`.
- [x] Whole-repository formal lint gate. A dead duplicate
      `FiniteContractionPeripheralTransient` was reduced to a compatibility re-export of
      `DissipativeQuantumReturnInformationTransition`, allowing both it and
      `FiniteQuantumObserverGraphSharpness` to enter the umbrella without declaration collisions.
- [x] Confirm no stale `lean`/`lake` process.
- [x] PDF compile, text extraction, and all-page render inspection: 16 pages, no TeX warnings,
      no internal verification terminology.
