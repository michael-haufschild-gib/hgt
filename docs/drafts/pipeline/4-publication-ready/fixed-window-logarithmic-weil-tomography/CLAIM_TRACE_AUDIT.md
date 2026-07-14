# Claim trace audit

This file is internal verification metadata and is not part of the manuscript.
The manuscript may be promoted only while every substantive mathematical claim below remains
covered by the listed unconditional declaration.

## Window and divisor foundation

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| \(A_L(w)\neq0\) for \(L>0\), \(\Re w\neq0\) | rectangularWindowAmplitude_ne_zero |
| \(A_L(-w)=e^{Lw}A_L(w)\) | rectangularWindowAmplitude_neg |
| exact square/edge decomposition | rectangularTwoEdgeTransform_sq_decomposition |
| reciprocal-square strip majorant | norm_rectangularWindowAmplitude_le and xiRectangularTwoEdgeTransform_square_le |
| multiplicity-exact reciprocal-square summability | xiSpectralPoint_inv_sq_summable |
| FE and Schwarz symmetry preserve Xi zeros with analytic multiplicity | xi_orderAt_one_sub, xi_orderAt_conj, xiZeroCopyReflectEquiv, xiZeroCopyConjEquiv |
| full divisor polarization equals the square sum | xiWeilPolarization_rectangular_eq_tsum_sq |
| diagonal Xi-Weil values and the sampled rectangular coefficients are real | xiWeilPolarization_diagonal_im_eq_zero, xiRectangularWeilLogCoefficient_im_eq_zero |
| exact dominant/remainder split | xiWeilPolarization_rectangular_sub_dominant_eq_tsum_remainder |
| uniform remainder bound | norm_xiWeilPolarization_rectangular_sub_dominant_le |

## Dirichlet continuation and multiplicity

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| right coefficients are summable and nonzero | xiRectangularRightCoefficient_summable, xiRectangularRightCoefficient_ne_zero |
| logarithmic samples are exact \(n^w\) monomials | xiRectangularTwoEdgeDominant_logSample_of_right |
| L-series equals twice the shifted-zeta carrier on the initial half-plane | LSeries_xiRectangularRightDirichletComplex_eq_shiftedZeta |
| reciprocal-\(3/2\) Xi divisor summability | xiSpectralPoint_inv_three_halves_summable |
| vertical square-root zeta bound | norm_riemannZeta_le_sqrt_norm_add_two |
| holomorphic shifted-zeta neighborhood at the actual real transverse boundary | exists_analyticOnNhd_xiRectangularShiftedZetaSeries_actualLandauBall |
| eventual lower boundedness forces tail summability strictly left of that boundary | exists_xiRectangularLandauCoefficient_summable_left_of_boundary |
| local normal convergence of the cancelled carrier on \(\Re s>1\) | summableLocallyUniformlyOn_xiRectangularCancelledTerm_rightOne |
| numerator order \(m-1\) at every shifted Xi zero | xiRectangularCancelledSeries_order |
| denominator order \(m\) | xi_shifted_half_order |
| base continuation is meromorphic on \(\Re s>1\) | meromorphicOn_xiRectangularRightDirichletContinuation_rightOne |
| its simple poles are exactly the shifted right Xi support | meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one_iff |
| its pole residue at a zero of multiplicity \(m\) is \(mA_L(w)^2\) | meromorphicTrailingCoeffAt_xiRectangularRightDirichletContinuation |
| ordinary coefficient L-series equals twice the continuation initially | LSeries_xiRectangularRightDirichletComplex_eq_continuation |
| summability of a constant-shifted finite-deletion tail bounds every shifted pole | xiRightShiftedPole_re_le_of_landau_summable |

## Completeness and quantitative laws

The full four-way equivalence and false-RH divergence statement are bundled by
fixedWindowLogarithmicWeilCompleteness_capstone.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| false RH forces cofinal negative divergence of actual sampled Weil values | xiWeilPolarization_rectangular_logSample_cofinally_unbounded_below |
| RH iff sampled values are nonnegative | riemannHypothesis_iff_rectangular_logSample_weil_nonneg |
| RH iff sampled values are eventually bounded below | riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow |
| RH iff sampled norms are bounded | riemannHypothesis_iff_rectangular_logSample_weil_norm_bdd |
| sharp power exponent is the supremal transverse displacement | xiRightTransverseSup_is_sharp_rectangular_power_exponent |
| under RH the fixed-width family is uniformly bounded | norm_xiWeilPolarization_rectangular_le_of_riemannHypothesis |
| an eventual lower budget of exponent \(\alpha\) exists iff the transverse supremum is at most \(\alpha\) | xiRectangularWeilTailPowerLower_iff_transverseSup_le_global |
| the lower budget is equivalent to the zero-free half-plane \(\Re\rho\le1/2+\alpha\) | xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le, xiRectangularWeilTailPowerLower_iff_xi_zeroFree_right_halfPlane |
| the complete one-sided exponent spectrum is exactly \([\delta_*,\infty)\) | xiRectangularOneSidedExponentSet_eq_Ici_transverseSup |
| fixed-abscissa negative energy of the actual observable transports through the finite prefix and bounded remainder | xiRectangularRightNegativePart_LSeriesSummable_at_one_add_of_tailNegativePart_summable |
| negative energy at the single abscissa \(1+\alpha\) bounds every Xi zero by \(\Re\rho\le1/2+\alpha\) | xi_zero_re_le_half_add_of_xiRectangularWeilTailNegativePart_summable |
| \(\delta_*\le\alpha\) iff the actual negative-mass series converges at every abscissa \(1+\alpha+\varepsilon\) | xiRightTransverseSup_le_iff_negativePartEnergyAbove |
| one real point of negative-mass convergence bounds \(\delta_*\) by that abscissa minus one | xiRightTransverseSup_le_sub_one_of_negativePart_summable |
| the negative-mass series converges above \(1+\delta_*\) and diverges strictly between \(1\) and \(1+\delta_*\) | xiRectangularNegativePart_summable_above_transverseSup, not_xiRectangularNegativePart_summable_below_transverseSup |
| under false RH the negative-mass absolute-convergence abscissa is exactly \(1+\delta_*\) | xiRectangularNegativePart_abscissa_eq_transverseSup_of_not_rh |
| under RH the negative carrier vanishes and its abscissa is \(-\infty\) | xiRectangularNegativePart_abscissa_eq_bot_of_rh |
| unconditional RH/false-RH abscissa dichotomy | xiRectangularNegativePart_abscissa_dichotomy |
| the negative-mass abscissa is independent of positive window width and admissible prefix | xiRectangularNegativePart_abscissa_independent_of_window_tail |
| at every real abscissa an exact positive split is summable iff both channels are summable | negativeChannelSplit_summable_iff |
| every exact positive split conserves the total abscissa as the maximum channel abscissa | negativeChannelSplit_abscissa_eq_max |
| maximum positive-channel abscissa is independent of window, cutoff, and exact allocation | negativeChannelSplit_max_abscissa_independent |
| every finite positive cover contains a channel whose abscissa is at least the carrier abscissa | finiteNegativeChannelCover_forces_full_abscissa |
| under false RH every finite positive cover has a channel of abscissa at least $1+\delta_*$ | finiteNegativeChannelCover_forces_transverseSup_of_not_rh |
| every finite positive exact split has a channel attaining the carrier abscissa | finiteNegativeChannelSplit_attains_full_abscissa |
| under false RH every finite positive exact split has a channel of abscissa exactly $1+\delta_*$ | finiteNegativeChannelSplit_attains_transverseSup_of_not_rh |
| channel abscissae at most $1+\alpha$ in one finite positive cover force $\delta_*\le\alpha$ | xiRightTransverseSup_le_of_finiteNegativeChannelCover_abscissa |
| channel abscissae at most one in one finite positive cover prove RH | riemannHypothesis_of_finiteNegativeChannelCover_abscissa_le_one |
| \(\delta_*\le\alpha\) iff there exists any positive shifted-energy majorant of the actual negative mass | xiRightTransverseSup_le_iff_exists_negativeEnergyMajorantAbove |
| \(\delta_*\le\alpha\) iff there exists a positive two-channel energy cover, without exact splitting | xiRightTransverseSup_le_iff_exists_twoChannelEnergyCoverAbove |
| for every exact nonnegative split and every \(\alpha\ge0\), shifted energy plus residual order \(\alpha\) is equivalent to \(\delta_*\le\alpha\) | xiRightTransverseSup_le_iff_negativeChannelSpectrum |
| the positive-channel spectrum is equivalent to the full zero-free half-plane \(\Re\rho\le1/2+\alpha\) | all_xiZeros_re_le_iff_negativeChannelSpectrum |
| the zero member of the positive-channel spectrum is exactly RH | riemannHypothesis_iff_negativeChannelSpectrum_zero |
| every exact nonnegative split gives the endpoint energy/subpower RH equivalence | riemannHypothesis_iff_negativeChannelEnergy_and_subpowerChannel |
| false RH forces every positive split to fail in its residual or energy channel | negativeChannelDichotomy_of_not_riemannHypothesis |
| every fractional selector gives an exact continuous positive allocation | riemannHypothesis_iff_fractionalNegativeEnergy_and_complementarySubpower |
| for every exceptional set, RH is equivalent to finite Dirichlet energy of its actual carried negative mass plus off-set subpower lower control | riemannHypothesis_iff_exceptionalNegativeEnergy_and_subpowerLowerOff |
| under false RH every exceptional set exposes complementary non-subpower loss or divergent carried negative energy | exceptionalCarrierDichotomy_of_not_riemannHypothesis |
| the complete observable has an unconditional square-root envelope | norm_xiRectangularWeilLogCoefficient_le_halfPower |
| a global \(n^\beta\) budget plus \(\beta\)-thin exceptional support and off-support subpower lower control forces RH | riemannHypothesis_of_xiRectangularWeilSubpowerLowerOff_of_powerEnergy |
| at the exact sharp exponent \(\delta_*\), transverse-thin sparse control is equivalent to RH | riemannHypothesis_iff_xiRectangularWeilSubpowerLowerOff_transverse |
| under false RH every exceptional carrier of all non-subpower negative excursions is thick at the exact transverse exponent | exists_transverseExceptionalEnergy_divergence_of_not_riemannHypothesis |
| the divisor-independent half-power specialization and its false-RH thickness law | riemannHypothesis_iff_xiRectangularWeilSubpowerLowerOff, exists_halfPowerExceptionalEnergy_divergence_of_not_riemannHypothesis |

## Cutoff-free full-sequence tomography

The strengthened principal theorem is bundled by
fixedWindowFullObservableDivisorTomography_capstone.  It concerns the complete coefficient
sequence and has no cutoff parameter.  Width-independence of the normalized divisor is bundled by
fixedWindowFullObservableDivisorUniversality_capstone.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| an admissible proof cutoff exists for every width | exists_xiRectangularAdmissibleCutoff |
| the global observable remainder is a bounded tail remainder plus a finite prefix | xiRectangularWeilFullRemainderCoefficient_eq_tail_add_prefix |
| global remainder L-series converges absolutely on \(\Re s>1\) | xiRectangularWeilFullRemainderCoefficient_LSeriesSummable |
| global remainder L-series is analytic on \(\Re s>1\) | analyticAt_LSeries_xiRectangularWeilFullRemainderCoefficient |
| the complete observable L-series equals the cutoff-free continuation initially | LSeries_xiRectangularWeilLogCoefficient_eq_fullContinuation |
| cutoff-free continuation is meromorphic throughout \(\Re s>1\) | meromorphicOn_xiRectangularWeilFullContinuation_rightOne |
| its simple poles are exactly the shifted right Xi zeros | meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one_iff |
| its pole residue is \(2mA_L(w)^2\) | meromorphicTrailingCoeffAt_xiRectangularWeilFullContinuation |
| normalized residue recovers the exact analytic multiplicity | normalizedFullObservableResidue_eq_xiRightMultiplicity |
| normalized pole weights are independent of width and multiplicity-copy choice | normalizedFullObservableResidue_intrinsic |
| RH iff the cutoff-free full continuation is analytic throughout \(\Re s>1\) | riemannHypothesis_iff_fullObservableContinuation_analytic_rightOne |

## Screw coordinate

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| screw divisor series is absolutely summable | xiScrewDivisorTerm_summable |
| screw profile is real | star_xiScrewDivisor |
| exact fixed-width second-difference identity | xiWeilPolarization_rectangular_eq_screwCurvature |
| screw nonnegativity and eventual-lower-bound RH criteria | riemannHypothesis_iff_xiScrewWindowCurvature_logSample_nonneg, riemannHypothesis_iff_xiScrewWindowCurvature_logSample_eventually_bddBelow |

## Complete sharp rectangular Guinand--Weil formula

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the finite symmetric contour equals the multiplicity-counted Xi divisor sum | rectIntegral_rectangularLogDeriv_symmetric_eq_xiZeroCopy_sum |
| symmetric finite divisor rectangles exhaust the complete sharp polarization | tendsto_symmetric_xiZeroCopy_rectangular_sum_atTop |
| the truncated bottom edge tends to the absolutely convergent complete bottom contribution | tendsto_normalizedRectangularTruncatedBottomXiContribution_atTop |
| vertical resolvent edges become arbitrarily small along an admissible cofinal sequence | exists_large_integral_rectangular_mul_logDeriv_XiC_norm_lt |
| the complete sharp divisor polarization equals the literal bottom-edge integral | xiWeilPolarization_rectangular_eq_normalizedBottomXiContribution |
| the exact sharp value is the finite von Mangoldt autocorrelation plus the archimedean integral | xiWeilPolarization_rectangular_eq_prime_add_arch |
| after the explicit Gamma and polar correction, the full spectral value is the finite prime--polar source | rectangularCorrectedXiWeilValue_eq_primePolarSource |
| the arithmetic-aperture autocorrelation splits into a fixed tent and one moving multiplicative window | rectangularPrimeAutocorrelationSum_logAperture |

## Exact sharp prime--Gamma RH spectrum

The source-only headline theorem is formalized in
`CCMPrimeGammaSourceEnergySpectrum.lean`.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the arithmetic sample (g_L(n)) is a finite von Mangoldt autocorrelation plus the completed Gamma integral | xiRectangularPrimeGammaLogCoefficient |
| on every admissible sample, (g_L(n)=Q_L(\frac12\log n)) | xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re |
| the complete prime--Gamma tail is pointwise the real sharp Weil tail | xiRectangularPrimeGammaTailCoefficient_eq_weilTail_re |
| its negative mass is pointwise the intrinsic fixed-window negative carrier | xiRectangularPrimeGammaTailNegativePart_eq_weilTailNegativePart |
| RH iff every retained prime--Gamma sample is nonnegative | riemannHypothesis_iff_primeGammaLogCoefficient_tail_nonneg |
| the Xi half-plane at width `alpha` iff the prime--Gamma negative tail has energy above `1+alpha` | xiZeroHalfPlaneBound_iff_primeGammaTailNegativeEnergyAbove |
| the explicit prime--Gamma source, inverse-tilted source, critical-Mellin defect, and Xi half-plane form one quantitative spectrum | ccmPrimeGammaSourceDivisorEnergySpectrum_capstone |
| the `alpha=0` endpoint of the explicit spectrum is RH | riemannHypothesis_iff_ccmPrimeGammaSourceDivisorEnergyEndpoint |
| the source negative abscissa is `-infinity` under RH and `1+delta_*` under false RH | xiRectangularPrimeGammaTailNegativePart_abscissa_dichotomy |
| RH iff the source negative abscissa is `-infinity` | riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_eq_bot |
| RH iff the source negative abscissa is at most one | riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one |

## Source-defined complete Xi-divisor carrier

The complete prime-source theorem is bundled by
`inverseTiltedDyadicPrimeFullDivisorTomography_capstone`.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the inverse-tilted dyadic Mellin factor is \(A_{\log 2}(s)\) | inverseTiltedDyadicMellin_eq_rectangularAmplitude |
| this factor is nonzero throughout \(\Re s>0\) | inverseTiltedDyadicMellin_ne_zero_of_re_pos |
| the inverse-tilted quadrature remainder converges locally uniformly and is analytic on \(\Re s>1/2\) | summableLocallyUniformlyOn_inverseTiltedDyadicErrorSummand, differentiableOn_inverseTiltedDyadicErrorSeries_rightHalf |
| the displayed real finite-prime coefficient has the canonical ordinary Dirichlet series initially | LSeries_inverseTiltedDyadicRealSourceCoefficient_eq_continuedSource |
| the canonical source is meromorphic throughout \(\Re s>1/2\) | meromorphicOn_inverseTiltedDyadicContinuedSource_rightHalf |
| every nontrivial Xi zero produces a genuine simple pole | meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one |
| every simple source pole in \(\Re s>1/2\) comes from a unique shifted Xi zero | meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one_iff, inverseTiltedXiPole_injective |
| the complete Xi support is canonically equivalent to the source simple-pole support | inverseTiltedXiDivisorEquivSimplePoleSupport |
| normalized Laurent coefficients recover exact analytic multiplicity | normalizedInverseTiltedDyadicResidue_eq_multiplicity |
| RH iff every source pole lies on \(\Re s=1\) | riemannHypothesis_iff_inverseTiltedDyadic_poles_on_line |
| RH iff the source is analytic throughout \(\Re s>1\) | riemannHypothesis_iff_inverseTiltedDyadic_analytic_rightOne |

## Exact critical-Mellin identification

The direct Connes-source bridge is bundled by
`inverseTiltedCriticalMellinFactorization_capstone`.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the pole-filled defect agrees with the polar--prime critical-Mellin Laplace channel on \(\Re u>0\) | regularizedCriticalMellinDefect_eq_continued, criticalMellinDefectLaplaceChannelComplex_eq_continued |
| the inverse-tilted source is exactly a translated critical-Mellin defect times its Mellin aperture plus the explicit correction | inverseTiltedDyadicContinuedSource_eq_criticalMellinDefect_add_correction |
| the correction is analytic throughout \(\Re s>1/2\) | analyticAt_inverseTiltedCriticalMellinCorrection |
| source holomorphy on \(\Re s>1\) iff defect holomorphy on \(\Re u>-1/2\) | inverseTilted_source_analytic_rightOne_iff_regularizedCriticalMellin_analytic_rightNegHalf |
| RH iff the regularized critical-Mellin defect is analytic throughout \(\Re u>-1/2\) | riemannHypothesis_iff_regularizedCriticalMellinDefect_analytic_rightNegHalf |

## Principal quantitative source--divisor--energy spectrum

The quantitative equivalence is bundled by
`ccmQuantitativeSourceDivisorEnergySpectrum_capstone`; its RH endpoint is bundled by
`riemannHypothesis_iff_ccmSourceDivisorEnergyEndpoint`.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the Xi half-plane bound at width `alpha` is equivalent to inverse-tilted source holomorphy on `Re s > 1+alpha` | xiZeroHalfPlaneBound_iff_inverseTiltedDyadicSourceAnalyticAbove |
| the same Xi bound is equivalent to critical-Mellin holomorphy on `Re u > alpha-1/2` | xiZeroHalfPlaneBound_iff_criticalMellinDefectAnalyticAbove |
| the same Xi bound is equivalent to fixed-window negative energy above `1+alpha` | xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove |
| the four quantitative coordinates form one exact spectrum | ccmQuantitativeSourceDivisorEnergySpectrum_capstone |
| the `alpha=0` endpoint is exactly RH | riemannHypothesis_iff_ccmSourceDivisorEnergyEndpoint |
| every pointwise-summable positive covering aggregate has abscissa at least the carrier abscissa | summableNegativeChannelCover_aggregate_forces_full_abscissa |
| under false RH every such aggregate has abscissa at least `1+delta_*` | summableNegativeChannelCover_aggregate_forces_transverseSup_of_not_rh |
| aggregate abscissa at most `1+alpha` forces the matching Xi zero-free half-plane | xiZeroHalfPlaneBound_of_summableNegativeChannelCover_aggregate_abscissa |
| aggregate abscissa at most one proves RH | riemannHypothesis_of_summableNegativeChannelCover_aggregate_abscissa_le_one |

## Strengthened source laws

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| false RH forces cofinal power-scale excursions of both signs | not_riemannHypothesis_implies_rectangular_weil_twoSided_power_oscillation |
| the Gamma--polar correction converges to an explicit limit at exponential aperture rate | abs_rectangularGammaPolarCorrection_sub_limit_le_exp |
| the arithmetic logarithmic sample has explicit inverse-square-root error | abs_rectangularGammaPolarCorrection_logSample_sub_limit_le_inv_sqrt |
| the elementary coefficient \((\Lambda(n)-1)\sqrt n\) has the stated zeta-logarithmic-derivative Dirichlet series | LSeries_simplePrimeDivisorSourceCoefficient_eq_zetaLogDeriv |
| its continued source has a removable pole at \(3/2\) | analyticAt_simplePrimeDivisorContinuedSource_three_halves |
| every shifted Xi zero gives a simple pole with exact multiplicity residue | meromorphicOrderAt_simplePrimeDivisorContinuedSource_eq_neg_one, tendsto_simplePrimeDivisorContinuedSource_residue |
| holomorphy of the elementary source on \(\Re s>1\) is equivalent to RH | riemannHypothesis_iff_simplePrimeDivisorContinuedSource_analyticOn_rightOne |
| the all-epsilon sharp dyadic estimate is equivalent to its restriction to perfect squares | eventually_dyadicWeightedPrimeWindow_upper_iff_squareSamples |
| the perfect-square sharp dyadic estimate proves RH | riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_square_upper |

## Contractive endpoint reflection law

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the completed endpoint curvature is \(2+\gamma-\log(4\pi)\) | xiEndpointCompletedCurvature_eq_eulerMascheroni_log |
| the completed endpoint curvature lies strictly between zero and one half | xiEndpointCompletedCurvature_pos, xiEndpointCompletedCurvature_lt_one_half |
| the exact endpoint polarization identity is \(E=2(H-C)\) | xiEndpointReflectionDefectEnergy_eq_mass_sub_source |
| the reflection defect satisfies \(E\le C^2/(1-C)<C\) | xiEndpointDefectEnergy_le_unconditional_source_factor, xiEndpointReflectionDefectEnergy_lt_endpointCurvature |
| the raw Hermitian mass satisfies \(C\le H<3C/2<3/4\) | xiEndpointCompletedCurvature_le_rawMass, xiRawReciprocalHermitianMass_lt_three_halves_mul_endpointCurvature, xiRawReciprocalHermitianMass_lt_three_fourths |
| every reciprocal coordinate lies in the uniform disk of radius \(9/10\) | xiRawReciprocalCoordinate_norm_lt_nine_tenths |
| critical-line reflection is the exact Mobius transform of the conjugate reciprocal coordinate | xiRawReciprocalCoordinate_lineConj_eq_mobius |
| the reflected coordinate is its pointwise convergent Neumann series | hasSum_xiRawReciprocalCoordinate_lineConj_neumann |
| the endpoint cross trace is the absolutely convergent all-order holomorphic power-trace series | summable_xiRawReciprocalNeumann_double, hasSum_xiEndpointCrossTrace_allOrder |
| the all-order trace sum equals the completed Xi logarithmic derivative | xiEndpointCrossTrace_eq_completedLogDeriv, hasSum_completedEndpointLogDeriv_holomorphicTraces |
| the real all-order trace sum equals the completed endpoint curvature | hasSum_xiEndpointCompletedCurvature_holomorphicTraces |
| the normalized prime--Gamma source germ is the reciprocal-square resolvent and has the stated moments | normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm, primeArchSourceMoment_eq_xiCentralReciprocalMoment |
| endpoint saturation \(H=C\) is equivalent to RH | primeArchEndpointSaturation_iff_riemannHypothesis |
| complete integer-polynomial source Hankel positivity is equivalent to RH | primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis |
| a reflection-positive Gram realization of the normalized moments is equivalent to RH | primeArchComplexReflectionPositiveGram_iff_riemannHypothesis |
| a bounded self-adjoint vacuum realization of the normalized moments is equivalent to RH | primeArchSelfAdjointVacuumRealization_iff_riemannHypothesis |
| the complete unconditional and sharp endpoint package is bundled in one theorem | primeArchConnesReflectionMain |

## Explicit dyadic source endpoints

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| Dirichlet energy of the positive dyadic von Mangoldt-window excess at every abscissa `1+epsilon` proves RH | riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessEnergy |
| the proper-prime-power channel is nonnegative and bounded by an explicit logarithmic cost | dyadicWeightedHigherPrimePowerWindow_nonneg, dyadicWeightedHigherPrimePowerWindow_le_log |
| the all-epsilon source estimate is equivalent after removing every proper prime power | dyadicWeightedPrimeWindowSubpowerUpper_iff_primeOnly |
| the displayed prime-only estimate proves RH | riemannHypothesis_of_eventually_dyadicWeightedPrimeOnlyWindow_upper |

## Optimal positive correction of the signed sharp-prime source

The source-facing optimization theorem is bundled by
`dyadicSharpPrimePositiveCorrectionAbscissaSpectrum_capstone`.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the negative part of the signed sharp-prime source is an admissible positive correction | dyadicSharpPrimeSourceNegativePart_isPositiveCorrection |
| the canonical correction equals twice the positive dyadic-window excess | dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess |
| every admissible positive correction dominates the canonical correction pointwise | dyadicSharpPrimeSourceNegativePart_le_of_positiveCorrection |
| the canonical correction has no larger absolute-convergence abscissa than any admissible correction | dyadicSharpPrimeSourceNegativePart_abscissa_le_of_positiveCorrection |
| at every extended-real threshold, an admissible correction exists below that threshold iff the canonical correction does | exists_dyadicSharpPositiveCorrection_abscissa_le_iff |
| the canonical correction has unconditional absolute-convergence abscissa at most `3/2` | dyadicSharpPrimeSourceNegativePart_abscissa_le_three_halves |
| the admissible correction spectrum is therefore nonempty at `3/2` | exists_dyadicSharpPositiveCorrection_abscissa_le_three_halves |
| existence of any all-epsilon correction-energy carrier is equivalent to energy of the canonical correction | exists_dyadicSharpPositiveCorrectionEnergy_iff_negativePartEnergy |
| an admissible correction of abscissa at most `1+alpha` forces the Xi zero-free half-plane `Re rho <= 1/2+alpha` | xiZeroHalfPlaneBound_of_dyadicSharpPositiveCorrection_abscissa |
| an admissible correction of abscissa at most one proves RH | riemannHypothesis_of_dyadicSharpPositiveCorrection_abscissa_le_one |
| under false RH every admissible correction fails summability at each `1+alpha` below the actual transverse exponent | not_dyadicSharpPositiveCorrection_summable_below_transverseSup_of_not_rh |
| under false RH the canonical correction abscissa is bounded below by `1+xiRightTransverseSup` | transverseSup_le_dyadicSharpPrimeSourceNegativePart_abscissa_of_not_rh |
| under false RH the canonical correction abscissa lies in the sharp unconditional interval from `1+xiRightTransverseSup` to `3/2` | dyadicSharpPrimeSourceNegativePart_abscissa_interval_of_not_rh |

## Complete critical-Mellin divisor tomography

The stronger intrinsic theorem is bundled by
`criticalMellinDivisorTomography_capstone`.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the regularized critical-Mellin defect is meromorphic on \(\Re u>-1\) | meromorphicOn_regularizedCriticalMellinDefect_rightNegOne |
| pointwise holomorphy is equivalent to \(Z_*(u+1)\ne0\) | analyticAt_regularizedCriticalMellinDefect_iff_regularizedZeta_ne_zero |
| every simple pole is uniquely \(u=\rho-1\) for a nontrivial Xi zero | meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one_iff, criticalMellinXiPole_injective |
| the critical-Mellin pole residue is the exact analytic multiplicity | meromorphicTrailingCoeffAt_regularizedCriticalMellinDefect |
| the complete Xi divisor is canonically equivalent to the critical-Mellin simple-pole support | criticalMellinXiDivisorEquivSimplePoleSupport |
| RH iff every critical-Mellin pole lies on \(\Re u=-1/2\) | riemannHypothesis_iff_criticalMellin_poles_on_line |
| RH iff the defect is analytic throughout \(\Re u>-1/2\) | riemannHypothesis_iff_regularizedCriticalMellinDefect_analytic_rightNegHalf |

## Exact quartet source--temperature ultraviolet--infrared spectrum

The quantitative endpoint, thermal, response, and cold-limit clauses are bundled by
`primeArchExactQuartetConnesBornWittenKMSMaster`; the certified-radius specialization is bundled
by `primeArchExactQuartetConnesBornWittenKMSMaster_twoHundredEighteen_twentyFifths`.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| the endpoint curvature satisfies \(C<93/2000\) | xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand |
| the off-line endpoint charge is nonnegative and bounded by \(C\) | xiEndpointOffLineCharge_nonneg, xiEndpointOffLineCharge_le_curvature |
| every off-line quartet is paid inside the off-line sector: \(4c_\rho\le C_\perp\) and \(4\le C_\perp(\gamma^2+1)\) | four_mul_xiEndpointCrossCharge_le_offLineCharge, four_le_offLineCharge_mul_one_add_im_sq |
| every off-line quartet satisfies \(4\le C(\gamma^2+1)\) and \(\gamma^2>7907/93\) | four_le_endpointCurvature_mul_one_add_im_sq_of_offLine, xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq |
| every exact quartet-admissible central band is zero-free and the continued response is anti-Herglotz there | XiC_ne_zero_of_upperHalf_exactOffLineQuartetBand, continuedPrimeArchSourceRelativeTrace_im_nonpos_exactOffLineQuartetBand |
| the relative transverse factor is \(\kappa_4(C)<1/84\) | xiThermalQuartetRelativeOrientationFactor_lt_one_eightyFourth |
| the exact source gap is the nonnegative transverse orientation energy | xiThermalSecondMoment_sub_source_eq_orientationEnergy, xiThermalOrientationEnergy_nonneg |
| every transverse atom is cubically controlled by its exact endpoint cross charge | xiThermalOrientationTerm_le_exactEndpointCrossCharge_cube |
| the endpoint cross charges sum exactly to the completed curvature | tsum_xiEndpointCrossCharge_eq_curvature |
| the absolute thermal defect satisfies \(\mathcal E_\perp\le4(C/(4-C))^3\) | xiThermalOrientationEnergy_le_exactCubicEndpointBudget |
| the defect self-localizes as \(\mathcal E_\perp\le4(C_\perp/(4-C_\perp))^3\le4(C/(4-C))^3\) | xiThermalOrientationEnergy_le_offLineChargeCubicBudget, xiThermalOffLineChargeCubicBudget_le_exactCubicEndpointBudget |
| \(C_\perp=0\), the self-cubic budget zero, the thermal energy zero, and RH have the same zero locus | xiThermal_offLineCharge_budget_energy_zero_tfae |
| the exact cubic budget is strictly below the rational majorant \((86/85)^3C^3/16\) | xiThermalExactCubicEndpointBudget_lt_cubicEndpointBudget |
| the thermal/source gap is nonnegative and below \(1/150000\) | xiThermalSecondMoment_source_absoluteGap |
| the zeroth finite KMS coordinate converges unconditionally to the zeroth source moment | tendsto_xiThermalTruncation_zero_source |
| the transverse energy is bounded by the projective displacement and cubic reciprocal mass | xiThermalSourceGap_le_intrinsicTransverseCubicBudget |
| false RH forces the stated square-sampled prime-energy abscissa lower bounds | one_add_sqrt_normalized_xiThermalSourceGap_le_squarePrimeWindowPositiveExcess_abscissa, one_add_two_mul_sqrt_normalized_xiThermalSourceGap_le_squarePrimeWindowPositiveExcessSquare_abscissa |
| the faithful cold partition has exponential type equal to the horizontal divisor radius | xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveColdPartition_le |
| one bound uniform in the cold parameter and all sufficiently large finite systems is equivalent to RH | riemannHypothesis_iff_exists_eventually_cold_eventually_thermodynamic_bound |
| false RH is equivalent to divergence of every cofinal finite-system cooling section, in particular \(Z_{J,J}\to+\infty\) | thermalProjectiveCofinalSection_tendsto_atTop_iff_not_riemannHypothesis |
| RH is equivalent to one fixed diagonal upper bound recurring cofinally often | riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveDiagonal |
| RH is equivalent to local finite-block approximation of the source by finite positive atomic or finite KMS/Wightman moment systems | primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis, primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis |
| high-frequency passivity above any quartet-admissible radius is equivalent to RH | continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_exactOffLineQuartetBand |
| the universal one-state zero-Hamiltonian KMS palette has imaginary response cluster set exactly \(( -\infty,0]\) at every upper-half-plane point | closure_range_universalOneStateKMSPassiveResponse_im |
| countable Gaussian-rational source membership in that palette is exactly the positive-frequency response condition above the same radius | primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_positiveFrequency |
| at every quartet-admissible radius, that countable passive membership condition is equivalent to RH | primeArchGaussianRatFiniteKMSPassiveClosureAbove_iff_riemannHypothesis |

## Cofinal endpoint-calibrated source--temperature master law

The headline synthesis is bundled by `primeArchCofinalSourceTemperatureMaster`; its
scale-resolved free-energy and source-abscissa statement is bundled by
`primeArchCofinalSourceTemperatureSpectrum`.

| Manuscript claim | Unconditional Lean declaration |
|---|---|
| every endpoint-calibrated Hausdorff difference is the real reciprocal-square Xi-divisor polynomial value | scaledHausdorffMomentDifference_eq_re_xiCentralSum |
| every individual divisor atom is nonnegative for `k <= 13`, `r <= 43` | re_xiCentral_scaledBasis_rectangle_nonneg |
| the complete `14 x 44` southwest rectangle is nonnegative | scaledPrimeArchEndpointHausdorffDifference_rectangle_nonnegative |
| the discharged rectangle contains exactly 616 indexed conditions | primeArchEndpointHausdorffRectangle_cardinality |
| positivity on one common deep calibrated Hausdorff quadrant is equivalent to RH | cofinalScaledPrimeArchHausdorffQuadrantNonnegative_iff_riemannHypothesis |
| the critical prime--polar abscissa endpoint is equivalent to that deep quadrant | rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalHausdorffQuadrant |
| arbitrarily large nonnegative complete calibrated Hausdorff diagonals are equivalent to RH | cofinalScaledPrimeArchHausdorffDiagonalsNonnegative_iff_riemannHypothesis |
| cofinal vanishing of the aggregate negative Bernstein mass is equivalent to RH | cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis |
| the critical prime--polar abscissa endpoint is equivalent to cofinal aggregate negative-mass vanishing | rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalBernsteinNegativeMassVanishing |
| positive-part Bernstein approximation differs from the signed approximation by at most the aggregate negative mass in every coordinate | hausdorffBernsteinPositiveAtomicMoment_sub_signed_nonneg, hausdorffBernsteinPositiveAtomicMoment_sub_signed_le_negativeMass |
| for every cofinal finite-volume/cooling schedule, the normalized logarithmic partition converges to the projective reflection radius | tendsto_xiThermalProjectiveColdTruncation_log_div_cold |
| RH is equivalent to zero cofinal free-energy density | riemannHypothesis_iff_tendsto_thermalProjectiveCofinalFreeEnergy_zero |
| RH is equivalent to subexponential growth along every, equivalently one, cofinal thermal schedule | riemannHypothesis_iff_thermalProjectiveCofinalSubexponential |
| positivity on monic integer polynomials Eisenstein at `2` in any infinite exact-degree set is equivalent to RH | primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis |
| every positive-degree polynomial in the fixed Eisenstein chamber is irreducible | irreducible_of_monic_primeArchTwoEisenstein |
| the source endpoint, sparse irreducible chamber, cofinal diagonals, aggregate negative-mass vanishing, deep quadrant, zero free energy, subexponential growth, finite KMS closure, Connes reflection positivity, and RH form one chain | primeArchCofinalSourceTemperatureMaster |

## Axiom and lint gate

- Exact build targets: GaloisForLFunctions.RHTower.CCMUnconditionalFoundation,
  GaloisForLFunctions.RHTower.CCMRectangularOneSidedTransverseExponent, and
  GaloisForLFunctions.RHTower.CCMRectangularSparseExceptionCompleteness,
  GaloisForLFunctions.RHTower.CCMRectangularNegativeChannelSplitCompleteness, and
  GaloisForLFunctions.RHTower.CCMRectangularNegativeChannelSpectrum, and
  GaloisForLFunctions.RHTower.CCMRectangularNegativeDirichletAbscissa, and
  GaloisForLFunctions.RHTower.CCMRectangularFiniteChannelNonDilution, and
  GaloisForLFunctions.RHTower.CCMSourceDivisorEnergySpectrum, and
  GaloisForLFunctions.RHTower.CCMPrimeGammaSourceEnergySpectrum, and
  GaloisForLFunctions.RHTower.CCMSharpPrimeWindowMinimalPositiveCorrection, and
  GaloisForLFunctions.RHTower.CCMInverseTiltedDyadicPrimeTomography, and
  GaloisForLFunctions.RHTower.CCMInverseTiltedCriticalMellinFactorization, and
  GaloisForLFunctions.RHTower.CCMCriticalMellinDivisorTomography, and
  GaloisForLFunctions.RHTower.XiThermalQuartetCubicChargeBound, and
  GaloisForLFunctions.RHTower.XiThermalOffLineChargeSelfCubicBound, and
  GaloisForLFunctions.RHTower.XiThermalProjectiveCofinalSection, and
  GaloisForLFunctions.RHTower.PrimeArchFiniteKMSLocalMomentClosure, and
  GaloisForLFunctions.HTGeometry.FiniteKMSPassivePalette, and
  GaloisForLFunctions.RHTower.PrimeArchCountablePassiveResponseEquivalence, and
  GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetKMSMaster, and
  GaloisForLFunctions.RHTower.PrimeArchEndpointHausdorffTemperatureMaster, and
  GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffQuadrantRH, and
  GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffDiagonalRH, and
  GaloisForLFunctions.RHTower.XiThermalProjectiveFreeEnergyRadius, and
  GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail, and
  GaloisForLFunctions.RHTower.PrimeArchCofinalSourceTemperatureMaster.
- Allowed foundational dependencies in the checked capstones:
  [propext, Classical.choice, Quot.sound].
- Repository lint must report no active sorry, admit, axiom, opaque, or unsafe declaration.
