# Internal claim trace audit

This file is not part of manuscript. Formal verification is used only as truth
control. It contributes nothing to novelty or significance.

Audit date: 2026-07-31.

## Scope policy

- Every mathematical assertion in `main.tex` must be an unconditional
  consequence of declarations below.
- Manuscript contains no mention of formalization, proof software, or machine
  checking.
- RH is not assumed and not claimed.
- The paper does not claim zero exclusion, a defect-vanishing theorem, or a
  bounded positive reflection sewing.

## Universal normal-cone law

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Functional-equation endpoint charts glue | `endpointNormalChart_eq_reflected` | `formal/GaloisForLFunctions/RHTower/XiSourceNormalConeDivisorConservation.lean` |
| Endpoint chart tends to reciprocal exceptional section | `tendsto_endpointNormalChart_zero` | same |
| Depth successor differentiates to \(-u f'(u)/f(u)\) | `hasDerivAt_depthSuccessorTransport_zero` | same |
| Exceptional section reverses logarithmic connection | `logDeriv_exceptionalBoundarySection` | same |
| Exceptional section reverses meromorphic order | `meromorphicOrderAt_exceptionalBoundarySection` | same |
| Centered affine current is reflection invariant | `exceptionalAffineDivisorCurrent_reflection` | same |
| Its residue is \(-n(\rho-\tfrac12)\) | `exceptionalAffineDivisorCurrent_residue` | same |
| Reflection-odd affine weight is uniquely centered | `affineWeight_reflectionOdd_iff`; `affineWeight_eq_centered_of_reflectionOdd` | same |
| Completed Xi endpoint charts glue and tend to \(1/(2\xi)\) | `xiEndpointNormalChart_eq_reflected`; `tendsto_xiEndpointNormalChart_zero` | same |
| Xi exceptional section reverses divisor order | `meromorphicOrderAt_xiExceptionalBoundarySection` | same |
| Xi current residue law | `xiExceptionalAffineDivisorCurrent_residue` | same |

## Positive exponent-depth source

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Bounded-exponent source equals the \(m\)-free L-series | `boundedExponentEulerSource_eq_LSeries` | `XiSourceNormalConeDivisorConservation.lean` |
| Euler quotient \(\zeta(s)/\zeta((M+1)s)\) | definition `boundedExponentEulerSource`; `boundedExponentEulerSource_normal_coordinate` | same |
| Fixed-scale convergence to zeta | `tendsto_boundedExponentEulerSource_fixedScale` | same |
| Inverse-depth convergence to \(-1/(2\zeta(u))\) | `tendsto_boundedExponentEulerSource_normalScale` | same |
| Microscopic convergence to one | `tendsto_boundedExponentEulerSource_microscopicScale` | same |
| Bundled three-scale law | `zetaSourceScaleTransition_law` | same |
| Positive shell resolution and bulk-boundary duality | `positiveHTBulkBoundaryDuality_law` | same |
| Positive source is positive on its defining half-plane | `boundedExponentEulerSource_pos_of_one_lt` | same |

## Positive shell and relative hypertranscendence

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Shell is \(0/1\)-valued and exact largest-exponent support | `shellIndicator_eq_zero_or_one`; `shellIndicator_eq_one_iff` | `formal/GaloisForLFunctions/RHTower/HighExponentShellZeroFree.lean` |
| Distinct shells have disjoint supports | `shellIndicator_eq_zero_of_ne` | same |
| Shell factorization \(S_m=\zeta H_m\) | `LSeries_shellIndicator` | same |
| Prime-two head and tail bounds | `le_norm_shellHead`; `norm_riemannZeta_diff_sub_shellHead_le` | same |
| \(H_m\) holomorphic and zero-free on \(\Re s>1/2\), \(m\ge12\) | `shellMultiplier_ne_zero`; `analyticAt_shellMultiplier` | same |
| Lowest shell \(\Omega\)-grade and pure-prime equality case | `shellIndicator_cardFactors_lower`; `shellIndicator_eq_prime_pow_of_cardFactors_eq` | `formal/GaloisForLFunctions/RHTower/HighExponentShellHypertranscendence.lean` |
| Selected-prime derivative leading layer | `primeDeriv_rotatedShellJet_eq_zero_of_cardFactors_lt`; `primeDeriv_rotatedShellJet_eq_pointMass_of_cardFactors_eq` | same |
| Tail-immune determinant coefficient | `arithmeticFunction_det_apply_eq_of_cardFactors_lowerLayer_fintype` | same |
| Universal \(\Omega\)-leading finite-jet independence | `omegaLeadingJets_algebraicIndependent` | same |
| Joint zeta-plus-shell differential independence over \(\mathbb C(s)\) | `zetaPositiveShellUpperEnd_differentialIndependent` | same |
| Relative shell multiplier family independent over the full zeta differential field | `relativeShellMultiplierUpperEndCarrier_differentialIndependent_two` | same |

## Least-atom character and two-prime tomography

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Quantitative prime-two extraction | `norm_two_cpow_mul_riemannZeta_sub_one_sub_one_le` | `formal/GaloisForLFunctions/RHTower/HighExponentShellLeastAtomAsymptotic.lean` |
| \(2^{ns}H_n(s)\to1-2^{-s}\) | `tendsto_two_cpow_nat_mul_shellMultiplier` | same |
| Adjacent shell ratio tends to \(2^{-s}\) | `tendsto_shellAdjacentTransfer` | same |
| Normalized ratio tends to \(2^{1/2-s}\) | `tendsto_normalizedShellAdjacentTransfer` | same |
| Character modulus and entropy formula | `norm_shellTransferCharacter`; `log_norm_shellTransferCharacter` | same |
| Critical-line iff unit modulus | `norm_shellTransferCharacter_eq_one_iff` | same |
| Prime-three residual and normalized ratio | `tendsto_three_cpow_nat_mul_shellSecondAtomResidual`; `tendsto_normalizedShellSecondAtomAdjacentTransfer` | `formal/GaloisForLFunctions/RHTower/HighExponentShellPrimeSpectrum.lean` |
| Two-prime character spectrum is injective | `twoPrimeShellTransferSpectrum_injective` | same |
| Shell entropy equals \(1/2-\Re s\) | `shellTransferEntropy_eq` | `formal/GaloisForLFunctions/RHTower/XiHypertranscendentalModularResidueTransgression.lean` |
| Xi affine residue equals shell entropy times multiplicity | `re_centeredXiAffineResidue_eq_shellTransferEntropy`; `tendsto_re_xiExceptionalAffineDivisorCurrent_eq_transferEntropy` | same |
| Base-independent prime-two/prime-three charge | `xiModularCharge_prime_two_eq_prime_three` | same |

## BV prime windows and Hurwitz character

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Compact BV window and Mellin transform | `CompactBVPrimeWindow`; `mellinTransform` | `formal/GaloisForLFunctions/RHTower/BVPrimeWindowQuadrature.lean` |
| Moving-prime and prime-polar coefficients | `weightedPrimeWindow`; `polarCoefficient` | `BVPrimeWindowDirichlet.lean`; `BVPrimeWindowContinuation.lean` |
| Prime-polar L-series convergence and canonical continuation | `polarCoefficient_LSeriesSummable`; `LSeries_polarCoefficient_eq_continuedSource`; `meromorphicOn_continuedSource_rightHalf` | `BVPrimeWindowContinuation.lean` |
| Actual Laurent residue \(2m_\rho I_W(\rho+\tfrac12)\) | `tendsto_continuedSource_residue_of_zeta_zero` | `BVPrimeWindowDivisorTomography.lean` |
| Noncensoring gives a simple pole | `meromorphicOrderAt_continuedSource_eq_neg_one_of_mellin_ne_zero` | same |
| Forward/inverse Mellin characters | `mellinTransform_argumentDilation`; `mellinTransform_argumentExpansion` | `formal/GaloisForLFunctions/RHTower/BVPrimeWindowDilationOrientation.lean` |
| Forward/inverse residue characters | `continuedSourceResidueValue_argumentDilation`; `continuedSourceResidueValue_argumentExpansion` | same |
| Weighted and polar coefficients obey square-index decimation | `weightedPrimeWindow_argumentDilation_eq_argumentExpansion_sq_mul`; `polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul` | same |
| Residue norm ratio recovers horizontal displacement | `xiBVResiduePhaseCoordinate_eq_sourceModularCharge` | `formal/GaloisForLFunctions/RHTower/XiSourceModularTypeSuperselectionLaw.lean` |
| Complex modular character is additive | `centeredComplexModularCharacter_add` | `formal/GaloisForLFunctions/RHTower/RiemannComplexModularCharacterLaw.lean` |
| Real ray equals Mellin character | `centeredComplexModularCharacter_real_cpow` | same |
| Imaginary period equals negative Hurwitz monodromy | `centeredComplexModularCharacter_hurwitzPeriod` | same |
| Principal phase is alias-free in open critical strip | `centeredComplexModularCharacter_principalPhase` | same |

## Valuation Hellinger-Rees fracture

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Diagonal activation is the squarefree partition \(\zeta(s)/\zeta(2s)\) | `woldActivationHolonomy_diagonal_eq_squarefreePartition` | `formal/GaloisForLFunctions/RHTower/EulerActivationSquarefreeDisintegration.lean` |
| Positive valuation mass factors into occupancy and conditional geometric depth | `diagonalActivationPositiveValuationMass_factorization` | same |
| Positive atoms sum to occupancy and total local mass is one | `tsum_diagonalActivationPositiveValuationMass`; `diagonalActivationValuationMass_total` | same |
| Occupancy Fisher coordinate is Bernoulli variance | `diagonalActivationOccupancyFisher_eq_variance` | same |
| Positive prime atoms are Möbius Schur differences | `diagonalActivationPositiveValuationMass_prime_eq_mobiusDifference` | same |
| Positive prime atoms are Fisher-damped Gamma valuation coordinates | `diagonalActivationPrimeMass_eq_fisherDampedGammaValuation` | same |
| Squared damping is exactly occupancy Fisher variance | `xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher` | same |

## Fisher–Gamma infinite Rees resolution

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Fisher-whitened Gamma fibre has exact mass \((p-1)/(p(p+1))\) | `criticalActivationGammaFibreMass_eq` | `formal/GaloisForLFunctions/RHTower/CriticalActivationReesSourceLaw.lean` |
| Gamma-fibre mass is nonsummable over the primes | `not_summable_criticalActivationGammaFibreMass` | same |
| Gamma-sewn multiplier has the exact fourth-power law | `gammaSewnMobiusValuationContractionMultiplier_pow_four` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusValuationContraction.lean` |
| On positive aperture the multiplier lies strictly between \(1/2\) and \(1\) | `one_half_lt_gammaSewnMobiusValuationContractionMultiplier`; `gammaSewnMobiusValuationContractionMultiplier_lt_one` | same |
| Gamma sewing preserves summability of every nonnegative prime energy in both directions | `summable_gammaSewnMobiusMultiplier_sq_mul_iff` | same |
| Iterated valuation differences have exact geometric form | `gammaSewnMobiusContinuousApertureDepthDifference_eq_geometric` | same |
| Every normalized depth difference converges to its prime-log Rees symbol | `tendsto_gammaSewnMobiusContinuousApertureDepthDifference_div_pow` | same |
| First \(N\) symbols on \(N\) distinct primes form a weighted Vandermonde matrix of nonzero determinant | `gammaSewnMobiusReesPrincipalSymbolMatrix_factorization`; `gammaSewnMobiusReesPrincipalSymbolMatrix_det_ne_zero` | same |
| Bundled activation–Gamma–Rees resolution law | `gammaSewnActivationReesResolution_law` | `formal/GaloisForLFunctions/RHTower/XiSourceModularTypeSuperselectionLaw.lean` |
| Exact geometric squared Hellinger formula | `squaredHellingerAffinity`; `primeRadialCrossMass_sq`; definition `primeValuationSquaredHellingerFactor` | `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesReflectionFracture.lean` |
| Negative face is \(\Theta(a_N)\) after squaring | `primeValuationSquaredHellingerBelow_isTheta_wold_of_neg` | same |
| Negative unsquared face is \(\Theta(\sqrt{a_N})\) | `primeValuationHellingerBelow_isTheta_halfNormal_of_neg` | same |
| Critical affinity equals one | `primeValuationSquaredHellingerBelow_zero`; `primeValuationHellingerBelow_zero` | same |
| Positive face is bounded by every Wold power | `primeValuationSquaredHellingerBelow_isBigO_woldPower` | same |
| Positive squared and unsquared faces are all-orders flat | `primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos`; `primeValuationHellingerBelow_reesAllOrdersFlat_of_pos` | same |
| Exact three-phase classification | `primeValuationHellinger_reesType_trichotomy` | same |
| Reflection swaps flat and nonflat type | `reflected_primeValuationSquaredHellinger_type_fracture` | same |

## Universal superselection and exact sewing cost

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Definition of all-orders-flat radical and finite Rees grade | `ReesAllOrdersFlat`; `ReesGradeAtMost`; `ReesOperatorGradeAtMost` | `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesJetStability.lean` |
| Finite packets are flat iff coordinatewise flat | `reesAllOrdersFlat_pi_iff` | same |
| Finite matrices with uniform finite Rees order preserve flatness | `reesAllOrdersFlat_finiteReesJetTransform` | same |
| Arbitrary-dimensional bounded finite-Rees operators preserve flatness | `reesAllOrdersFlat_apply_reesOperatorGradeAtMost` | same |
| Universal scalar essential sewing cost | `reesEssentialSewingCost_beyondEveryFiniteOrder` | `formal/GaloisForLFunctions/RHTower/AsymptoticTypeSuperselection.lean` |
| Universal operator-norm essential sewing cost | `reesExactSewingOperatorNorm_beyondEveryFiniteOrder` | same |
| Actual reflected squared sectors cannot be finitely sewn | `no_finiteReesOperator_sews_reflected_Hellinger_sectors` | `PrimeValuationHellingerReesReflectionFracture.lean` |
| Actual unsquared sectors cannot be finitely sewn | `no_finiteReesOperator_sews_xiRightModularAffinities` | `XiSourceModularTypeSuperselectionLaw.lean` |
| Unsquared exact sewing cost dominates every inverse Wold power | `xiRightModularAffinitySewingCost_beyondEveryReesOrder`; `xiRightModularAffinitySewingOperatorNorm_beyondEveryReesOrder` | same |
| Bundled right-Xi cross-chart superselection law | `xiRightSourceModularTypeSuperselection_law` | same |

## Escaping-quartet optimality

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Xi is unconditionally hypertranscendental | `xi_hypertranscendental` | `formal/GaloisForLFunctions/RHTower/XiHypertranscendenceUnconditional.lean` |
| Normalized quartet gauge and gauged Xi | `normalizedEscapingQuartetGauge`; `escapingQuartetGaugedXi` | `formal/GaloisForLFunctions/RHTower/CompactOpenKolchinWardChargeEscape.lean` |
| Gauged Xi is hypertranscendental and completed-symmetric | `escapingQuartetGaugedXi_hypertranscendental`; `escapingQuartetGaugedXi_one_sub`; `escapingQuartetGaugedXi_conj` | same |
| Added zero is off critical line | `escapingQuartetGaugedXi_added_zero`; `escapingQuartetGaugedXi_added_zero_off_critical` | same |
| Gauged Xi and every fixed jet converge locally uniformly to Xi | `escapingQuartetGaugedXi_tendstoLocallyUniformly`; `escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly` | same |
| Ward density vanishes uniformly on bounded windows | `escapingQuartetWard_window_tendstoUniformly` | same |
| Ward mass is exactly \(8\pi\) | `escapingQuartetWard_mass` | same |
| Modular weight and principal phase remain fixed | `escapingModularPoint_weight`; `escapingModularPoint_principalPhase` | `formal/GaloisForLFunctions/RHTower/RiemannComplexModularCharacterLaw.lean` |
| Reciprocal-square energy has exact formula and tends to zero | `escapingModularTraceEnergy_eq`; `escapingModularTraceEnergy_tendsto_zero` | same |
| Bundled separation theorem | `escapingModularCharacterSeparation_law` | same |

## Bifiltered acquisition and analytic-node obstruction

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Same-prime fusion adds shifted valuation depth and unions residue support | `primeResidueValuationObservableColumn_fusion` | `formal/GaloisForLFunctions/HTGeometry/PrimeResidueValuationInteractionSuperselection.lean` |
| Overlapping residue support makes breadth strictly subadditive while depth remains additive | `primeResidueValuationFusion_depth_breadth_separation` | same |
| No additive map \(\mathbb N^2\to\mathbb N\) is injective | `natProd_addMonoidHom_not_injective` | `formal/GaloisForLFunctions/HTGeometry/BifilteredScalarizationNoGo.lean` |
| Two paired transverse degrees are injective | `transverseScalarDegrees_injective` | same |
| Unpaired marginal degree multisets do not recover pairing | `transverseScalarMarginal_pairing_ambiguity` | same |
| Theta heat nodes converge to zero | `thetaHeatNode_tendsto_zero` | `formal/GaloisForLFunctions/RHTower/XiThetaHeatNodeObstruction.lean` |
| No local analytic or entire single-node delta reader exists | `no_analyticOnNhd_thetaHeatNode_delta`; `no_entire_thetaHeatNode_delta` | same |

## Odd Julia/Fisher orientation producer

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Gamma-sewn scalar cell has a unique minimal positive two-channel Julia lift | `gammaSewnMobiusJuliaSourceTransportV_unique_minimal_positive_lift`; definition `ArithmeticJuliaCellwiseMinimality` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusJuliaSourceTransport.lean`; `ArithmeticJuliaNormalConeUniversalityLaw.lean` |
| Normalized positive Julia defect tends to \(\log p\) | `tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero` | `GammaSewnMobiusJuliaSourceTransport.lean` |
| Julia packet clock tends to actual prime-log clock | `tendsto_gammaSewnMobiusJuliaFiniteTraceClock_nhdsGT_zero` | `ArithmeticJuliaNormalConeUniversalityLaw.lean` |
| Prime source/log-clock graph closure is the full product | `primeFiniteTraceClock_graphClosure_eq_top` | `ArithmeticLogClockBoundedCompletionSaturation.lean` |
| Every bounded packet recovery has diverging operator norm | `tendsto_norm_of_extends_gammaSewnMobiusJuliaFiniteTraceClock` | `ArithmeticJuliaNormalConeUniversalityLaw.lean` |
| Pointed Fisher--Ward trace is odd in the unsquared tangent | `pointedCutoffWardTrace_neg_tangent`; `pointedFisherWard_orientationTransgression` | `formal/GaloisForLFunctions/HTGeometry/PointedFisherCutoffWardTrace.lean`; capstone |
| For self-adjoint cutoff, pointed trace is pairing with double-cutoff curvature | `pointedCutoffWardTrace_eq_opTrace_curvature`; `pointedFisherWard_orientationTransgression` | same |
| Bundled source acquisition law | field `arithmeticJuliaOrientedAcquisition` of `xiRamifiedSingularBoundary_law` | capstone |

## Even-current/odd-orientation parity and finite readers

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Squared completed Xi remains hypertranscendental | `xiRotatedUpperEndCarrier_sq_hypertranscendentalOver` | `formal/GaloisForLFunctions/RHTower/XiRamifiedDifferentialOrientationLaw.lean` |
| Squaring preserves the complete logarithmic-current differential field | `differentialAdjoin_logDeriv_xiRotatedUpperEndCarrier_sq_eq` | same |
| Source-selected Cayley coordinate reverses under sharp reflection | `thetaCuspTailSecondDensityReflectionOddCoordinate_sharp` | same |
| Odd Cayley coordinate vanishes exactly on the regular Xi divisor chart | `thetaCuspTailSecondDensityReflectionOddCoordinate_eq_zero_iff`; `thetaCuspTailSecondDensityReflectionOddCoordinate_eq_zero_at_XiC_zero` | same |
| Every differentiable even reader loses its first jet at the fixed point | `evenReader_firstJet_zero` | `formal/GaloisForLFunctions/HTGeometry/ReflectedChannelProjectiveFlow.lean` |
| Every finite-dimensional Xi log-derivative reporter misses a nonzero derivative packet | `exists_xiLogDeriv_nonzero_finiteDerivativeReporterPacket_ker` | `formal/GaloisForLFunctions/RHTower/XiLogDerivFiniteReporterBlindness.lean` |
| Finite Gibbs dressing does not repair reporter blindness | `exists_xiLogDeriv_add_finiteGibbs_nonzero_finiteDerivativeReporterPacket_ker` | same |
| No positive-aperture finite local polynomial spectral frame represents the horizontal Xi derivative | `not_XiFiniteLocalPolynomialSpectralFrame_of_pos` | `formal/GaloisForLFunctions/RHTower/XiFiniteLocalSpectralFrameObstruction.lean` |
| Bundled parity-resolved source law | `xiDifferentialParityResolved_law`; fields `differentialParityResolution` and `noFiniteLocalOrientationFrame` of `xiRamifiedSingularBoundary_law` | capstone |

## Ramified character and quadratic compression

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Centered complex character is additive and has exact real-ray norm | `centeredComplexModularCharacter_add`; `norm_centeredComplexModularCharacter_ofReal` | `formal/GaloisForLFunctions/RHTower/RiemannComplexModularCharacterLaw.lean` |
| Reflection gives conjugate inverse on the real ray | `centeredComplexModularCharacter_reflection_real` | capstone |
| Real-step unitarity is exactly the critical-line equalizer | `norm_centeredComplexModularCharacter_eq_one_iff` | capstone |
| Deck charge is a \(2^k\)-th root of unity and reads \(2^k\)-divisibility of multiplicity | `xiDeckCharge_pow`; `xiDeckCharge_eq_one_iff_toNat_dvd` | `formal/GaloisForLFunctions/RHTower/XiDeckCharge.lean` |
| Inner profile and outer current have common charge \(-m_\rho(\rho-\tfrac12)\) | `xiDepthNearby_outerCharge_and_affineResidue_match` | `formal/GaloisForLFunctions/RHTower/XiDepthMobiusGammaOuterInnerWeld.lean` |
| Bundled ramified divisor-character law | `xiRamifiedDivisorCharacter_law` | capstone |
| Xi--Hurwitz orientation energy is finite and nonnegative | `xiHurwitzOrientationWeight_summable`; `xiHurwitzOrientationEnergy_nonneg` | `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationEnergy.lean` |
| Energy is zero exactly when every centered divisor character is unitary | `xiHurwitzOrientationEnergy_eq_zero_iff_unitaryCenteredCharacters` | capstone |
| Positive energy has an explicit off-line divisor witness | `xiHurwitzOrientationEnergy_pos_iff_exists_offCriticalZero`; `xiHurwitzOrientationWitness_le_energy` | `XiHurwitzOrientationEnergy.lean` |
| Local quadratic defect is \(\sin^2(2\pi\Re\rho)\) | `xiHurwitzOrientationDefect_eq_sin_sq` | same |
| Terminal Xi--Hurwitz chart package is exactly the zero-energy locus | `xiHurwitzOrientationEnergy_eq_zero_iff_universalCertificate` | `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationUniversalityLaw.lean` |
| Whole-corpus eighteen-family positive phase and a single Sonin collar have the same zero-energy/RH locus | `riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate`; `wholeCorpusPositivePhaseUniversalCertificate_iff_singlePositiveSoninAperture`; `riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero` | `XiWholeCorpusPositivePhaseUniversalityLaw.lean`; `XiWholeCorpusPositiveSoninApertureCollapseUniversalityLaw.lean`; `XiHurwitzOrientationEnergy.lean` |

## Hedenmalm, Wold, Sonin/Calkin, and Ward consumers

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Positive momentum-symmetric theta-null forms are divisor-supported atomic Fourier riggings | `universalPositiveForm_thetaNull_iff_canonicalMeasure_support_realDivisor`; `universalPositiveForm_canonicalMeasure_atomic_of_thetaNull` | `formal/GaloisForLFunctions/RHTower/HedenmalmUniversalPositiveFormClassification.lean` |
| Every nonzero such form has dense nonclosed \(L^2\) radical and is nonclosable | `universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw`; `universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_zero` | `HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean`; `HedenmalmUniversalPositiveFormClassification.lean` |
| Independent Wold-depth/Poisson-time quadrant boundedness is the zero-rate equalizer | `conjugateTwoClockQuadrantBounded_iff`; `conjugateTwoClockQuadrantBounded_xiSourceRate_iff_boundaryFracture_zero` | `HighExponentShellLeastAtomAsymptotic.lean`; capstone |
| All-scale prime-seam Sonin/Calkin compactness is the same equalizer | `xiPrimeSeamAllScaleCalkinCertificate_iff_riemannHypothesis`; `xiBoundaryCharacterNeutral_iff_regularBoundaryConsumers` | `XiPrimeSeamCalkinUniversalityLaw.lean`; capstone |
| Fixed-edge four-unit Ward positivity is the same equalizer; one strict-right zero gives a one-node failure | `continuedXiWardEulerEdgeBoundaryGramLaw_of_riemannHypothesis`; `xiRightUpperHorizontalFailure_law` | `GammaSewnMobiusXiWardEulerEdgeCompleteness.lean`; capstone |
| All three consumers are bundled by one character-neutrality law | `xiBoundaryCharacterNeutral_iff_regularBoundaryConsumers` | capstone |

## Dyadic ramification and full aperture spectrum

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Each dyadic rung is equivalent across analytic roots, slit roots, circle monodromy, window decks, and Schwarz roots | `rhLadder_iff_dyadicDescentLevelUniversalCertificate` | `formal/GaloisForLFunctions/RHTower/XiDyadicDescentLevelUniversalityLaw.lean` |
| All dyadic levels are equivalent to RH | `riemannHypothesis_iff_forall_dyadicDescentLevelUniversalCertificate` | same |
| If RH fails, valid dyadic levels form the exact initial segment through the sharp level | `dyadicDescentLevelUniversalCertificate_iff_le_sharpLevel` | same |
| Persistent rung-one defect loop is equivalent to odd multiplicity in the right open strip | `xiDefect_persistentLoop_openStrip_oddOrderUniversality` | `XiDefectPersistentLocalLoopUniversalityLaw.lean` |
| Positive finite first-order density forces \(2qm=1\) | `two_mul_rate_mul_analyticOrderNatAt_eq_one_of_boundaryDensity_pos` | `formal/GaloisForLFunctions/RHTower/CCMFiniteRamifiedBoundaryNoGo.lean` |
| Finite-sheeted positive density forces even sheet number and sign deck character | `finiteRamified_boundaryDensity_forces_even_and_deckCharacter_neg_one` | same |
| Full finite deck descent is incompatible with positive density, including four-unit normalization | `not_exists_finiteRamified_deckInvariant_positiveBoundaryDensity`; `ccmFourUnit_not_finiteRamified_deckInvariant` | same |
| Nontorsion deck descent is incompatible with positive density | `not_exists_analyticRamified_infiniteDeckInvariant_positiveBoundaryDensity`; `ccmFourUnit_not_analyticRamified_infiniteDeckInvariant` | same |
| Poisson vertical type is equivalent to the divisor half-plane bound | `xiPoissonTraceVerticalTypeAtMost_iff_xiZeroHalfPlaneBound` | `XiSpectralApertureConservationUniversalityLaw.lean` |
| Full common aperture spectrum is \([\text{projective reflection radius},\infty)\) | `xiSpectralApertureSpectrum_eq_Ici_projectiveReflectionRadius` | same |
| Original aperture bound implies the same mass-trace exponential type | `xiMassTraceLineGrowth_of_xiZeroStrip` | `XiMassGradedTraceZeroFreeDistortionUniversalityLaw.lean` |
| Mass-trace type returns original width with factor \((9+a^2)/9\) | `nine_mul_sq_im_xiSpectralPoint_le_of_xiMassTraceLineGrowth` | same |
| Bundled mass data-processing law | `xiMass_gradedTrace_zeroFreeDistortionUniversality`; field `massTraceDistortion` of `xiRamifiedSingularBoundary_law` | same; capstone |
| Bundled bifiltered ramified-character boundary law | `xiRamifiedSingularBoundary_law` | capstone |

## Universal conservative descent

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| A norm-conservative real-linear action cannot have a nonzero positive eigenvector with eigenvalue other than one | `normConservative_realEigenvector_eigenvalue_eq_one` | capstone |
| A nonzero exponential eigencharacter in a conservative target has zero real rate | `normConservative_expCharacter_forces_zero` | capstone |
| Faithful equivariant descent into a conservative target forces zero rate | `normConservative_equivariantDescent_forces_zero` | capstone |

## Projective source pointing and finite positive collision geometry

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Complete signed-prime shift fields agree iff orientations are eventually equal or opposite | `signedPrimeNaturalShiftPalette_differentialAdjoin_eq_iff` | `formal/GaloisForLFunctions/HTGeometry/PrimeDirichletDifferentialField.lean` |
| Every projective-tail class is dense; quotient is indiscrete | `booleanProjectiveTailClass_fiber_dense`; `booleanProjectiveTail_coinduced_eq_indiscrete` | `formal/GaloisForLFunctions/HTGeometry/PrimeDirichletTailGroupoid.lean` |
| Continuous \(T_0\)-valued invariants factoring through projective tail class are constant | `continuous_constant_of_booleanProjectiveTailClass` | same |
| Signed vertical prime trace is positive definite iff all signs are positive | `signedPrimeVerticalTrace_positiveDefinite_iff_allPositive` | `formal/GaloisForLFunctions/HTGeometry/PrimeDirichletPositiveDefinite.lean` |
| Bundled projective-tail pointing law | `primeProjectiveTailPositivePointing_law` | capstone |
| Pairwise transverse Xi carriers have the rooted incidence matroid | `rootedIncidenceMatroid_charZero_eq`; `xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_base_eq_allValuation` | `formal/GaloisForLFunctions/RHTower/XiPairwiseValuationBaseUniversalityLaw.lean` |
| Adjoining every scalar valuation layer leaves that matroid unchanged | `xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_base_eq_allValuation` | same |
| Rooted-star incidence, valuation, Gaussian, Szegő, cofinite jet, and raw-Xi phases collapse to distinct nonzero labels | `xiRootedStar_incidenceValuationExactMetricFusion_reparam_iff` | `formal/GaloisForLFunctions/RHTower/XiRootedStarIncidenceValuationMetricFusionUniversalityLaw.lean` |
| Cofinite raw-Xi reconstruction is equivalent to nonzero label injectivity | `xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff` | `formal/GaloisForLFunctions/RHTower/XiRootedStarGaussianCurvatureFusionUniversalityLaw.lean` |
| Every finite resolution has a reporter faithful to Xi jets and blind to a nonzero log-current packet | `exists_injective_xiEvaluationReporter_faithfulXi_blindLogDeriv` | `formal/GaloisForLFunctions/RHTower/XiEvaluationReporterSourceDiscriminationUniversalityLaw.lean` |
| Isometric encoding preserves positive Xi Gram, blind kernel/rank, and adjoint recovery | `xiCofiniteEvaluationReporter_exactBlindDataProcessingUniversality` | `formal/GaloisForLFunctions/RHTower/XiCofiniteExactBlindDataProcessingUniversalityLaw.lean` |
| Bundled finite source/current separation | `xiFiniteSourceObservableSeparation_law` | capstone |

## Strict positive-observable hierarchy and quantitative positive survivor

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Any prescribed \(\vartheta\pm ia\) in the right critical strip occurs as zeros of an explicit nonnegative unit-pole Mellin source | `ccm_criticalClock_divisor_blindness` | `formal/GaloisForLFunctions/RHTower/CCMCriticalClockDivisorBlindness.lean` |
| This witness has the unit exponential critical clock and Schwarz-pair Cauchy energy \(>8\) | `tendsto_blindWitness_criticalClockLaplace`; `schwarzPairCauchyEnergy_gt_eight`; `ccm_criticalClock_divisor_blindness` | same |
| Four-unit source profile is a critical-clock class invariant but divisor energy is not | `fourUnitBudget_classInvariant_but_divisor_not` | same |
| Endpoint cross charge is \(c_\rho=\Re(1/[\rho(1-\rho)])\), nonnegative in open critical strip | `xiEndpointCrossCharge`; `endpoint_cross_term_re_eq`; `endpoint_cross_term_re_nonneg` | `formal/GaloisForLFunctions/RHTower/XiEndpointOffLineQuartetHeightGap.lean`; `formal/GaloisForLFunctions/RHTower/XiEndpointQuantitativeNormBudget.lean` |
| Off-line endpoint charge is nonnegative, bounded by completed endpoint curvature, and vanishes exactly on RH | `xiEndpointOffLineCharge_nonneg`; `xiEndpointOffLineCharge_eq_zero_iff_rh`; `xiEndpointOffLineCharge_le_curvature` | `formal/GaloisForLFunctions/RHTower/XiThermalOffLineChargeSelfCubicBound.lean` |
| Every hypothetical off-line zero satisfies \((\Im\rho)^2>7907/93\) | `xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq` | `formal/GaloisForLFunctions/RHTower/PrimeArchExactOffLineQuartetAccretivity.lean` |
| Total transverse orientation energy obeys the self-localized cubic budget | `xiThermalOrientationEnergy_le_offLineChargeCubicBudget` | `formal/GaloisForLFunctions/RHTower/XiThermalOffLineChargeSelfCubicBound.lean` |
| Self-localized budget improves the source-only exact cubic budget | `xiThermalOffLineChargeCubicBudget_le_exactCubicEndpointBudget` | same |
| Exact source-only cubic budget is below \(1/150000\) | `xiThermalExactCubicEndpointBudget_lt_one_over_oneHundredFiftyThousand` | `formal/GaloisForLFunctions/RHTower/XiThermalQuartetCubicChargeBound.lean` |
| Off-line charge, cubic budget, transverse energy, and RH have the same zero locus | `xiThermal_offLineCharge_budget_energy_zero_tfae` | `XiThermalOffLineChargeSelfCubicBound.lean` |
| Thermal/source second-moment gap is exactly transverse energy | `xiThermalSecondMoment_sub_source_eq_orientationEnergy`; `xiThermalSecondMoment_source_absoluteGap` | `XiThermalQuartetCubicChargeBound.lean` |
| Every off-line atom has a real affine test with zero positive Hilbert response and positive transverse charge | `exists_xiSquaredEulerAperture_atom_charge_without_hilbert` | `formal/GaloisForLFunctions/RHTower/XiSquaredEulerApertureDiagonalControlObstruction.lean` |
| No finite atomwise comparison constant exists off line; orbitwise bounded control is equivalent to RH | `not_exists_xiSquaredEulerAperture_termwise_bound_of_ne_half`; `xiSquaredEulerApertureOrbitwiseBoundedCharge_iff_riemannHypothesis` | same |
| The mixed exponential witness is nonnegative on the physical diagonal but its separated cylinder lift is negative | `coneObstruction_nonneg`; `cylinderLift_obstructionPoint` | `formal/GaloisForLFunctions/RHTower/ConePositivstellensatzFailure.lean` |
| Separated cylinder lift is not a finite sum of squared moduli | `cylinderLift_not_sum_of_squares` | same |
| Reflected source-only Ward majorant diverges on every fixed source line | `xiWardInteriorSourceArithmeticBound_vertical_tendsto_atTop`; `not_exists_uniform_xiWardInteriorSourceArithmeticBound` | `formal/GaloisForLFunctions/RHTower/XiWardInteriorSourceBudgetDivergence.lean` |
| No finite-energy half-line source represents the already-scalarized full Xi current | `not_exists_halfLineLaplaceSource_logDeriv_xi_vertical` | same |
| Every off-axis centered Xi zero is detected by one negative rank-one diagonal Weil value | `exists_neg_weilDiagonal_of_offAxis_zero`; `riemannHypothesis_of_weilDiagonal_nonneg` | `formal/GaloisForLFunctions/RHTower/XiWeilCriterionConverse.lean` |
| Bundled hierarchy law | `xiPositiveObservableHierarchy_law` | capstone |

## Hyperbolic reflection, quantized debt, and Schur tax

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Reflected rate pair preserves only the hyperbolic quadratic form \(2xy\) up to scale | `reflectedRealCharacter_invariantQuadratic_iff` | capstone |
| Only positive-semidefinite invariant quadratic form at nonzero rate is zero | `reflectedRealCharacter_no_nonzero_positiveInvariantQuadratic` | capstone |
| Finite generic quartet Ward charge/\(4\pi\), Euler pole excess, and Weil negative index agree | `finiteQuartet_eulerWardWeil_index_law` | `formal/GaloisForLFunctions/RHTower/PositiveEulerFiniteQuartetOrientationLaw.lean` |
| Positive two-channel completion requires \(c\ge n+b^2/a\) | `suzukiKreinScalarSchurComplement_posSemidef_iff`; `suzukiKreinScalarWeld_posSemidef_iff_twoChannelForm` | `formal/GaloisForLFunctions/RHTower/SuzukiKreinSchurBlockCongruence.lean` |
| Bundled reflection-character completion | `xiReflectionCharacterCompletion_law` | capstone |

## Source horizon, local quotient, global tomography, and multiplicity

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Poisson order normalization uniquely converts a source generator into its direct conjugate displacement | `coherentGenerator_duality`; `sourceCayley_inverse_observationTime`; `sourceHorizonEscapeConservation_law` | `formal/GaloisForLFunctions/RHTower/SourceHorizonEscapeConservationLaw.lean` |
| Critical line is the neutral source horizon | `sourceCayleyTransverseRate_eq_zero_iff`; field `sourceHorizon` of `sourceHorizonEscapeConservation_law` | same |
| Continuous finite-factor-invariant compact-germ readers are constant on reflected local orbits | `no_continuous_frequencyInvariant_traceHankel_classifier` | `formal/GaloisForLFunctions/RHTower/ReflectedLambertRHBarrier.lean` |
| One fixed-width logarithmically sampled prime–Gamma tail reconstructs off-line divisor poles and multiplicities | `meromorphicOrderAt_xiRectangularPrimeGammaTailContinuation_eq_neg_one_iff`; `normalizedPrimeGammaTailResidue_eq_xiRightMultiplicity` | `formal/GaloisForLFunctions/RHTower/CCMPrimeGammaSourceDivisorTomography.lean` |
| Local reflection-odd aperture collision equals \(-4m_\rho^2\) | `xiCompletedApertureRegularizedResonantTwoPointDet_zero` | `formal/GaloisForLFunctions/RHTower/XiCompletedAperturePoleResonance.lean` |
| Collision value \(-4\) is equivalent to simplicity, Hedenmalm normality, trivial relative \(K_1\) unit, and zero regulator | `xiCompletedApertureCollision_neg_four_iff_completeLocalSimplicity` | same |
| Final capstone includes pointing, source/current separation, positive hierarchy, reflection completion, global tomography, and multiplicity tomography | `xiRamifiedSingularBoundary_law` | capstone |

## Uniform-annihilator and Cholesky results intentionally not promoted to direct corollaries

| Corpus theorem | Audit disposition |
|---|---|
| Uniform-annihilator inverse-limit law and clock-order escape | Structural instance of cofinal singularity: every finite stage can be differentially algebraic while annihilator order escapes every bound. It does not add a new divisor-orientation implication, so manuscript mentions it only in corpus interpretation. |
| Cofinal inverse-Cholesky carrier selection and divergent repair | Structural analogue of singular acquisition and recovery blow-up. Its general Herglotz setting is not a theorem about the Xi source, so importing it into the main theorem would be collage. |

## Direct verification record

Pending final audit after manuscript freeze.
