# Formalization certificate: completed-seam theta Green-square boundary law

- **ID:** `completed-seam-theta-green-square-boundary-law-formalized`
- **Stage:** 3-formalized
- **Paper/open card:** `../../../1-in-progress/completed-seam-theta-green-square-boundary-law.md`
- **Scientific status:** `[FORMALIZED CROSS-ROUTE LAW] [FORMALIZED PRODUCER NO-GO] [RH OPEN]`

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaGreenSquareBoundaryLaw.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaGreenReflectionPairNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaGreenHyperbolicGaugeNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaRouteRPositiveUnitCurrentBridge.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniFluxPolarization.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniHarmonicCoercivity.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrimeSeamPolarizationBridge.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniQuantizedEscape.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniBalancedIndexNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniPermutationSectorNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrincipalCountertermPolarityNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrincipalClassTrichotomy.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaContinuousPrincipalRenormalizationNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalProfileBridge.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalWardContract.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalCodiagonalPacketBlowup.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalScalarReaderPacketBlowup.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointCompletedResponseWardBridge.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaCompletedResponseMarginalGaugeNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointLogarithmicBoundaryLaw.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointHardyGreenResidualBridge.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaCompletedResponseCofinalGaugeNegativity.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointPrimeHardyGreenScaling.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointPrimeHardyGreenRenormalizationNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointSymmetricQuartetHardyGreenNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMovingHorizonReflectionIncidenceTrichotomy.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMovingHorizonCovariantHardyGreenRegularization.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMovingHorizonAnalyticDoubletNoGo.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaXiHardySymmetricSquareWeld.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusTwoSidedApertureWall.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusUnitHardyGramRigidity.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSourceJuliaPythagoras.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusHyperbolicRapidity.lean
```

All thirty-four modules are imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Closed theorem chain

Namespace `RHTower.HedenmalmThetaSource`.

| Statement | Lean declaration |
|---|---|
| every nonzero spectral value of the source inverse has positive real square iff RH | `thetaSquaredSeamSpectrumPositive_iff_riemannHypothesis` |
| individual Green-boundary neutrality iff RH | `thetaGreenBoundaryNeutral_iff_riemannHypothesis` |
| squared spectral positivity iff individual boundary neutrality | `thetaSquaredSeamSpectrumPositive_iff_greenBoundaryNeutral` |
| squared spectral positivity iff compact Markov endpoint | `thetaSquaredSeamSpectrumPositive_iff_compactMarkov` |
| squared spectral positivity iff compact Thorin endpoint | `thetaSquaredSeamSpectrumPositive_iff_compactThorin` |
| Green-square decomposition `G B^2=B^* G B+i R_2 B` | `thetaMetric_greenSquare_boundary_decomposition` |
| correction range lies in pinned affine boundary space | `range_pinnedBoundary_mul_thetaKernel_le_affineSubspace` |
| theta root energy is invariant under functional-equation reflection | `thetaXiRootEnergy_reflect` |
| boundary current is reflection-odd | `thetaXiRankTwoBoundaryFlux_reflect` |
| unsquared theta eigenvalue is reflection-odd; its square is reflection-invariant | `thetaXiReciprocalEigenvalue_reflect`, `thetaXiReciprocalEigenvalue_sq_reflect` |
| one squared theta node is strictly positive real iff its same-fibre boundary current vanishes | `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero` |
| reflected-pair current cancels unconditionally | `thetaGreenReflectedPairNeutral_unconditional` |
| one folded `B²` node contains both reflected eigenmodes and zero aggregate current | `thetaGreenSquaredReflectionFiber_sameNode_zeroCurrent` |
| automatic pair neutrality plus individual neutrality is still exactly RH | `thetaGreenReflectedPairNeutral_and_fiberNeutral_iff_riemannHypothesis` |
| theta rank-two current is Route R's split Hermitian form in moment coordinates | `inner_pinnedBoundaryCLM_eq_thetaGreenHyperbolicCurrent` |
| split current equals incoming-minus-outgoing intensity and is boost-invariant | `thetaGreenHyperbolicCurrent_eq_amplitudeDifference`, `thetaGreenHyperbolicCurrent_gauge` |
| conserved current cannot select neutral grade on a prime-character orbit | `thetaGreenHyperbolicCurrent_not_neutralSelector` |
| fixed positive polar energy is boost-invariant exactly at neutral grade | `thetaGreenFixedPolarEnergy_gauge_eq_iff` |
| quantile source and its boundary image are independent lightlike axes | `thetaGreenQuantileNullFrame_current_zero`, `thetaGreenQuantileNullFrame_det_ne_zero` |
| their positive energies balance after boost exactly at neutral grade | `thetaGreenQuantileNullFrame_gauge_balanced_iff` |
| theta Green flux is negative positive-unit equivalent to actual Route R Hodge mate | `thetaXiRankTwoBoundaryFlux_eq_neg_positiveUnit_mul_routeRHodgeMate` |
| theta Green flux is negative positive-unit equivalent to literal reflected Deninger boundary | `thetaXiRankTwoBoundaryFlux_eq_neg_positiveUnit_mul_deningerBoundary` |
| either source-current annihilation is exactly individual Route P node positivity | `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_routeRHodgeMate_eq_zero`, `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_deningerBoundary_eq_zero` |
| Route N current is centered grade times a completed strictly positive Krein slope | `routeNGammaSewnCriticalHorizonKreinCharge_eq_neg_grade_mul_slope`, `thetaRouteNKreinSlope_pos` |
| local Hellinger defect is a strictly positive unit times squared theta Green flux | `primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq`, `thetaKakutaniFluxPositiveUnit_pos` |
| reflected signed currents cancel but their positive polarizations add to twice one defect | `thetaKakutaniFluxPolarization_add_reflect_eq_two_gap`, `thetaKakutaniFluxPolarization_add_reflect_pos_iff` |
| all-prime polarization summability is exactly same-fibre current neutrality and node positivity | `summable_thetaKakutaniFluxPolarization_iff_boundaryFlux_zero`, `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_kakutaniFluxPolarization` |
| off-neutral polarization dominates an explicit positive multiple of `1/p` prime by prime | `thetaKakutaniHarmonicFloor_pos_iff_boundaryFlux_ne_zero`, `thetaKakutaniHarmonicFloor_mul_primeHarmonic_le_polarization` |
| reflected pairing doubles the harmonic lower floor | `two_mul_thetaKakutaniHarmonicFloor_mul_primeHarmonic_le_reflectionPair` |
| uniform boundedness of finite-prime polarization energies is exactly node positivity | `thetaXiRankTwoBoundaryFlux_eq_zero_of_uniform_finset_polarization_bound`, `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_uniform_finset_polarization_bound` |
| prime-clock reflection energy is the local Hellinger defect times the exact absolute-grade source gauge | `primeClockReflectionEnergy_eq_absCenteredGauge_mul_hellingerGap` |
| squared norm of the literal FE--Schwarz prime seam is an explicit positive source unit times theta polarization | `norm_sq_orbitwisePrimeSeamCharge_eq_positiveUnit_mul_thetaPolarization`, `thetaPrimeSeamPolarizationPositiveUnit_pos` |
| normalized literal seam energy equals theta polarization without grade division | `norm_sq_orbitwisePrimeSeamCharge_div_sourceUnit_eq_thetaPolarization` |
| one-prime seam vanishing and uniform normalized finite-prime seam energy are exactly node positivity | `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_primeSeamCharge_zero`, `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_uniform_normalizedPrimeSeamEnergy` |
| local polarization is one harmonic atom minus an explicit radial deficit | `thetaKakutaniFluxPolarization_eq_primeHarmonic_mul_sq`, `thetaKakutaniFluxPolarization_add_deficit_eq_primeHarmonic` |
| off center, the radial deficit is summable and the renormalized polarization has a finite prime sum | `summable_thetaKakutaniHarmonicDeficit_of_boundaryFlux_ne_zero`, `hasSum_thetaKakutaniFluxPolarization_sub_primeHarmonic` |
| finite-prime polarization divided by reciprocal-prime mass converges to the quantized index zero or one | `tendsto_thetaKakutaniFluxPolarization_div_primeReciprocalMass`, `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_harmonicEscape_zero` |
| a nonneutral reflected pair has quantized escape two | `tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass` |
| escape multiplicity is reflection-even, while the balanced Fredholm index is always zero | `thetaKakutaniEscapeMultiplicity_reflect`, `thetaKakutaniBalancedFredholmIndex_eq_zero` |
| balanced unsigned defect energy is twice escape multiplicity and equals the reflected theta-energy limit | `thetaKakutaniBalancedUnsignedDefectEnergy_eq`, `tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass_eq_defectEnergy` |
| no reflection-odd integer index represents positive escape on a nonneutral pair | `reflectionOdd_integerIndex_ne_escapeMultiplicity_of_boundaryFlux_ne_zero` |
| universal critical prime amplitude is not square summable, while every nonneutral twisted amplitude is | `not_summable_routeNGammaSewnUniversalCriticalChannelAmplitude_sq`, `summable_routeNGammaSewnTwistedCriticalChannelAmplitude_sq_of_ne` |
| subtracting any square-summable prime correction cannot produce a square-summable critical-channel gap | `not_summable_sq_sub_universal_of_summable_sq` |
| arbitrary prime relabeling yields square-summable critical/twisted gap exactly at neutral grade | `exists_primePermutation_summable_amplitudeGap_iff` |
| prime-sector equivalence under some relabeling is exactly boundary-flux neutrality and individual Route P node positivity | `exists_primePermutation_summable_amplitudeGap_iff_boundaryFlux_zero`, `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_exists_primePermutation_summable_amplitudeGap` |
| subtraction of universal harmonic mass makes the Hellinger gap summable exactly off neutral grade, stably under every summable correction | `summable_thetaPrimePrincipalRelativeGap_iff`, `summable_thetaPrimePrincipalRelativeGap_add_iff_of_summable` |
| normalized unit-double Euler response is exactly `-p⁻¹+2p⁻²` | `thetaUnitDoubleEulerNormalizedCounterterm_eq` |
| adding that actual source counterterm makes the Route P gap summable exactly when theta flux is nonzero | `summable_thetaGap_add_unitDoubleEulerCounterterm_iff_boundaryFlux_ne_zero` |
| individual squared-node positivity is failure of summability for the unit-double-corrected gap | `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_not_summable_unitDoubleCorrectedGap` |
| modulo summable tails, fixed principal correction is summable exactly in the two class-cancelling cases | `summable_thetaPrimeFixedPrincipalCorrection_iff` |
| coefficient zero selects only neutral grade, coefficient minus one selects only nonneutral grade, and every other coefficient selects nothing | `summable_thetaPrimeUnrenormalizedGap_add_iff`, `summable_thetaPrimeFullySubtractedGap_add_iff`, `not_summable_thetaPrimeFixedPrincipalCorrection_of_ne_zero_of_ne_neg_one` |
| unrenormalized gap plus any summable tail retains exact individual Route P node-positivity locus | `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_unrenormalizedGap_add` |
| universal grade-dependent diagonal admission forces principal coefficient zero at the wall and minus one off it | `principalCoefficient_eq_zero_at_wall_of_universalAdmission`, `principalCoefficient_eq_neg_one_off_wall_of_universalAdmission` |
| no principal coefficient continuous at the critical wall can universally admit every grade, even with arbitrary grade-dependent summable tails | `no_continuous_principalCoefficient_universalAdmission`, `no_continuous_principalCoefficient_universalAdmission_global` |
| literal singular Möbius prime-normal reflection profile is `p^a-p⁻ᵃ` | `thetaMobiusPrimeNormalReflectionProfile_eq` |
| Route P local Hellinger gap is a strictly positive gauge times the square of that physical source profile | `primeValuationHellingerGap_eq_mobiusPrimeNormalProfile_sq`, `thetaMobiusPrimeNormalProfilePositiveGauge_pos` |
| physical source-profile vanishing is exactly theta Green-flux neutrality | `thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero` |
| all-prime weighted physical source-profile admission is exactly individual Route P squared-node positivity | `thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_mobiusPrimeNormalProfileEnergy` |
| every finite physical Möbius-profile packet energy equals the theta/Kakutani packet energy | `thetaMobiusPrimeNormalProfilePacketEnergy_eq_thetaPolarization` |
| uniform finite-packet physical Ward control at one divisor copy is exactly positivity of its Route P squared node | `thetaMobiusPrimeNormalWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal` |
| global finite-packet physical Ward control is equivalent to RH | `thetaMobiusPrimeNormalWardBound_iff_riemannHypothesis` |
| normalized physical half-density is the oriented universal-minus-twisted critical channel gap and its square is the Route P energy | `thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap`, `thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq` |
| physical half-density is absolutely summable exactly at theta-flux neutrality | `summable_abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_iff_boundaryFlux_zero` |
| physical half-density belongs to the adaptive prime-normal `ℓ¹` domain exactly at theta-flux neutrality; global admission is RH | `exists_adaptivePrimeL1_physicalHalfDensity_iff_boundaryFlux_zero`, `all_exists_adaptivePrimeL1_physicalHalfDensity_iff_riemannHypothesis` |
| finite physical half-density packet has exact `ℓ¹` norm and its Route P energy is bounded by that norm | `norm_thetaMobiusPrimeNormalHalfDensityPacket`, `thetaMobiusPrimeNormalProfilePacketEnergy_le_halfDensityPacket_norm` |
| adaptive codiagonal lower bound controls finite physical packet norm by actual arithmetic output norm | `norm_halfDensityPacket_le_codiagonalPacketOutput` |
| uniform actual codiagonal packet-output boundedness is exactly same-fibre neutrality and individual Route P node positivity | `thetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt_iff_boundaryFlux_zero`, `thetaMobiusPrimeNormalCodiagonalPacketOutputBoundAt_iff_reciprocalEigenvalue_sq_positiveReal` |
| every nonneutral copy has actual codiagonal packet outputs exceeding every threshold; global boundedness is RH | `exists_codiagonalPacketOutput_norm_gt_of_boundaryFlux_ne_zero`, `thetaMobiusPrimeNormalCodiagonalPacketOutputBound_iff_riemannHypothesis` |
| physical half-density coefficients have one common orientation across all primes | `thetaMobiusPrimeNormalProfileHalfDensityAmplitude_nonneg_of_rate_nonneg`, `thetaMobiusPrimeNormalProfileHalfDensityAmplitude_nonpos_of_rate_neg`, `norm_sum_thetaMobiusPrimeNormalProfileHalfDensityAmplitude` |
| exact scalar reader differs from common `-1` principal output by at most one quarter of packet mass and retains at least three quarters | `norm_scalarReaderPacketOutput_add_principal_le_quarter`, `three_quarters_halfDensityMass_le_scalarReaderPacketOutput_norm` |
| Route P packet energy is controlled by literal signed scalar reader output; boundedness is copywise neutrality and globally RH | `thetaMobiusPrimeNormalProfilePacketEnergy_le_scalarReaderPacketOutput_norm`, `thetaMobiusPrimeNormalScalarReaderPacketOutputBoundAt_iff_boundaryFlux_zero`, `thetaMobiusPrimeNormalScalarReaderPacketOutputBound_iff_riemannHypothesis` |
| every nonneutral copy has signed scalar Möbius packet outputs exceeding every threshold | `exists_scalarReaderPacketOutput_norm_gt_of_boundaryFlux_ne_zero` |
| physical endpoint marginal times normalized physical-profile square is exactly Route P local energy | `physicalPrimeEndpointWeight_mul_normalizedHalfDensity_sq` |
| completed-response signed Dirichlet term is the explicit corrected off-diagonal endpoint kernel | `thetaPhysicalEndpointCompletedResponseDirichletEnergy_eq_pairResponse`, `thetaPhysicalEndpointCompletedResponseDirichletEnergy_eq_kernel` |
| every Route P packet is exactly completed response pairing plus one half of signed Dirichlet energy | `thetaPhysicalEndpointCompletedResponsePairing_eq_packetEnergy_sub_half_dirichlet`, `thetaMobiusPrimeNormalProfilePacketEnergy_eq_completedResponseBudget` |
| uniform completed-response budget is individual Route P node positivity; globally it is RH | `thetaPhysicalEndpointCompletedResponseWardBoundAt_iff_reciprocalEigenvalue_sq_positiveReal`, `thetaPhysicalEndpointCompletedResponseWardBound_iff_riemannHypothesis` |
| every symmetric finite coupling budget depends only on its row marginal; same-marginal couplings have identical budgets | `finite_symmetric_coupling_budget_eq_marginal`, `finite_symmetric_same_marginal_budget_eq` |
| completed response minus diagonal marginal is a zero-row-sum gauge whose pairing plus half Dirichlet energy vanishes identically | `sum_thetaPhysicalEndpointCompletedGaugeCoupling`, `thetaPhysicalEndpointCompletedGaugePairing_add_half_dirichlet_eq_zero` |
| completed-response combined budget equals diagonal marginal budget for every packet | `thetaPhysicalEndpointCompletedResponseBudget_eq_diagonalMarginalBudget` |
| normalized endpoint profile has exact logarithmic square `(1-p⁻ᵈ)²` and quantized prime trace zero/one | `log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq`, `tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_zero_iff_boundaryFlux_zero`, `tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_one_iff_boundaryFlux_ne_zero` |
| ordinary prime-`ℓ²` admission of normalized endpoint profile is copywise neutrality; global admission and zero trace are RH | `summable_sq_thetaPhysicalEndpointNormalizedHalfDensity_iff_boundaryFlux_zero`, `all_summable_sq_thetaPhysicalEndpointNormalizedHalfDensity_iff_riemannHypothesis`, `all_tendsto_log_mul_thetaPhysicalEndpointNormalizedHalfDensity_sq_zero_iff_riemannHypothesis` |
| missing endpoint tail exactly complements physical profile and has energy `4/|a|` | `thetaPhysicalEndpointHardyGreenResidual_complements_physical_profile`, `integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_four_div_abs_centeredRate` |
| residual energy equals exceptional Hardy--Green energy and four times transverse Cauchy self-energy | `integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_exceptionalHardyGreenEnergy`, `integral_sq_thetaPhysicalEndpointHardyGreenResidual_eq_cauchy_self` |
| every exceptional residual exceeds four; global four-unit residual bound is RH | `four_lt_integral_sq_thetaPhysicalEndpointHardyGreenResidual`, `thetaPhysicalEndpointHardyGreenResidualFourBound_iff_riemannHypothesis` |
| on a two-prime positive edge the completed gauge is a negative graph Laplacian, and such strict negative directions occur cofinally | `thetaPhysicalEndpointCompletedGaugeQuadraticForm_pair`, `thetaPhysicalEndpointCompletedGaugeDirichletForm_pair`, `exists_cofinal_thetaPhysicalEndpointCompletedGauge_negativeDirection` |
| physical prime sampling of residual square is exactly eight times prime-square Euler weight | `physicalPrimeEndpointWeight_mul_hardyGreenResidual_sq`, `thetaPhysicalEndpointSampledHardyGreenResidualEnergy_eq` |
| sampled energy equals the real prime-log Dirichlet series and has exact critical coefficient four | `thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_primeLogDirichlet`, `tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy`, `tendsto_normalized_thetaPhysicalEndpointPrimeHardyGreenEnergy` |
| sampled energy is exactly continuous `4/d` energy plus a prime/continuous regular anomaly extending to the wall | `thetaPhysicalEndpointPrimeHardyGreenEnergy_eq_four_div_add_regularAnomaly`, `tendsto_thetaPhysicalEndpointPrimeHardyGreenEnergy_sub_four_div` |
| scalar `c/d` removes the scaled principal pole iff `c=4`, which then leaves a finite anomaly for all nearby positive depths | `tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy_sub_counterterm`, `thetaPhysicalEndpointPrimeHardyGreen_counterterm_cancels_iff` |
| actual conjugate quartet energy is twice one-copy residual energy plus a strictly positive height cross-term and hence exceeds eight off center | `thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy_eq`, `two_mul_integral_sq_thetaPhysicalEndpointHardyGreenResidual_lt_quartetEnergy`, `eight_lt_thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy` |
| neutral quartet energy is zero and global eight-unit quartet control is RH | `thetaPhysicalEndpointSymmetricQuartetHardyGreenEnergy_eq_zero_of_boundaryFlux_zero`, `thetaPhysicalEndpointSymmetricQuartetHardyGreenEightBound_iff_riemannHypothesis` |
| full constant two-copy reflection incidence is exactly `(α-β)²` times original Route P packet energy | `thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_eq_sub_sq_mul_packetEnergy` |
| symmetric incidence annihilates every fibre; antisymmetric incidence amplifies packet energy by `4α²` | `thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_self_eq_zero`, `thetaPhysicalEndpointCompletedResponseCopyIncidenceBudget_neg_eq_four_mul_sq` |
| every fixed nonsymmetric copy incidence retains the pointwise Ward contract and is globally RH-equivalent | `thetaPhysicalEndpointCompletedResponseCopyIncidenceWardBoundAt_iff`, `thetaPhysicalEndpointCompletedResponseCopyIncidenceWardBound_iff_riemannHypothesis` |
| moving-horizon connection annihilates flat principal carrier and returns depth times twisted tail | `thetaMovingHorizonConnection_wardContinuousHalfDensityProfile`, `thetaMovingHorizonConnection_wardContinuousHalfDensityProfile_prime` |
| covariant prime energy is summable on every fibre and equals `d²` times prime Hardy--Green energy | `summable_thetaWardMovingHorizonCovariantPrimeEnergyTerm`, `thetaWardMovingHorizonCovariantPrimeEnergy_eq` |
| covariant energy is asymptotic to `4d` and extends to zero at wall | `tendsto_thetaPhysicalEndpointCovariantHardyGreenEnergy_div_depth`, `tendsto_thetaPhysicalEndpointCovariantHardyGreenEnergy` |
| finite covariant energy vanishes exactly at same-fibre neutrality and globally exactly under RH | `thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff`, `all_thetaWardMovingHorizonCovariantPrimeEnergy_eq_zero_iff_riemannHypothesis` |
| full analytic covariant doublet splits exactly into stable and unstable reflection channels | `thetaMovingHorizonAnalyticCovariantDoubletEnergy_eq_stable_add_unstable`, `thetaMovingHorizonConnection_sq_eq_stableAnalyticDoubletChannel` |
| unstable analytic channel is nonsummable at every nonzero grade; doublet admission is copywise neutrality and globally RH | `not_summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy`, `summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_at_iff_boundaryFlux_zero`, `all_summable_thetaMovingHorizonAnalyticCovariantDoubletEnergy_iff_riemannHypothesis` |
| strict-right Xi Hardy rate is half the theta depth, and its critically renormalized symmetric square is exactly the stable P-G34 profile | `primeDepthBVWoldXiCenteredRate_right_eq_two_mul_re`, `thetaXiRightHardySymmetricSquareProfile_eq` |
| source Hardy square agrees coefficientwise at every prime with the stable moving-horizon response, and every strict-right factor contributes positive finite energy | `thetaMovingHorizonConnection_right_prime_eq_sourceHardySquare`, `thetaWardMovingHorizonCovariantPrimeEnergy_right_pos` |
| squarefree-Möbius source extends to the full two-sided Hilbert range `u>-1/2`, with critical norm-square `(1+2u)⁻¹` | `summable_norm_sq_infiniteMobiusCriticalDampedSignedWeight_of_negHalf_lt`, `tendsto_norm_sq_infiniteMobiusCriticalTwoSidedDampedSignedWeightLp` |
| every negative aperture before the half-density wall is strictly expansive | `tendsto_norm_sq_twoSidedDamped_gt_one_of_negative` |
| exact finite normalization produces unit source vectors whose critical two-aperture Gram is the normalized Hardy kernel | `norm_sq_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp`, `tendsto_inner_infiniteMobiusCriticalTwoSidedUnitSignedWeightLp` |
| normalized Hardy loss is an exact square and unit overlap occurs exactly for equal apertures | `one_sub_mobiusCriticalTwoSidedUnitHardyGram`, `mobiusCriticalTwoSidedUnitHardyGram_eq_one_iff` |
| source Cayley discrepancy is literally the Xi Ward half-plane Cayley factor and is Pythagorean-complementary to normalized Hardy overlap | `xiWardHalfPlaneCayleyFactor_sourceApertures`, `sq_mobiusCriticalTwoSidedCayleyDiscrepancy_add_sq_unitHardyGram` |
| normalized Hardy saturation is exactly vanishing of the source Xi Ward Cayley coordinate | `mobiusCriticalTwoSidedUnitHardyGram_eq_one_iff_cayleyFactor_eq_zero` |
| Cayley discrepancy and normalized Hardy overlap are hyperbolic tangent and secant of source rapidity separation | `mobiusCriticalTwoSidedCayleyDiscrepancy_eq_tanh_rapidity_sub`, `mobiusCriticalTwoSidedUnitHardyGram_eq_inv_cosh_rapidity_sub` |
| normalized Möbius aperture is literally one Route R horizontal-boost orbit and carries constant split theta Green current | `mobiusCriticalTwoSidedHyperbolicPoint_relativeGauge`, `thetaGreenHyperbolicCurrent_mobiusCriticalTwoSidedHyperbolicPoint` |

## New obstruction law

Functional-equation reflection supplies the opposite boundary current automatically:

```text
F(q#) = -F(q),
F(q) + F(q#) = 0.
```

Thus reflected direct sums, paired traces, and supertraces can be boundary-neutral without proving
anything about RH.  A valid Route P producer must equalize incoming/outgoing intensities inside
each multiplicity-exact fibre; cancellation only after a reflected orbit is aggregated is
formally excluded.

The stronger square-fold theorem places both opposite-current vectors over the same `B²`
eigenvalue.  Therefore even zero boundary trace block by block on the folded Route P spectrum is
unconditional.  Positivity must be certified on the oriented `B` double cover before the
reflection quotient is taken.

Pointwise, Lean now proves more than the global spectrum/RH equivalence: a single squared theta
node is strictly positive real exactly when that copy's own Green current vanishes. This excludes
all orbit-aggregate criteria even when imposed separately on every folded `B²` node.

The monopole/dipole moment chart identifies this boundary form exactly with Route R's split
Hermitian source plane. Its horizontal boost preserves the Green current for every grade, while
the fixed positive Euclidean polarization is preserved for all vectors only at grade zero. Hence
P and R share one hyperbolic-gauge obstruction: intrinsic conserved boundary data cannot build
the missing positive polarization.

Theta source nevertheless fixes a canonical gauge-breaking target frame: quantile coordinate and
its rank-two boundary image are independent lightlike axes, normalized by one nonzero theta
dipole. Their positive axis energies balance under horizontal boost exactly at grade zero. Hence
open work is coefficient-faithful Euler--Gamma transport into this explicit frame, not discovery
of an abstract positive metric.

Physical comparison is sharper still: theta flux, Route R adjacent-depth Hodge mate, and literal
reflected degree-six Deninger boundary differ only by explicit strictly positive units and one
orientation reversal. Their nullity is the same copy by copy, and either source-boundary nullity
is exactly positivity of the associated Route P squared node. The remaining theorem is common
pre-divisor annihilation, not another comparison map.

The Route N/Kakutani polarization supplies the missing reflection-safe positive receiver. Minus
the Route N Krein current divided by centered grade has an explicit positive removable completion
at grade zero. Consequently every local Hellinger gap equals a strictly positive explicit unit
times squared theta Green flux. Reflection reverses signed flux but doubles this positive defect,
and summability over all primes is exactly same-fibre flux neutrality, hence individual Route P
node positivity. This does not prove summability: it isolates pre-divisor admission to this exact
Kakutani domain as the remaining source theorem.

This source theorem can be attacked at finite level. The polarization at every prime dominates
`c(q)/p`, where the explicit coefficient `c(q)` is strictly positive exactly when the theta current
is nonzero; reflection doubles this lower floor. Therefore a single upper bound, uniform over all
finite prime sets, forces same-fibre neutrality and node positivity. This replaces a vague
infinite-product admission request by an exact finite-prime Green/Gamma energy estimate and proves
that cofinal rearrangement cannot evade the obstruction.

The canonical FE--Schwarz source seam now supplies this finite energy literally. Its squared norm
is the theta polarization multiplied by the forced positive scale
`(log p)^2 p^|a(q)|`; division by that scale is exact and never divides by centered grade. Thus
coefficient-faithful source-to-theta transport is no longer open. The unresolved producer is a
genuine source-side uniform upper bound for normalized finite seam energies.

The off-center divergence is now classified to finite part. Every nonneutral oriented copy has
polarization equal to prime-harmonic mass minus an absolutely summable radial deficit, so its
finite-prime energy divided by reciprocal-prime mass converges to exactly one. Neutral copies have
limit zero; reflected nonneutral pairs have limit two. Horizontal displacement changes only the
summable correction. This quantized escape index is the source invariant that a valid operator,
Calkin, or Green producer must force to zero.

The quantized receiver is specifically an unsigned defect number. The balanced Toeplitz model with
the same escape multiplicity has zero Fredholm index and unsigned energy `2m`; on a nonneutral
reflected pair this unsigned energy is exactly the cofinal theta limit two. Any reflection-odd
integer index therefore loses the obstruction. Surviving source targets are invertibility, sector
equivalence, or simultaneous vanishing of both positive defect channels, not signed index zero.

The remaining obstruction is stronger than a failure of the identity prime matching. The
universal critical amplitude `p^(-1/2)` lies outside `ℓ²` over primes, whereas every nonneutral
twisted amplitude lies in `ℓ²`; arbitrary prime permutations preserve that ideal class. More
generally, subtracting any `ℓ²` correction leaves a non-`ℓ²` gap. Thus finite-support,
finite-dimensional, square-summable Gamma corrections and all coordinate relabelings are
formally excluded. A live producer must cancel a matching non-`ℓ²` principal symbol before
Hilbert completion or prove the action of a genuinely non-coordinatewise source operator.

The corpus's actual unit-double Euler source provides the tempting opposite symbol, but its fixed
coefficient has exactly wrong polarity. Normalized by prime log it is `-p⁻¹+2p⁻²`; adding it to
the Route P Hellinger defect gives a summable sequence exactly off center. This reversal survives
every trace-class correction. Therefore fixed diagonal principal subtraction hides nonneutral
fibres and makes the neutral fibre divergent. A successful source must make principal
cancellation grade-sensitive through a pre-evaluation Ward/range law, not append a fixed
counterterm after fibre scalarization.

Passing to the quotient by summable prime families yields a complete two-class law. Neutral gap
has class zero; every nonneutral gap has the universal harmonic class. For any fixed coefficient
`c` and any trace-class tail, the corrected family is summable only for `(t=0,c=0)` or
`(t≠0,c=-1)`. Hence zero is the unique fixed coefficient with correct Route P polarity, minus one
reverses it, and all other coefficients admit no fibre. The source must prove the original class
vanishes on actual Xi fibres or mix channels before this quotient; quotient translation cannot
produce RH.

Allowing the diagonal coefficient to vary with grade does not provide a regular escape. Universal
admission forces the discontinuous wall law `c(0)=0`, `c(t)=-1` for `t≠0`, regardless of
grade-dependent trace-class tails. Lean excludes every coefficient continuous at zero and hence
every analytic diagonal functional calculus. A surviving universal mechanism must be singular at
the wall or non-diagonal before fibre evaluation.

The singular survivor is now physically instantiated. Ratios of literal raw amplitudes in the
existing Möbius prime-normal source graph have oriented reflection profile `p^a-p⁻ᵃ`, and its
square multiplied by the explicit positive gauge `1/[p(1+p^|a|)^2]` is exactly the Route P local
Hellinger gap. Thus the source graph and Route P receiver are coefficient-exactly welded. Remaining
work is admission: a source Green/Ward theorem must uniformly bound finite packets of this literal
profile energy; the algebraic identity supplies no such bound by itself.

That remaining assertion is now a named finite theorem. Uniform boundedness of literal weighted
Möbius-profile energy over every finite prime packet at one divisor copy is equivalent to positivity
of its Route P squared node; imposing it on every copy is equivalent to RH. This removes all
ambiguity about completion and gives the producer a finite-stage proof obligation.

The existing adaptive codiagonal does not discharge that obligation. The canonical physical
half-density is exactly the oriented difference between the universal `p⁻¹ᐟ²` channel and its
twist, and its square is the packet-energy density. It is absolutely summable—and hence belongs to
the codiagonal's `AdaptivePrimeL1` domain—exactly when the divisor copy is already neutral. Global
domain admission is RH. Therefore the closed-range `ℓ¹` theorem is circular for this vector.
Surviving source work must act on finite packets through a quadratic Ward form or construct a
closable singular extension on the weak-`ℓ²` boundary before taking a completion.

Finite packets now expose the obstruction inside the actual adaptive arithmetic output. Their
Route P energy is bounded by packet `ℓ¹` mass, which the adaptive codiagonal's `3/4` lower bound in
turn controls by `(4/3)` times output norm. Uniform boundedness of those literal output norms is
therefore exactly same-fibre neutrality; off center they exceed every threshold. Global output
boundedness is RH. The live producer must create signed/coherent cancellation before the positive
arithmetic `ℓ¹` norm, or a quadratic Ward identity before absolute completion.

Signed scalar augmentation also cannot provide that cancellation. Every physical half-density
coefficient has the same real orientation on one divisor copy, while each exact adaptive Möbius
reader column stays within `1/4` of the common principal value `-1`. The signed scalar packet output
therefore retains at least `3/4` of total half-density mass and is cofinally unbounded off center.
Its uniform boundedness is copywise neutrality and globally RH. Any viable new channel must carry
opposite principal phase or a non-diagonal oscillation before the existing reader; its current
Möbius tail and reflection symmetrization cannot generate this.

The completed physical-endpoint coupling gives an exact non-diagonal receiver weld, but not the
missing estimate. Its row marginal is `log(p)/p`, and normalization by `sqrt(p/log(p))` makes the
marginal square Route P energy. Yet the identity `E_F=Q_F+(1/2)D_F` holds for every symmetric
coupling with that marginal. Subtracting diagonal marginal leaves a zero-row-sum gauge satisfying
`Q_K+(1/2)D_K=0`; completed-kernel data cancels completely. On arbitrarily late positive
adjacent-prime edges this gauge is a negative graph Laplacian, so it has strict negative quadratic
directions while its Dirichlet form is strict positive. No generic sign choice survives. A useful
sign must be theta/entire-specific and restricted to source packets.

Endpoint normalization exposes a sharper cross-route invariant. At centered depth `d`,
`log(p)phi_p²=(1-p⁻ᵈ)²`, whose prime trace is zero at the wall and one everywhere off it. The
missing tail `2sqrt(2)e⁻ᵈˣ` has exact continuous energy `4/d=2/|Im rho|`, equal to exceptional
Hardy--Green energy and four times Route R's transverse Cauchy self-energy. Every exceptional copy
therefore exceeds four; imposing a global four-unit bound is exactly RH, not an unconditional
estimate.

Physical prime sampling recovers this singularity without coefficient loss. Its energy is
`8 sum_p log(p)p^(-1-2d)=8 Re P_log(1+2d)`. The prime-log pole decomposition proves
`d E_prime(d)->4` and `(d/4)E_prime(d)->1`. Thus discrete prime clock and continuous half-line
Hardy--Green geometry encode the same exceptional pole. Remaining producer must use a literal
theta-entire or pole-order cancellation to remove that residue before positive completion, or
exclude the exceptional mode directly; marginal algebra and generic critical-clock bounds cannot.

The pole has a complete principal-class no-go. Exactly
`E_prime(d)=4/d+A(d)`, with
`A(d)=8 Re(zetaLogDerivReg(1+2d)-primeHigher(1+2d))` continuous at zero. For scalar counterterm
`c/d`, the scaled remainder tends to `4-c`, so coefficient four is uniquely forced. Yet that unique
subtraction leaves a finite limit for every positive depth approaching the wall. This is the same
selector failure as the diagonal `0/-1` trichotomy in a new coordinate: scalar principal
cancellation cannot distinguish actual neutral Xi fibres from arbitrary nearby radial depths.

Height-phase coherence does not repair this failure inside positive divisor assembly. For actual
conjugate right-half pair the finite Cauchy Gram is twice one-copy residual energy plus the strictly
positive cross-term `4a/(a²+gamma²)`. Every exceptional quartet therefore exceeds eight, while a
neutral quartet has zero energy. Functional-equation/conjugation completion with positive
multiplicities amplifies exceptional pole. Any cancellation must carry signed pre-divisor data or
annihilate mode before positive Gram completion.

The complete constant signed alternative is now classified. The moving-horizon physical carrier
is reflection-odd, so after including the missing mixed-copy response and Dirichlet terms, copy
coefficients `α,β` produce exactly `(α-β)²` times original packet energy. Symmetric incidence kills
all fibres without information; every nonsymmetric incidence retains exact RH-equivalent Ward
obstruction. Reflection copy space therefore has no constant coefficient capable of selecting
critical grade. Any live cancellation must use arithmetic/theta-dependent incidence before the
reflection quotient or annihilate the antisymmetric source mode itself.

Covariant moving-horizon differentiation supplies a genuine positive survivor. It annihilates the
flat universal carrier before quadratic completion and multiplies twisted tail by centered depth.
Resulting logarithmically weighted prime energy is summable for every divisor copy and exactly
`d²` times prime Hardy--Green energy. Thus sharp wall law is `4d`, not `4/d`; energy is zero exactly
on neutral fibres and strictly positive on exceptional ones. Route P therefore now has a regular
finite source detector with correct polarity. Missing theorem is unconditional
theta-entire/completed-source vanishing of this detector, rather than construction of another
receiver, extension of singular domain, or subtraction of principal pole.

That survivor has a sharp provenance obstruction. P-G34 selects decaying branch
`p^(-1/2-|t|)`, whereas reflection-entire source carries both analytic branches. Covariant positive
doublet decomposes as `t²p^(-1-2|t|)+t²p^(-1+2|t|)`; unstable term is prime-harmonic-or-worse for
every nonzero `t`. Full analytic doublet is therefore summable only at neutral grade. Route P
cannot obtain finite positive response from entireness alone. At P-G35, missing structure was a
literal theta/Gamma stable or Hardy projection switching branch under reflection without reading
zero grade, followed by source trace vanishing of selected finite response. P-G36 closes the
projection clause below.

That missing projection is now source-constructed. The strict-right Xi canonical product supplies
an anti-causal Paley--Wiener ray whose critical half-density-renormalized symmetric square is
exactly P-G34's stable profile. Theta depth is twice the real Hardy decay, explaining the former
factor-two mismatch. Prime sampling and moving-horizon connection agree coefficientwise, so every
strict-right source factor deposits positive finite covariant energy. The open theorem is no
longer projection provenance; it is completed-source saturation/vanishing of this literal factor.

Attempting to obtain saturation from reversible source contractivity yields a sharp no-go and a
new positive geometry. Raw Möbius damping extends to `u>-1/2`, but its critical norm-square is
`(1+2u)⁻¹`; negative aperture is strictly expansive. Exact mass-ratio normalization produces unit
vectors, yet their normalized Hardy overlap is strictly below one off the diagonal, with loss an
explicit square. Scalar normalization preserves displacement as Hilbert angle.

The resulting angle is exactly the Xi Ward Julia defect. In half-density coordinates the
complementary Cayley discrepancy is a literal `xiWardHalfPlaneCayleyFactor`, and its square plus
the normalized Hardy overlap square is one. This unifies Möbius source loss, Xi Ward contraction,
and Route P stable response in one Julia cell. A producer must force the actual source Cayley
coordinate to zero before divisor/reflection aggregation; contractivity, unit normalization, and
positive completion only repackage that coordinate.

The Julia cell is exactly the already formalized P/R hyperbolic gauge orbit. Source aperture has
rapidity `log sqrt(1+2u)`; Cayley and Hardy coordinates are its hyperbolic tangent and secant. Its
canonical two-sector point is obtained by Route R horizontal boost, and the common split theta
current is constant on the full curve. Hence P and R do not merely share a qualitative external
polar problem. They share the same normalized source orbit. Any successful source law must break
that orbit in the fixed positive frame; an intrinsic current identity cannot distinguish neutral
rapidity.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaGreenSquareBoundaryLaw.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaGreenSquareBoundaryLaw
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaGreenReflectionPairNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaGreenReflectionPairNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaGreenHyperbolicGaugeNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaGreenHyperbolicGaugeNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaRouteRPositiveUnitCurrentBridge.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaRouteRPositiveUnitCurrentBridge
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniFluxPolarization.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniFluxPolarization
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniHarmonicCoercivity.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniHarmonicCoercivity
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrimeSeamPolarizationBridge.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeSeamPolarizationBridge
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniQuantizedEscape.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniQuantizedEscape
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniBalancedIndexNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniBalancedIndexNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaKakutaniPermutationSectorNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKakutaniPermutationSectorNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrincipalCountertermPolarityNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrincipalCountertermPolarityNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrincipalClassTrichotomy.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrincipalClassTrichotomy
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaContinuousPrincipalRenormalizationNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaContinuousPrincipalRenormalizationNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalProfileBridge.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalProfileBridge
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalWardContract.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalWardContract
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalCodiagonalPacketBlowup.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalCodiagonalPacketBlowup
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusPrimeNormalScalarReaderPacketBlowup.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalScalarReaderPacketBlowup
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointCompletedResponseWardBridge.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointCompletedResponseWardBridge
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaCompletedResponseMarginalGaugeNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompletedResponseMarginalGaugeNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointLogarithmicBoundaryLaw.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointLogarithmicBoundaryLaw
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointHardyGreenResidualBridge.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointHardyGreenResidualBridge
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaCompletedResponseCofinalGaugeNegativity.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompletedResponseCofinalGaugeNegativity
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointPrimeHardyGreenScaling.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointPrimeHardyGreenScaling
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointPrimeHardyGreenRenormalizationNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointPrimeHardyGreenRenormalizationNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPhysicalEndpointSymmetricQuartetHardyGreenNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointSymmetricQuartetHardyGreenNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMovingHorizonReflectionIncidenceTrichotomy.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMovingHorizonReflectionIncidenceTrichotomy
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMovingHorizonCovariantHardyGreenRegularization.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMovingHorizonCovariantHardyGreenRegularization
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMovingHorizonAnalyticDoubletNoGo.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMovingHorizonAnalyticDoubletNoGo
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaXiHardySymmetricSquareWeld.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaXiHardySymmetricSquareWeld
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusTwoSidedApertureWall.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusTwoSidedApertureWall
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusUnitHardyGramRigidity.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusUnitHardyGramRigidity
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSourceJuliaPythagoras.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceJuliaPythagoras
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaMobiusHyperbolicRapidity.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusHyperbolicRapidity
```

All sixty-eight commands pass. `/tmp` `#print axioms` audits for every declaration above report only
`propext`, `Classical.choice`, and `Quot.sound`.

Target modules are reachable from `RHTower.lean` and exact module builds pass. Global formal lint
is presently blocked by pre-existing unreachable RHTower/Sieve and HTGeometry modules; none of the
thirty-four modules in this certificate is reported.
