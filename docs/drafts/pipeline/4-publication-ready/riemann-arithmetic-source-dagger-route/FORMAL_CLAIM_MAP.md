# Formal claim map

Manuscript: `Arithmetic source descent toward the Riemann hypothesis`

This file is external to manuscript. It records exact formal support and prevents conditional
interfaces from being reported as constructed mathematics.

## Universal descent law

| Manuscript claim | Formal support |
|---|---|
| Serial source conservativity is equivalent to conservativity of each edge on propagated source sector | `HTGeometry/SourcePointedConservativityChainLaw.lean`: `isConservativeOn_comp_iff`; quantitative form `isUniformlyConservativeOn_comp` |
| Resolved finite packet vanishes grade by grade; every nonzero term has same-full-grade mate; coarsened zero witnesses grade collision | `HTGeometry/ResolvedGradeConservationLaw.lean`: `resolvedGradePacket_eq_zero_iff`, `exists_sameGrade_mate_of_resolvedGradePacket_eq_zero`, `exists_gradeCollision_of_coarsenedPacket_eq_zero` |
| Principal responses of different degrees cannot be treated as one signed cancellation before grade coarsening | same module: `principalDefectResponse_mul`, `principalDefectResponse_eq_zero_iff`, `principalDefectResponse_neg_of_even`, `principalDefectResponse_neg_of_odd` |

## Physical Möbius--theta source and Xi landing

| Manuscript claim | Formal support |
|---|---|
| Target-free physical Möbius--theta source exists in `L²`; source sums and complete cofaces are summable | `RHTower/MobiusThetaPhysicalSourceToXiLanding.lean`: `summable_mobiusThetaRungTerm_of_three_le`, `mobiusThetaDirectPhysicalRung_eq_mobiusThetaRung`, `summable_norm_mobiusThetaCompletePhysicalChannel_three`, `summable_mobiusThetaCompletePhysicalChannel_three` |
| Complex Fourier--Laplace transform is reciprocal-zeta multiplier times `XiC` | `RHTower/MobiusThetaComplexSourceToXiLanding.lean`: `mobiusThetaFourierLaplace_eq_invZeta_mul_XiC` |
| Internally promoted source lands in every Xi jet with same multiplier | `RHTower/MobiusThetaInternalJetSourceToXiLanding.lean`: `mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC`; complete-channel identity `mobiusThetaInternalJetCompleteChannelFourierLaplace_eq`; telescoping `sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace` |
| Cofinal source converges to exact Xi jet at every divisor, retains first nonzero multiplicity jet | `RHTower/MobiusThetaInternalJetCofinalComplexLanding.lean`: `tendsto_mobiusThetaInternalJetFourierLaplace_cofinal_at_divisor`, `tendsto_sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace_at_divisor`, `mobiusThetaInternalJetCofinalLanding_retains_supportMultiplicity` |
| Division-free leading conormal lands as `(0, XiC^(r))` and second coordinate is nonzero | same module: `mobiusThetaInternalJetConormalPair_leading_vertical_at_divisor` |
| Complete positive resolution is `ℓ¹`, has coordinate sum one, and contains a channel preserving analytic order | `RHTower/CompleteResolutionSummableConormalLanding.lean`: `completeResolution_summable_conormalLanding`, `completeResolution_safe_summable_conormalLanding` |

## Completed Hellinger--Gamma/Calderón--Witt incidence

| Manuscript claim | Formal support |
|---|---|
| Leading physical source coefficient is first nonzero Xi jet and never vanishes | `RHTower/MobiusThetaInternalJetCompletedHellingerGammaIncidenceBridge.lean`: `thetaInternalJetLeadingSourceCoefficient_eq`, `thetaInternalJetLeadingSourceCoefficient_ne_zero` |
| Completed incidence coefficient equals physical source coefficient; incidence is nonzero at every divisor stalk | same module: `thetaInternalJetLeadingCompletedIncidence_coefficient`, `thetaInternalJetLeadingCompletedIncidence_ne_zero` |
| Decoding equals physical coefficient times actual Gamma witness | same module: `thetaInternalJetLeadingCompletedIncidence_sourceValue` |
| Joined unsquared Hodge trace is physical coefficient times Gamma trace and vanishes iff displacement is zero | same module: `thetaInternalJetLeadingGaugedPureHodgePrimitive_trace_eq`, `thetaInternalJetLeadingGaugedPureHodgePrimitive_trace_eq_zero_iff` |
| Completed Hellinger cofaces recover physical landing for every real modular displacement | same module: `thetaInternalJetLeadingCompletedIncidence_cofaceRecovery_tendsto` |
| Normalized Hodge marginal graph has vertical closure point `(0,1)` and is not closed | `RHTower/MobiusThetaInternalJetHellingerGammaNormalizedVerticalRelation.lean`: `thetaInternalJetHellingerGammaNormalizedBoundary_vertical_mem_closure`, `thetaInternalJetHellingerGammaNormalizedBoundaryGraph_not_isClosed` |

## Reflected Green transport and atomic non-erasure

| Manuscript claim | Formal support |
|---|---|
| Reflected adaptive reader satisfies distance-to-`-1` at most `1/4`, hence modulus between `3/4` and `5/4` | `RHTower/MobiusThetaAdaptivePrimeNormalReflectedGreenSource.lean`: `norm_adaptivePrimeNormalReflectedReader_add_one_le_quarter`, `adaptivePrimeNormalReflectedReader_lower`, `adaptivePrimeNormalReflectedReader_upper` |
| Reflected horizon multiplier is invertible, with forward norm at most `5/4`, inverse norm at most `4/3`, and lower modulus `3/4` | same module: `adaptivePrimeNormalReflectedHorizonInverse_forward`, `adaptivePrimeNormalReflectedHorizonForward_inverse`, `norm_adaptivePrimeNormalReflectedHorizonForward_le`, `norm_adaptivePrimeNormalReflectedHorizonInverse_le`, `adaptivePrimeNormalReflectedHorizonForward_lower` |
| It commutes with completed source Green reflection and harmonic Hodge | same module: `deningerArithmeticCompletedSourceGreen_reflectedHorizonForward`, `deningerXiHarmonicHodge_reflectedHorizonForward` |
| Every reflected horizon coordinate is nonzero | same module: `adaptivePrimeNormalReflectedHorizonColumn_apply_ne_zero` |
| Local Green coefficient vanishes iff divisor is on critical line; global provenance vanishes iff RH | same module: `adaptivePrimeNormalReflectedHorizonGreenCoefficient_eq_zero_iff`, `adaptivePrimeNormalReflectedHorizonGreenProvenance_eq_zero_iff_riemannHypothesis` |

## Cyclic--paracyclic boundary-defect law

| Manuscript claim | Formal support |
|---|---|
| Target degree-one rotation squares to half-density mate gain | `RHTower/SourceDaggerCyclicMonodromyRigidity.lean`: `sourceDaggerNormalizedDegreeOneRotation_sq` |
| For arbitrary landing, two-step target/source square mismatch is exactly sum of two transported equivariance defects | `HTGeometry/CyclicParacyclicBoundaryDefectLaw.lean`: `cyclicParacyclicEquivarianceDefect_twoStep`, `cyclicParacyclicEquivarianceDefect_twoStep_apply` |
| Equivariance modulo a target-stable boundary plus one retained quotient class forces scalar monodromy one | same module: `retainedCyclicClass_forces_monodromy_one` |
| Away from monodromy one, every strict single-valued cyclic-to-paracyclic landing is zero, independently of topology | same module: `strictCyclicParacyclicLanding_eq_zero_of_monodromy_ne_one` |
| Source--dagger boundary class forces `Re s = 1/2`; strict landing is zero off line | `RHTower/SourceDaggerCyclicBoundaryDefectLaw.lean`: `re_eq_half_of_sourceDaggerCyclicBoundaryClass`, `sourceDaggerStrictCyclicLanding_eq_zero_of_re_ne_half` |
| One global boundary-class landing on every Xi divisor fibre implies RH | same module: `riemannHypothesis_of_sourceDaggerCyclicBoundaryClassLanding` |
| Mate gain is `exp ((2 Re s - 1) log n)` | `RHTower/DeningerOneSidedFramedMateCurvatureTransgression.lean`: `deningerHalfDensityMateGain`, `deningerHalfDensityMateGain_eq_norm_inv_sq` |

## Completion no-gos

| Manuscript claim | Formal support |
|---|---|
| Product-topology closed relation retaining all finite prime blocks is maximally vertical and equals domain times full output | `RHTower/CompleteResolutionCofinalConditioningLaw.lean`: `completeResolution_closedLinearRelation_countablePrime_affine_fullVertical`, `linearRelation_eq_domain_prod_of_fullVertical`, `completeResolution_closedLinearRelation_countablePrime_affine_eq_domain_prod`, `completeResolution_countablePrime_topologyAlternative`, `completeResolution_countablePrime_informative_forces_strictTopology` |
| Actual cross-prime arithmetic source span is dense in completed packet | `RHTower/DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion.lean`: `deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_denseRange` |
| Old oriented boundary kills actual cross-prime source span; every continuous extension is zero | same module: `deningerCalderonWittGlobalOrientedBoundary_crossPrimeSourceSpan`, `deningerCalderonWittCrossPrimeContinuousOrientedBoundaryExtension_eq_zero` |
| Relative Calderón--Witt class is exactly Green primitive escape from admitted sector | `RHTower/DeningerCalderonWittRelativeBoundaryTransgression.lean`: `deningerCalderonWittRelativeBoundaryClass_eq_zero_iff`, `deningerCalderonWittGlobalRelativeBoundaryClass_eq_zero_iff` |
| Every regular orientation-blind consumer factors through one orientation trace; no third regular source channel | `RHTower/DeningerCalderonWittOrientationTransgressionCompleteness.lean`: `deningerCalderonWittOrientationTransgressionCompleteness`, `deningerCalderonWittGlobalOrientationTransgressionCompleteness` |

## Explicitly unproved

Manuscript Problem 8.2 (`Arithmetic boundary-class law`) is **not constructed**. In particular:

- no global source-generated target-stable arithmetic boundary submodule has been identified;
- no theorem proves the physical Möbius--theta source--dagger equivariance defect lies in that
  boundary on the unsymmetrized top-conormal grade;
- existing atomic non-erasure proves a target vector is nonzero, not that its quotient class is
  nonzero modulo the missing boundary;
- `SourceDaggerCyclicBoundaryDefectLaw.lean` is a consumer with explicit boundary stability,
  defect exactness, and quotient non-erasure hypotheses;
- reflected Green commutation is even under functional-equation reflection and is not the
  missing same-fibre mixed rotation;
- local completed Gamma incidence is coefficient-faithful but does not prove global
  source--dagger boundary exactness;
- no RH theorem is claimed.

The two boundary-defect modules were added for the new universal identity, strict obstruction,
boundary-class rigidity, and conditional global consumer. They do not assume or construct any of
the three missing arithmetic clauses.
