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

## Canonical maximal quotient and physical collapse

| Manuscript claim | Formal support |
|---|---|
| Minimal admissible boundary is `range D ⊔ range (T ∘ D)`, contains all defects, is target-stable, and lies in every competing stable defect boundary | `RHTower/MobiusThetaSourceDaggerMinimalBoundaryLaw.lean`: `cyclicParacyclicMinimalDefectBoundary`, `cyclicParacyclicEquivarianceDefect_mem_minimalBoundary`, `cyclicParacyclicMinimalDefectBoundary_target_stable`, `cyclicParacyclicMinimalDefectBoundary_le` |
| An atom survives some admissible boundary quotient iff it survives the minimal one | same module: `not_mem_cyclicParacyclicMinimalDefectBoundary_iff_exists` |
| Away from unit monodromy the entire landing range lies in the minimal boundary; for a surjective landing the boundary is top | same module: `land_mem_cyclicParacyclicMinimalDefectBoundary_of_monodromy_ne_one`, `cyclicParacyclicMinimalDefectBoundary_eq_top_of_surjective` |
| Physical two-leg landing is scaling by the first nonzero Möbius–theta/Xi jet, hence is surjective and retains the exact multiplicity grade | same module: `thetaInternalJetLeadingTwoLegLanding`, `thetaInternalJetLeadingTwoLegLanding_surjective`, `thetaInternalJetLeadingSourceAtom_landing_eq_multiplicityJet` |
| Physical minimal boundary is bottom on the critical line and top off it | same module: `thetaInternalJetSourceDaggerMinimalBoundary_eq_bot_of_re_eq_half`, `thetaInternalJetSourceDaggerMinimalBoundary_eq_top_of_re_ne_half` |
| Canonical physical quotient class is nonzero iff `Re rho = 1/2`; global survival iff RH | same module: `thetaInternalJetLeadingSourceBoundaryClass_ne_zero_iff`, `thetaInternalJetSourceDaggerBoundaryClassSurvives_iff_riemannHypothesis` |

## Literal cyclic comparison and residue transgression

| Manuscript claim | Formal support |
|---|---|
| Literal degree-one rational-adelic cyclic source and genuine rotation/trace exist; trace is rotation-invariant | `RHTower/MobiusThetaSourceDaggerMinimalBoundaryLaw.lean`: `CCMRationalAdelicDegreeOneCyclicSource`, `ccmRationalAdelicDegreeOneCyclicRotation`, `ccmRationalAdelicDegreeOneTrace`, `ccmRationalAdelicDegreeOneTrace_rotate` |
| For every ordinary prime, the canonical `p ⊗ p⁻¹` crossed-product cycle has trace exactly one | same module: `ccmRationalAdelicOrdinaryPrimeCycleAtom`, `ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one` |
| Pre-divisor ordered comparison maps every prime cycle to the physical source atom `(1,0)` | same module: `ccmRationalAdelicOrderedTwoLegComparison`, `ccmRationalAdelicOrderedTwoLegComparison_primeCycle` |
| Coordinate-sum cyclic residue kills the untwisted cyclic comparison defect | same module: `ccmRationalAdelicTwoLegCyclicResidue`, `ccmRationalAdelicTwoLegCyclicResidue_cyclicDefect_eq_zero` |
| Global comparison exists for every independent jet grade, physical rung, and spectral parameter; it converges to the Xi-jet landing at every divisor and specializes at multiplicity to physical landing (6.8) | same module: `ccmMobiusThetaFilteredTwoLegLanding`, `ccmMobiusThetaXiJetTwoLegLanding`, `tendsto_ccmMobiusThetaFilteredTwoLegLanding_primeCycle_at_divisor`, `ccmMobiusThetaXiJetTwoLegLanding_eq_physicalLeadingLanding` |
| Multiplicity stays filtered: residue is zero below support multiplicity and nonzero at support multiplicity, without a unitary Jordan premise | same module: `ccmMobiusThetaXiJetTwoLegResidue_eq_zero_before_supportMultiplicity`, `ccmMobiusThetaXiJetTwoLegResidue_ne_zero_at_supportMultiplicity` |
| Physical prime-cycle atom is detected by source residue | same module: `ccmRationalAdelicTwoLegCyclicResidue_physicalPrimeCycle_ne_zero` |
| Exact physical transgression is `Res(D x) = (δ-1)cρ ε₀¹(x)` | same module: `ccmMobiusThetaTwoLegParacyclicDefect_residue` |
| Constructed source residue annihilates physical `B_min,ρ` iff `Re rho = 1/2`; global annihilation iff RH | same module: `ccmMobiusThetaSourceResidueAnnihilatesMinimalBoundary_iff`, `ccmMobiusThetaSourceResidueAnnihilatesEveryMinimalBoundary_iff_riemannHypothesis` |
| Any linear residue annihilating `B_min,ρ` and detecting `Lρ(x₀)` forces `Re rho = 1/2` | same module: `re_eq_half_of_residue_annihilates_minimalBoundary_and_detects` |

## Completion no-gos

| Manuscript claim | Formal support |
|---|---|
| Product-topology closed relation retaining all finite prime blocks is maximally vertical and equals domain times full output | `RHTower/CompleteResolutionCofinalConditioningLaw.lean`: `completeResolution_closedLinearRelation_countablePrime_affine_fullVertical`, `linearRelation_eq_domain_prod_of_fullVertical`, `completeResolution_closedLinearRelation_countablePrime_affine_eq_domain_prod`, `completeResolution_countablePrime_topologyAlternative`, `completeResolution_countablePrime_informative_forces_strictTopology` |
| Actual cross-prime arithmetic source span is dense in completed packet | `RHTower/DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion.lean`: `deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_denseRange` |
| Old oriented boundary kills actual cross-prime source span; every continuous extension is zero | same module: `deningerCalderonWittGlobalOrientedBoundary_crossPrimeSourceSpan`, `deningerCalderonWittCrossPrimeContinuousOrientedBoundaryExtension_eq_zero` |
| Relative Calderón--Witt class is exactly Green primitive escape from admitted sector | `RHTower/DeningerCalderonWittRelativeBoundaryTransgression.lean`: `deningerCalderonWittRelativeBoundaryClass_eq_zero_iff`, `deningerCalderonWittGlobalRelativeBoundaryClass_eq_zero_iff` |
| Every regular orientation-blind consumer factors through one orientation trace; no third regular source channel | `RHTower/DeningerCalderonWittOrientationTransgressionCompleteness.lean`: `deningerCalderonWittOrientationTransgressionCompleteness`, `deningerCalderonWittGlobalOrientationTransgressionCompleteness` |

## Explicitly unproved

Literal source, pre-divisor comparison, source residue, ordinary-prime detection, and separate
multiplicity filtration are now constructed. The only unproved content is a source theorem making
the **physical paracyclic defect** null-homologous in the literal arithmetic cyclic complex (or
otherwise proving its source residue zero) before divisor specialization. Exact status:

- `ccmMobiusThetaTwoLegParacyclicDefect_residue` computes that residue as
  `(δ_n(rho)-1) c_rho ε₀¹(x)`;
- on the explicit ordinary-prime cycle, `ε₀¹(x)=1` and `c_rho ≠ 0`, so source-null-homology would
  force `δ_n(rho)=1`;
- `ccmMobiusThetaSourceResidueAnnihilatesMinimalBoundary_iff` proves pointwise boundary
  annihilation is exactly critical-line placement;
- `ccmMobiusThetaSourceResidueAnnihilatesEveryMinimalBoundary_iff_riemannHypothesis` proves global
  annihilation is exactly RH;
- no theorem proves physical source-null-homology or RH, and no declaration assumes either.

Thus the construction closes infrastructure and replaces the former vague comparison gap by one
exact RH-bearing homology statement. It must not be reported as an outstanding routine lemma.
