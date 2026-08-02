# Formal claim map

Paper: `Transverse information at singular descent`  
Scope: load-bearing mathematical claims only.  Manuscript contains no mention of formalization.

| Manuscript result | Unconditional theorem/module |
|---|---|
| Resolved-defect conservation and antidiagonal kernel | `HTGeometry/ResolvedDefectConservationLaw.lean`: `resolvedDefectCodiagonal_comp_factoredResolvedCovarianceDefect`, `ker_resolvedDefectCodiagonal_eq_range_antidiagonal`, `resolvedPair_eq_zero_of_disjoint_of_add_eq_zero` |
| Closed collapsing graph limits enter vertical fibre | `RHTower/CompleteResolutionCofinalConditioningLaw.lean`: `closedLinearRelation_mem_vertical_of_tendsto_zero`, `closedLinearRelation_mem_vertical_of_graph_tendsto`, `closedLinearRelation_span_le_verticalFiber_of_cofinalCollapse` |
| Dense graph limits force full verticality and domain-product relation | same module: `closedLinearRelation_fullVertical_of_dense_graph_limits`, `linearRelation_eq_domain_prod_of_fullVertical`; arithmetic instances include `completeResolution_closedLinearRelation_countablePrime_affine_eq_domain_prod` |
| Complete source collapse and injective two-prime blow-up | `CompleteResolutionCofinalConditioningLaw.lean`: `completeResolution_collapseBlowup_duality`, `completeResolutionCofinalBlowupLimit_injective`, `no_uniformLipschitz_completeResolutionCofinalBlowupChart_pair` |
| Prime-normal packet tends to zero and has dense span | `CompleteResolutionPrimeNormalHilbertSaturation.lean`: `tendsto_completeResolutionPrimeHilbertPacket_zero`, `completeResolutionPrimeHilbertPacketSpan_closure_eq_top`, `completeResolutionPrimeHilbertAffinePacketSpan_closure_eq_top` |
| Every infinite packet subsequence and affine centering is dense | `CompleteResolutionPrimeNormalFiniteFibreGrading.lean`: `completeResolutionPrimeHilbertPacketSpanOn_closure_eq_top`, `completeResolutionPrimeHilbertAffinePacketSpanOn_closure_eq_top` |
| Closed gradewise-proper carrier exists iff every grade fibre is finite | same module: `completeResolutionPrimeHilbert_exists_closed_gradewiseProperCarrier_iff` |
| Hypertranscendental divisor information localization | `HypertranscendentalDivisorInformationLocalizationLaw.lean`: `hypertranscendentalDivisorInformationLocalization_law` |
| Physical internally promoted theta source lands in Xi jets | `MobiusThetaInternalJetPhysicalGraph.lean`: `fourier_xiThetaInternalJetSchwartzSource`, `tendsto_fourier_sum_range_mobiusThetaInternalJetCompletePhysicalChannel` |
| Local Xi multiplicity matrix is nonsingular | `MobiusThetaInternalJetSourceLocalSpanning.lean`: local matrix diagonal/full-rank theorems |
| Euler valuation disintegration and Fisher variance | `EulerActivationSquarefreeDisintegration.lean`: local valuation-law, conditional-geometric, and parity-variance theorems |
| Reflected shell entropy equals signed horizontal displacement | `XiSourceBoundaryOrientationConservation.lean`: `reflectedShellTailLogRatio_eq_centeredHorizontalDisplacement`, `riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate` |
| Source entropy equals multiplicity-weighted Xi charge | same module: `centeredDivisorCharge_real_eq_reflectedShellTailLogRatio` |
| Nearby-cycle outer charge equals completed Xi affine residue | `XiDepthMobiusGammaOuterInnerWeld.lean`: `xiDepthNearby_outerCharge_and_affineResidue_match` |
| Additive boundary fracture equals twice centered real part | `XiSourceModularTypeSuperselectionLaw.lean`: `xiNearbyPoleDualityAdjunctionFracture_eq_two_re`, `xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff` |
| Hyperbolic invariant quadratic forms and positive metric no-go | same module: `reflectedRealCharacter_invariantQuadratic_iff`, `reflectedRealCharacter_no_nonzero_positiveInvariantQuadratic` |
| Faithful equivariant norm-conservative descent forces zero rate | same module: `normConservative_equivariantDescent_forces_zero` |
| Green factor defects are exact antidiagonal partners; resolved vanishing iff critical line/RH | `DeningerGreenResolvedDefectLaw.lean`: resolved Green defect theorems and global RH equivalence |
| No finite-Rees sewing; exact sewing cost beyond every order | `XiSourceModularTypeSuperselectionLaw.lean`: `no_finiteReesOperator_sews_xiRightModularSectors`, `xiRightModularSewingOperatorNorm_beyondEveryReesOrder` |
| Every Xi zero occurs in Meyer dual flow with full multiplicity | `DeningerMeyerXiSpectralInclusion.lean`: `deningerMeyerXiSupportJetEvaluationLM_linearIndependent`, `deningerMeyer_every_xiDivisor_is_flowEigenvalue` |
| Every finite family of actual Xi jets is a surjective Meyer quotient | `DeningerMeyerFiniteXiJetPacket.lean`: `deningerMeyerFiniteXiJetPacketLM_surjective` |
| Full unrestricted Xi jet product is not source-admissible | `DeningerMeyerFullXiJetAdmissionBoundary.lean`: `deningerMeyerFullXiJetUnitPacket_not_mem_range`, `deningerMeyerFullXiJetPacketLM_not_surjective` |
| Escaping actual divisor sequence and vertical decay | same module: `deningerMeyerXiVerticalEscape_abs_im_tendsto_atTop`, `deningerMeyerStrongLogMellin_tendsto_zero_on_xiVerticalEscape` |
| Cofinal unit synthesis singular at every positive differential order | `DeningerMeyerXiCofinalSynthesisSingularity.lean`: `exists_deningerMeyerXiCofinalUnitSynthesis`, `deningerMeyerXiCofinalUnitSynthesis_cost_gt_pow` |
| Pointwise Xi-nonerasing regular comparison may erase every reflection displacement | `DeningerMeyerPointwiseXiComparisonSharpness.lean`: `deningerMeyerPointwiseXiComparison_nonzero_on_support`, `deningerMeyerPointwiseXiComparison_erases_reflection`, `deningerMeyerPointwiseXiComparison_firstOrderRegular` |
| Meyer reciprocal operator descends | `DeningerMeyerPaugamJDescent.lean` and `DeningerMeyerStrongLogTarget.lean`: reciprocal descent/involution theorems |
| Complementary-jet Paugam form and exact weight-one flow | `DeningerMeyerPaugamGeneralizedJetPairing.lean`: `deningerMeyerPaugamGeneralizedJetPairing_flow`, skew/J laws |
| Positive reciprocal Calderón form has zero radical locally | `DeningerMeyerReciprocalPaugamPolarization.lean`: `deningerMeyerPoissonReciprocal_cupSigma_self`, `deningerMeyerPoissonReciprocal_cupSigma_eq_zero_iff` |
| Local reciprocal positive form pulls back to zero on genuine global middle cycles | `DeningerMeyerPaugamGradingObstruction.lean`: `deningerMeyerEndpointCycleReciprocalQuotient_eq_zero`, `deningerMeyerEndpointCycleReciprocal_cupSigma_self_zero` |
| Meyer-to-Xi spectral synthesis is exactly comparison injectivity | `DeningerMeyerXiSpectralInclusion.lean`: `deningerMeyerCompactOpenXiComparison_injective_iff` |
| Positive admissible completed dual spectrum implies RH | `DeningerMeyerPositiveAdmissibleCompletionFrontier.lean`: `normConservative_centeredXiCharacter_forces_re_half`, `riemannHypothesis_of_deningerMeyerPositiveAdmissibleDualSpectrum` |
| Finite invariant domination of a nonzero eigenfunctional exists iff character has zero real rate | `TransverseInformationInvariantGaugeDichotomy.lean`: `invariantGauge_bounded_eigenfunctional_iff_re_eq_zero`; forward implication also `DeningerMeyerInvariantEvaluationGaugeFrontier.lean`: `re_eq_zero_of_invariantGauge_bounded_eigenfunctional` |
| Canonical half-density source and quotient seminorm are exactly centered-flow invariant | `DeningerMeyerHalfDensityL1Completion.lean`: `deningerMeyerHalfDensityL1Seminorm_centeredFlow`, `deningerMeyerHalfDensityCohomologySeminorm_centeredFlow` |
| Half-density seminorm completion carries a surjective isometric centered flow | same module: `deningerMeyerHalfDensityCompletedFlow_norm`, `deningerMeyerHalfDensityCompletedFlow_surjective` |
| Actual Xi evaluation is half-density bounded iff its zero is critical | same module: `deningerMeyerHalfDensityXiEvaluationBounded_iff` |
| RH iff every actual Xi evaluation is continuous for canonical half-density topology | same module: `riemannHypothesis_iff_deningerMeyerHalfDensityXiEvaluationsBounded` |

## Unproved statement, explicitly labeled in manuscript

The canonical half-density quotient seminorm, Hausdorff seminorm completion, and surjective
isometric centered flow are proved.  What is not proved is universal arithmetic admission:
boundedness of every actual Xi evaluation for that seminorm.  By
`riemannHypothesis_iff_deningerMeyerHalfDensityXiEvaluationsBounded`, this statement is exactly
equivalent to RH.

## Verification status

- Paper proof audit: complete through canonical half-density selector.
- Direct Lean checks: new gauge dichotomy and half-density completion pass; dependency batch passed.
- Targeted module builds: pending final audit.
- Axiom audit: pending final audit.
- External novelty/priority audit: intentionally deferred; `[NOVELTY UNVERIFIED]`.
