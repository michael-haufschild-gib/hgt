# Arithmetic source interaction: integer-log decay and prime-gap scale

## Status
RH remains unproved/unfalsified. Goal remains ACTIVE; completion requires formal RH proof. This turn made verified progress, no genuine blocker. No negative full quadratic or all-source positivity obtained. No subagents, commits, push, full/umbrella builds, new axioms, sorry, numeric experiments, or heartbeat changes.

Repo /Users/michael/Documents/code/hgt/formal. All six new modules below passed individual `lake --old env lean ... -o .lake/build/lib/lean/...olean` audits, final versions without warnings. Wired in GaloisForLFunctions/RHTower.lean lines19730–19735 at time; MainTheorems already imports RHTower. Ten endpoint #print axioms checks returned only propext, Classical.choice, Quot.sound. Scratch work/noether_log_gap_axiom_audit.lean deleted. Index regenerated successfully. Final lint --check-generated reports NO stale generated files and NO own unreachable files; exits1 only for four pre-existing other-work unwired leaves: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving. Preserve others' work; do not wire unfinished modules.

## Critical correction
Existing separated ContDiffBump construction avoids ALL log n for n>=2, stronger than avoiding actual nonzero von Mangoldt translations (prime powers). Exponential gap-width estimate is ONLY for this complete integer mesh. Do not apply it to prime-only or prime-power-only gaps. Nor does mere sparse support avoidance imply the containing balls' entire difference interval is free. Actual bumps positive on their whole balls do meet that stronger condition.

## New verified modules (all under GaloisForLFunctions/RHTower)
### ThetaIntegerLogGapWidth
Namespace RHTower. thetaNextIntegerLogIndex(t)=floor(exp(max t0))+1. Always index>=2, max t0<log(index)<=max t0+exp(-max t0).
integerLogFree_interval_width_le: for l>=0 and Ioo(l,r) containing no log n,n>=2, r-l<=exp(-l).
integerLogFree_interval_scaled_width_le_one: (r-l)*exp l<=1.
integerLogFree_equalRadius_width_le: for l=d-2r>=0 and Ioo(d-2r,d+2r) free of all integer logs, 4r<=exp(-l).
integerLogFree_of_ball_pairs: if every pair x in ball c2 r,y in ball c1 r avoids all logs, full difference interval avoids them. Explicit midpoint realization of each lag.
integerLogFree_equalRadius_coupling_le: 2r exp((d+2r)/2)<=exp(1/2)/2 *exp(-(d-2r)/2). Proof radius<=1/4. Radius nonneg not needed for this scalar statement.

### CCMIntegerLogGapCrossBound
Actual CCMComplexSmoothInteriorSource u,v, possibly different apertures.
abs_screwRegularKernel_le_exp_of_threshold: beyond plastic-number sign threshold, |mu(t)|<=exp(t/2).
ccmSmoothSupportMeasure_le_ball: support in radius-r ball implies measure<=2r (r>=0).
ccmSmooth_l1_product_le_ball_mass_sum: L1(u)L1(v)<=r*(Mu+Mv), M=norm actual ccmArchimedeanFormEmbedding squared.
abs_screwRegularForm_ccm_le_l1: if all support differences are beyond threshold and <=D, |screwRegularForm(re u,re v)|<=exp(D/2)*L1u*L1v. Proof establishes integrability via measurable kernel, product majorant, dominated integrability. Handles signed real parts of complex sources.
abs_screwRegularForm_ccm_integerLogGap_le: equal-radius balls with entire difference interval all-integer-log-free and lower endpoint l>=threshold give |C|<=exp(1/2)/4*exp(-l/2)*(Mu+Mv).

### ThetaIntegerLogGapPolarization
Imports CCMThetaModulusObstruction for actual source reconstruction k*phi.
support_ccmThetaSourceOfCompactRealProfile: support of reconstructed source exactly support phi (positive k).
thetaGroundNormSq_compactReal_eq_physical: exact weighted mass = actual physical embedding norm squared.
thetaGammaPolarGroundCrossPairing_eq_ccm_screw: for ordered supports, continuous ground cross equals screw form of reconstructed physical real sources.
abs_thetaGammaPolarGroundCrossPairing_integerLogGap_le: transfers previous mass bound to arbitrary real compact Schwartz profiles in the two balls.
abs_thetaRealArithmeticQuadratic_integerLogGap_difference_le (line101): |Q(phi+psi)-Q(phi-psi)|<=exp(1/2)*exp(-l/2)*(Mphi+Mpsi), under stronger full interval integer exclusion. Uses existing exact full polarization including prime/Gamma/poles. No individual Q sign follows.

### ThetaPrimeSensitivePolarization
Namespace RHTower.ThetaSourceWard.
thetaRealArithmeticQuadratic_ordered_prime_correction (line40): for ANY ordered real Schwartz profiles,
Q(phi+psi)-Q(phi-psi)=4*C(phi,psi)-2*(PrimeCross(phi+psi)-PrimeCross(phi-psi)).
No arithmetic exclusion here; exact correction retained.
thetaPrimeScalingCross_sum_eq_sub_of_primePowerFree: prime correction vanishes if each support difference avoids log n for IsPrimePow n. Branches on vonMangoldt n=0; no need to exclude composites with zero weight.
thetaRealArithmeticQuadratic_primePowerFree_polarization (line120): full Q difference=4C under prime-power-only exclusion. This materially weakens earlier all-integer exclusion theorem, opening genuine arithmetic gap analysis.

### CCMPrimeGapCrossBound
Reuses XiHeatCassiniLogMeshPrimeGapQuadrature, nthPrimeSubtype, xiMassNthPrimeLogHeight, xiHeatCassiniOrderedPrimeLogGap, xiHeatCassiniOrderedPrimeGap; no duplicated prime enumeration/gap definitions.
screwSignThreshold_lt_primeLogHeight(N): unconditional all N; plasticRoot<2<=p_N, log monotonicity. Thus prime-gap source bounds need NO separate sign-threshold hypothesis.
primeLogGap_mul_criticalHalfDensity_le_gap_div_sqrt(N): deltaLog_N * exp(log p_(N+1)/2)<=2*gap_N/sqrt(p_N). Uses existing deltaLog<=gap/p and Bertrand q<=2p, sqrt q<=2sqrt p. No asymptotic prime-gap estimate.
abs_screwRegularForm_ccm_primeLogCell_le: sources supported in radius-r balls, whole difference interval [d-2r,d+2r] inside [log p_N,log p_(N+1)] => |C|<=gap_N/(2sqrt p_N)*(Mu+Mv). This only bounds continuous interaction; prime powers can lie in a consecutive-prime gap.

### ThetaPrimeGapPolarization
abs_thetaGammaPolarGroundCrossPairing_primeLogCell_le: same physical estimate in ground coordinates.
abs_thetaRealArithmeticQuadratic_primeLogCell_difference_le (line56): full |Qsum-Qdiff|<=2*gap_N/sqrt(p_N)*(Mphi+Mpsi)+2*|PrimeCrosssum-PrimeCrossdiff|. Retains EVERY arithmetic contribution. Conditions only support geometry inside prime-log cell, compact smoothness, r>=0.
abs_thetaRealArithmeticQuadratic_primePowerFree_primeLogCell_le (line104): with actual prime-power support-difference exclusion, correction=0 and remaining bound=2*gap/sqrt p *total physical mass.

## Research significance / next work
The exact continuous coupling driving previous arithmetic phase oscillator has a quantitative budget. Moving complete-integer-log-free bumps apart shrinks that budget exponentially per unit mass; this does NOT itself prove their Q positive. Genuine prime-power gaps retain a normalized additive prime-gap scale, matching existing quadrature infrastructure. Do NOT claim gap/sqrt p tends0 or cite any unverified asymptotic gap result.
Main missing step: compare actual diagonal source energies and signed prime correction with cross interaction for all sources, or exhibit actual negative Q. Natural next objective: build translation/recentering infrastructure for smooth sources and use existing small-aperture coercivity plus exact translation covariance to prove a full two-source Gram positivity region for far-separated narrow bumps. Fixed ambient-aperture small-support estimate has exponentially bad constants; recenter individual components instead. Also construct arbitrarily far actual bump families satisfying proved geometric bounds, if useful. Do not replace goal with abstract assumed positivity criteria.

## Operational notes
Needed 12 pre-existing missing oleans repaired using exact foreground leaf commands, one Lean process at a time: SuzukiCCMMixedScrewWeilBridge, SuzukiScrewNaturalDomainEquality, SuzukiPrimeFreeScaledCoercivity, SuzukiLimitingLogOperator, ThetaPrimeShiftNoetherBoundary, SuzukiCanonicalHankelPhysicalKernel, SuzukiCanonicalCompressedHankelOperator, SuzukiCanonicalHankelOneSidedSupport, SuzukiCanonicalKernelContinuity, CCMUnitRieszApertureResolventWeld, SuzukiWeilVerticalDecay, XiSchurDiscGerm. Their sources were untouched. A sequential Python subprocess driver was used solely for build orchestration. No process remains from this turn after final lint.
One Serena find_symbol lookup stalled for minutes and was canceled (functions cell527); direct Lean reads used. Do not batch essential compiler output behind Serena Promise.all; output was lost when stalled lookup was terminated and required re-audit.
Imported namespaces can shadow add_le_add_right with reversed orientation; direct linarith avoids surprise. abs_sub_le takes three arguments (triangle via intermediate point); use abs_sub_le A 0 B then simp sub_zero,zero_sub,abs_neg.
integral_prod_mul rewrite required explicit function arguments and Measure.volume_eq_prod.
For sqrt algebra use Real.sqrt_div_self' rather than nonlinear denominator normalization.
