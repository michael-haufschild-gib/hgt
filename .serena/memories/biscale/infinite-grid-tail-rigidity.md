# Infinite-grid tail rigidity — certified frontier

Goal ACTIVE: 100 significant mathematical packages in independent BiScaleUncertainty, not RH. Certified **11/100**. Count connected results, not helper lemmas. Read attachment `/Users/michael/.codex/attachments/ec12590a-2ebd-4912-837b-1b97ebc4e121/pasted-text-1.txt` each continuation. No hgtl7, numerical experiments, heartbeat hacks, full/umbrella builds, unproved analytic interfaces. One owned foreground Lean process at a time; final audits `lake --old env lean <leaf>`. No subagents requested.

Authoritative ledger `docs/reports/BiScaleUncertainty/InfiniteGridTailRigidity-FACTS.md`; parent card `docs/drafts/pipeline/1-in-progress/infinite-grid-tail-rigidity-2026-10-17.md`. Papers and formalized cards linked there. Read current files, preserve concurrent agents' research and umbrella edits.

## Certified results
1. `InfiniteGridTailRigidity.lean`, `LogarithmicIncrementEnergy.lean`: 22 theorem audits. ceil(exp T) lag in [0,exp(-T)], separated-copy detecting sample=-a h_f(lag). Fixed-source polar copies eventually violate the infinite grid; arbitrary changing compact C² seeds preserving the sample pay E>=exp(-1/2)T/4, seed and copy. Quantitative logarithmic increment theorem and local/error-sensitive variants.
2. `LogarithmicCompressionEnergy.lean`, `InfiniteGridPolarRecovery.lean`: 17 theorem audits. Actual smooth compact polar all-grid sources at arbitrarily large logarithmic midpoints, exp(-1/2)T/4<=E<=C+T. Compression upper bound E(f(L .))<=A+log L for L>=D. Exact polar error scaling L^-1.
3. `LogarithmicGridDistance.lean` (8), `InfiniteGridDistanceClassification.lean` (7): d(T)=min(T-log floor(exp T),log(floor(exp T)+1)-T), T>=2; nearest distance attained, <=exp(-T)<=1, positive iff off-grid. Radius-half smooth canonical polar copies exist exactly off-grid, with E of order log(1/d(T)), uniform upper constant.
4. `FiniteTranslationTrains.lean` (9), `FiniteCopyTailRigidity.lean` (6): finite common-seed trains G=sum c_j f(.-jS), nonzero endpoints, S>D+1. Near origin hG=Qhf; near L=mS only endpoint pair survives. All-grid zeros force d(L)>0 and E(seed),E(train)>=exp(-1/2)log(1/d(L))/4>=exp(-1/2)L/4 despite interior cancellation. Division-free final endpoint derives support threshold from source and covers zero mass.
5. NEW `FiniteTrainActiveLags.lean` (7 public), `FiniteTrainGridClassification.lean` (5 public plus private finite-radius helper): complete active-lag criterion. For nonzero c and S>=2, an actual smooth positive-mass radius-half seed yields a positive-mass all-grid train iff every positive active center kS is off-grid, where A_k=sum_{j-i=k}c_i c_j. Inactive packets impose no grid restriction. At every active center kS>=2, arbitrary compact C² seeds with S>D+1 pay E(seed),E(train)>=exp(-1/2)log(1/d(kS))/4. Interior near-resonances can exceed endpoint cost. Constructive dilation supplies the seed. Exact finite exponential symbol multiplies source moments; symbol zero at rate1/2 gives polar balance for the same constructed source.

6. NEW `LocalCorrelationEnergyStability.lean` (4), `FiniteTrainUniformEnergy.lean` (10): uniform matching cost for every compatible finite train. Define delta=min({1} union {d(kS):positive active k}); attained, 0<=delta<=1, positive iff compatible. One C works for all packet counts, nonzero coefficients, S>=2: actual smooth radius-half positive-mass seed/train, allgridzeros, exp(-1/2)log(1/delta)/4<=E(train)<=C+log(1/delta), and polar balance if finite symbol at1/2 vanishes. Lower bound holds for every admissible seed/train with separation S>D+1. Main new tool: if normalized correlations agree on [0,a], energy difference <=2 integral_a^infinity w. For trains use a=1; compress fixed bump to delta/4. Empty active set delta=1 handled. No optimal coefficient or arbitrary-shape theorem claimed.

7. **Arbitrary-source uniform modulus and tails**: InfiniteGridUniformTail.lean (10 public theorems, one private normalization helper). For any compact C² real source, c=exp(-1/2), R=h(0), J=Levy energy: c(-log|x-y|)(h(x)-h(y))²<=8RJ for 0<|x-y|<=1. Grid-free sampling error c T(h(T)-h(log ceil(exp T)))²<=8RJ for T>=0. With all grid zeros, c|T|h(T)²<=8RJ for EVERY real T; for R>0 divide by R² to get c|T|(h(T)/R)²<=8E. Uniform family continuity radius delta=exp(-(1+8K/(c epsilon²))) for E<=K; full-grid family tail radius A=1+8K/(c epsilon²). Window c A integral_A^B h²<=8(B-A)RJ for 0<A<=B; dyadic integral decays as1/logN. No common seed/support/derivative bound/sign interval. Unweighted tail question resolved; exponentially weighted polar tail remains open. Count connected package once.

8. **Compact correlation relaxation and finite limit energy**: InfiniteGridCorrelationCompactness.lean (9 public theorems) and InfiniteGridLimitEnergy.lean (8 public, one private identity). Actual InfiniteGridEnergySource K contains compact C² source, R>0, E<=K, allgridzeros. Normalizedcorrelations have compactclosure in GLOBALsupnorm via complexification and existing HTGeometry.isCompact_closure_bcf_of_uniform_tails. Every sequence hasstrictlyincreasing subsequenceuniformlyconverging torealH continuous/even/H0=1/|H|<=1/allgridzeros/vanishingatinfinity/allfinite realGramforms>=0. correlationLevyEnergy H is ENNReal integral of ofReal((1-H)w) onIoi0; equalsactualnormalizedE. Fatou provespointwiselowersemicontinuity. Capstone derives ACTUALintegrability of (1-H)w andrealintegral<=K. No source realization, convexityofclosure, polarclosedness, orenergyEQUALITY assumed. Countonce.

9. **Exact energy continuity and origin defect classification**: CorrelationOriginEnergy.lean (10 theorems, 2 definitions) and InfiniteGridOriginConcentration.lean (7 theorems). For actual all-grid H_n→H uniformly with E_n<=K, E_n→E(H) IFF every epsilon>0 admits a>0 with integral_(0,a](1-H_n)w<epsilon for ALL n. Eventual control is equivalent via finite-prefix shrinking. For every a>0, tail integrals converge even under pointwise correlation convergence, with uniform-error bound epsilon*integral_a∞w. If energies→L, D=L-E(H)>=0 and every fixed core integral tends to D+C_H(a); shrinking a leaves D. Every bounded-energy source sequence has a strict subsequence with simultaneous global uniform correlation and energy convergence and this exact defect formula. Package 10 constructs strict positive defects with common support and strong source convergence. Count once.


10. **Strict loss for actual smooth signed sources, with all-grid witnesses**: SmallSourceCorrelationStability (4 theorems), UnitEnergySmallSources (4), ShortSupportEnergyInjection (1), InfiniteGridStrictEnergyLoss (3). Unconditional C_c real source endpoint constructs smooth f,g_n, positive masses, common support radius B, energy ceiling K, d>0, source squared-L2 convergence and global uniform normalized-correlation convergence, yet E(g_n)>=E(f)+d every n. Witnesses additionally satisfy 2B<log2 and every gridzero, proved from support. For any b,eta>0 construct actual smooth q with radiusb, Jq=1 and0<Rq<eta by compressing a bump then amplitude-normalizing. Sign selection uses exact energyparallelogram. Setb=log2/16,t_n=1/(n+1),chooseRq<min(t_n²,Rf/(2Jf+1)),translateqby4b. ThenEgap>=1/(2Rf),Eupper<=2(Jf+1)/Rf,correrror<=t_n(Rf+3)/Rf,L2error²<=t_n². Anenergy-convergent subsequencehasD>=1/(2Rf)>0 andeveryfixedorigincorelimit=D+coref. General signed statementimposesnogridpremise; allgridpropertyisconstructedsharpness. No polar constraint/closedness asserted. Countonce.

11. **Exact signed-grid compactness criterion**: SignedGridEnergySources (9 publictheorems,2defs,1structure), SignedGridTailEquivalence (3theorems,2defs), SignedGridTraceCompactness (5publictheorems,1privatehelper). ForANYfamilySofactualcompactC²positive-masssources withoneenergyceilingK (arbitraryrealK), thefollowingareequivalent: uniformdecayofsignedH_f(logn) forallsourcesandn>=N; uniformtwo-sidedcontinuumtails; compactclosure inglobalsupnorm. No nodezero/sign,commonsupport,derivativeboundorpolarcondition. SignedsampleerrorcT(HfT-Hf(logceil(expT)))²<=8K, c=exp(-1/2); A=1+8max(K,0)/(c epsilon²) givesuniformerror<epsilonforT>=A. Compactnessnecessityusesfiniteuniformnets withcentersinACTUALsourcefamily; finitecompactcorrelationsupportsgivecommoncutoff. Noassumedvanishing/source-realizationoflimits. Anyuniformlytrace-tightsourcesequencehasstrictglobaluniformcorrelationsubsequencewithcontinuousrealH. Countsoneconnectedpackage. Noenergycontinuityorpolarclosednessclaim.

## Latest certification
Package11: all3direct lake --old env lean leafchecks passwithoutdiagnostics. All22publicdeclarations (17theorems,4definitions,1structure) audited in /tmp/signed_grid_trace_axioms.lean, onlypropext/Classical.choice/Quot.sound; privatefinite-familyhelpercoveredtransitively. All3umbrellaimports and22exactdeclaration/module APIpairsverified;indexrefreshpassed. Paper docs/reports/BiScaleUncertainty/SignedGridTraceCompactness.md;card docs/drafts/pipeline/3-formalized/signed-grid-trace-compactness-2026-10-17.md. Ledger/parentcount11. Logs /tmp/signed-grid-{sources-leaf,tail-equivalence-leaf,compactness-leaf}.log and /tmp/signed-grid-trace-{axioms,index,lint}.log. Globallintexit1only7foreignunwired: CoprimeAlternatingProjectionRate,CoprimeProjectionAngleNorm,CoprimeProjectionAnglePolynomial,CoprimeProjectionNeighbors,SignedGramCapacity,SignedGramCutoffComparison,SignedGramCutoffHierarchy. Noownedlinterror. Allownedjobsterminal;nameprobe/logcleaned,finalaxiomauditretained. No full/umbrella build. Read-onlyfieldREADMEhashstill80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507.

## Exact reusable APIs
Namespace GaloisForLFunctions.BiScaleUncertainty; open MeasureTheory Set Filter Topology; open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole; open scoped BigOperators.
- `autocorr_increment_mul_log_le hf hfc hd hd1`: exp(-1/2)*(R-h(d))*(-log d)<=4J, 0<d<=1. Ceiling-lag version `autocorr_logarithmicCeilLag_energy_bound hf hfc hT0` includes zero lag/mass.
- `exists_pos_autocorr_support_radius hfc`: exists D>0, forallx,D<|x| ->h_f(x)=0.
- `exists_logarithmicGridDistance_node hT`: exists n>=2,|log n-T|=d(T).
- `logarithmicGridDistance_le_node (T:=T) hn` has NO hT argument. `logarithmicGridDistance_pos_iff hT`, `logarithmicGridDistance_le_one hT`, `logarithmicGridDistance_le_exp_neg hT`.
- `exists_sourceRescale_logarithmic_energy_bound_of_support hf hfc hR hD hsupp`: exists A forall L>0,D<=L,E(f(L .))<=A+log L. `sourceRescale f L u=f(Lu)`, `autocorr_sourceRescale f hL x=L^-1 hf(Lx)`.
- `exists_smooth_compact_source_positive_mass` in BroadSpectralCostRealization gives actual C∞ compact seed. NEW `exists_smooth_compact_source_small_correlation_support hρ` directly gives C∞ compact positive mass with h=0 outside radiusρ.
- `integrableOn_archLevySinhWeight_Ioi ha`, `integral_archLevySinhWeight_Ioi ha` exact log+arctan tail; `integral_archLevySinhWeight_Ioi_le ha ha1` bounds tail by log(6/a)+pi. See LogarithmicCompressionEnergy lines20–62.
- `finiteTranslateSource f s c t u=sum i in s,ci*f(u-ti)`; `copyTrain f c S` uses Fin(m+1) shifts i.val*S. `copyTrainMass c=sum ci²`.
- `copyTrainMass_pos_of_exists hc`, where hc:existsi,ci!=0; regularity `contDiff_copyTrain hf c S`, `hasCompactSupport_copyTrain hfc c S`.
- `autocorr_copyTrain_local hfcontinuous hfc c hD hsupp hS hx`: hG(x)=Qhf(x), |x|<=1, S>D+1.
- `copyTrainLagCoefficient c k` uses signed integer k and double sum if j.val-i.val=k. `_zero`=Q, `_neg` even.
- `autocorr_copyTrain_grouped hfcontinuous hfc c S x`: sum over integer Icc(-m,m), A_k hf(x-kS).
- `autocorr_copyTrain_near_lag hfcontinuous hfc c hD hsupp hS hk hx`: exact A_k packet, hk:k in integer Icc(-m,m), hx:|x-kS|<=1.
- `CopyTrainGridCompatible c S := forall k:ℤ,1<=k ->k<=m ->A_k!=0 ->forall n:ℕ,2<=n ->kS!=log n`.
- `copyTrain_grid_compatible_of_zeros` proves necessity from compact continuous positive-mass seed.
- `copyTrain_active_lag_energy` gives distance positivity and lower costs for seed/train, with any nonzero coefficient vector, general support D and active center>=2.
- `exists_smooth_copyTrain_grid_source c hc hS hoff`: actual C∞ compact seed radiushalf positive mass, actual C∞ compact train positive mass, allgridzeros, and (copyTrainExpSymbol c S (1/2)=0 ->polar moment=0).
- `exists_smooth_copyTrain_grid_source_iff c hc hS`: seed existence iff compatible.
- `copyTrainExpSymbol c S beta=sum_i ci exp(beta*(i.val*S))`; `integral_copyTrain_mul_exp hfcontinuous hfc c S beta` exact source moment multiplier; `integral_copyTrain_autocorr_cosh_of_symbol_zero hfC2 hfc c S hB`.

## New package6 APIs
- `normalizedArchEnergy_eq_integral f`: E(f)=integral_Ioi0 ((R-h(x))*w(x)/R), no hypotheses.
- `normalizedArchEnergy_abs_sub_le_of_local hf hfc hRf hg hgc hRg ha hlocal`: |E(g)-E(f)|<=2 integral_Ioi a w, hlocal: forallx,0<=x ->x<=a ->h_g(x)/Rg=h_f(x)/Rf.
- `normalizedArchEnergy_copyTrain_uniform_error hf hfc hR c hc hD hsupp hS`: same bound with a=1, any nonzero coefficient vector and S>D+1.
- `exists_smooth_small_support_logarithmic_cost`: exists C forallrho>0,rho<=1, actual smooth compact positive-mass f, correlation outside rho zero, E(f)<=C-logrho.
- `copyTrainActiveLags c`: integer Icc1m filtered A_k!=0. `mem_copyTrainActiveLags` iff 1<=k,k<=m,A_k!=0.
- `copyTrainGridDistances c S` inserts1 into finite image d(kS). `copyTrainMinGridDistance c S` is min'. ALL image lambdas must explicitly type `fun k : ℤ => ...`: without annotation Lean inferred real k and coerced Finset integers to reals, breaking min witness proofs.
- `copyTrainActiveLags_center_ge_two hS hk`.
- `copyTrainMinGridDistance_le_one c S`, `copyTrainMinGridDistance_le_active S hk`, `copyTrainMinGridDistance_attained c S` (delta=1 or existsactivek,delta=d(kS)), `copyTrainMinGridDistance_nonneg c hS`, `copyTrainMinGridDistance_pos_iff c hS`.
- `copyTrain_min_distance_energy hf hfc hR hc hD hsupp hS hsep hgrid`: delta>0, seed andtrain lowerbound; hS>=2 and hsep:D+1<S.
- `copyTrain_grid_zero_of_min_distance_support hfcontinuous hfc c hS hd hsupp`: delta>0 and correlation radiusdelta/4 imply allgridzeros.
- `exists_smooth_copyTrain_uniform_distance_cost`: ONE C quantified before m,c,hc,S,hS,compatible, then actual source with lower/uppercost and polar implication.
- Toolchain names: `integral_div_const` DOES NOT exist; used `simp only [div_eq_mul_inv, integral_mul_const]`. `Finset.lt_min'` does not exist; min'mem/attainment sufficed. `Finset.min'_le`, `min'_mem`, `le_min'` verified. In local-density ratio algebra field_simp closed goal directly; trailing ring caused no-goals error, removed.

## New package7 APIs
All in namespace GaloisForLFunctions.BiScaleUncertainty, file InfiniteGridUniformTail.lean.
- autocorr_difference_sq_mul_log_le hfC2 hfc hdPositive hdLeOne: global raw square/log modulus.
- normalized_autocorr_difference_sq_mul_log_le hf hfc hR hd hd1: differences of h(x)/R, bound8E.
- exists_uniform_autocorr_continuity_radius hK0 hepsilonPositive: exists delta>0, forall compactC²sources R>0 E<=K, forallx y |x-y|<delta implies normalizeddifference<epsilon; no grid.
- autocorr_logarithmicCeilNode_error_sq_le hf hfc hT0: raw grid-free sample difference.
- autocorr_sq_mul_location_le_of_infinite_grid hf hfc hzeros hT0.
- autocorr_sq_mul_abs_location_le_of_infinite_grid hf hfc hzeros T.
- normalized_autocorr_sq_mul_abs_location_le_of_infinite_grid hf hfc hR hzeros T.
- exists_uniform_infinite_grid_tail_radius hK0 hepsilonPositive: existsA>0, forallf hf hfc R>0 E<=K hzeros, forallT A<=|T| implies |h(T)/R|<epsilon.
- integral_autocorr_sq_window_mul_left_le hf hfc hzeros hApos hAB: cA integral_A^B h²<=8(B-A)RJ.
- integral_autocorr_sq_dyadic_mul_log_le hf hfc hzeros hN2: c logN integral_logN^log2N h²<=8log2RJ.

## New package8 APIs
InfiniteGridEnergySource K fields: source:C_c(ℝ,ℝ), smooth:ContDiffℝ2source, mass_pos:0<autocorrsource0, energy_le:normalizedArchEnergy source<=K, grid_zero:foralln>=2 autocorrsource(logn)=0. correlation f x = h_f(x)/R; continuous_correlation, abs_correlation_le_one, correlation_zero, correlation_neg, correlation_log_nat. complexCorrelation:ℝ→ᵇℂ is actualcomplexification.
- isCompact_closure_infiniteGrid_correlations hK0: compactclosure(range complexCorrelation) inBCFglobalnorm.
- exists_uniform_limit_infiniteGrid_correlations hK0 (f:ℕ→InfiniteGridEnergySourceK): existsφ H,StrictMonoφ,ContinuousH,TendstoUniformly(fφ.correlation)H atTop.
- infiniteGrid_uniform_limit_geometry hK0 f hUniform: continuous/normalized/even/envelope/fullgrid/epsilon-tail-conjunction.
- correlationLevyEnergy H:ENNReal=integralofReal((1-H)w)Ioi0.
- InfiniteGridEnergySource.integrable_correlationLevyIntegrand f; .correlationLevyEnergy_eq f=ofReal(actualE).
- correlationLevyEnergy_le_liminf hMeasurable hPointwise: general measurable sequence pointwise lowersemicontinuity.
- infiniteGrid_pointwise_limit_energy_le f hPointwise: extendedenergyH<=ofRealK.
- infiniteGrid_uniform_limit_integrable_energy hK0 f hUniform: IntegrableOn actualdensity Ioi0 AND ordinaryintegral<=K.
- InfiniteGridEnergySource.gram_nonneg f m (c t:Finm→ℝ).
- infiniteGrid_uniform_limit_gram_nonneg f hUniform m c t.
- exists_infiniteGrid_finite_energy_limit hK0 f: completeuniformsubsequence+allgeometry+allfiniteGram+ordinaryintegrability+energyceiling endpoint.

## New package9 APIs
All in GaloisForLFunctions.BiScaleUncertainty:
- correlationOriginEnergy H a := integral_Ioc0a (1-H)w; correlationTailEnergy H a := integral_Ioi a (1-H)w.
- correlationOriginEnergy_nonneg hEnvelope a; correlationOriginEnergy_mono hIntegrable hEnvelope hab.
- correlation_energy_split hIntegrable haPositive: integral_Ioi0 = origin+tail.
- correlationTailEnergy_abs_sub_le hiG hiH ha hError: abs taildifference<=epsilon*integral_a∞w.
- tendsto_correlationOriginEnergy_zero hi: reciprocal radii 1/(n+1), limit0.
- exists_small_correlationOriginEnergy hi hEpsilon; exists_common_small_correlationOriginEnergy finiteSet kernels hi envelope hEpsilon.
- InfiniteGridEnergySource.integral_correlationLevyIntegrand f: ordinary integral=actualnormalizedE; .energy_split f ha.
- tendsto_correlationTailEnergy_of_pointwise f hPointwise ha: entire positive-cutoff tail convergence.
- tendsto_correlationOriginEnergy_of_energy_limit f hPointwise hEnergy ha: corelimit=L-tailH(a).
- infiniteGrid_uniform_origin_iff_eventual f: alln smallcore quantifiers equivalent eventualn.
- infiniteGrid_energy_convergence_iff_eventual_origin hK f hUniform.
- infiniteGrid_energy_convergence_iff_uniform_origin hK f hUniform.
- infiniteGrid_origin_energy_defect hK f hUniform hEnergy: D>=0 AND allpositivea corelimit=D+coreH(a).
- infiniteGrid_origin_defect_iterated_limit: explicitD and reciprocal-radius outerlimit.
- exists_infiniteGrid_origin_defect_limit hK f: existsphi,H,L,D; strictphi,continuousH,uniformcorrelationlimit,energyLimitL in[0,K],D>=0,D=L-EH,allcoredefectlimits,andalltailconvergence. No energy-convergence premise.

## New package10 APIs
All in GaloisForLFunctions.BiScaleUncertainty:
- source_cross_integral_young hfContinuous hqContinuous hfc hqc ht x: 2abs mixedtranslatedintegral<=tRf+Rq/t.
- autocorr_add_abs_sub_le_young hf hq hfc hqc ht x: rawcorrdifference<=Rq+tRf+Rq/t.
- normalized_autocorr_add_small_mass_le hf hq hfc hqc hR hcross ht ht1 hm x: normalizeddifference<=t(Rf+3)/Rf; hcross pointwise f*q=0;0<t<=1;Rq<=t².
- exists_signed_source_energy_between hfC2 hqC2 hfc hqc: existss,s²=1,Jf+Jq<=J(f+s q)<=2(Jf+Jq).
- autocorr_eq_zero_of_source_radius hs hx: fzerooutsideb and2b<absx implyhfx0, noregularityneeded.
- exists_smooth_source_in_radius hb: actualC∞compactpositive-massf withliteral source supportb.
- source_energy_normalization hJpositive: dividingf bysqrtJ givesrawenergy1,massRf/J.
- exists_smooth_unit_energy_small_mass hb heta: actualC∞compactq,0<Rq<eta,Jq1,source radiusb.
- exists_short_support_energy_injection hfC∞ hfc hR hb hs ht ht1: actualsmoothg supportradius5b,masspositive,Eupper2(Jf+1)/Rf,Egap1/(2Rf),squaredL2distance<=t²,normalizedcorruniformerror<=t(Rf+3)/Rf.
- exists_smooth_infiniteGrid_strict_energy_loss: unconditional commonshortsupport actual allgridsequencewithsourceL2anduniformcorrconvergence,butfixedpositiveenergygap.
- exists_smooth_source_strict_energy_loss: unconditional unrestricted signed-source version directly on C_c(ℝ,ℝ), withregularity/masses/ceiling/support/convergences/gapexplicit.
- exists_smooth_infiniteGrid_positive_origin_defect: unconditional actualsmoothallgridsequenceuniformcorr→actualf, energies→Ef+D,D>0,everypositivea core→D+coref(a).

## New package11 APIs
AllinGaloisForLFunctions.BiScaleUncertainty:
- LevyEnergySource K: source:C_c(ℝ,ℝ),smooth:ContDiffℝ2source,mass_pos:0<R,energy_le:E<=K. NOgridfield.
- .correlation f x=h_f(x)/R; .continuous_correlation, .abs_correlation_le_one, .correlation_zero, .correlation_neg, .correlation_abs (H|x|=Hx), .exists_correlation_zero_radius (existsA>0forallx,A<=absx→Hx0).
- .complexCorrelation f:ℝ→ᵇℂ, .complexCorrelation_apply.
- .signed_sample_error_sq_le f hT0: cT(HfT-Hf(logceil(expT)))²<=8K.
- exists_uniform_signed_sample_radius K hEpsilon: existsA>0forallf:LevyEnergySourceK forallT>=A,abssampleerror<epsilon. NoKnonnegativepremise.
- UniformSignedGridTail S := forallepsilon>0existsN:Nat,N>=2 andforallf∈S,n>=N,absHf(logn)<epsilon.
- UniformCorrelationTail S := forallepsilon>0existsA>0forallf∈S,x,A<=absx→absHfx<epsilon.
- uniformSignedGridTail_of_correlationTail, uniformCorrelationTail_of_signedGridTail, uniformSignedGridTail_iff_correlationTail S.
- isCompact_closure_signed_correlations_of_tail hTail; uniformCorrelationTail_of_isCompact_closure hCompact.
- isCompact_closure_signed_correlations_iff_tail S; isCompact_closure_signed_correlations_iff_gridTail S. Compactsetisclosure(LevyEnergySource.complexCorrelation '' S).
- exists_uniform_limit_of_signedGridTail (f:Nat→LevyEnergySourceK) (h:UniformSignedGridTail(rangef)): existsstrictphi,continuousrealH,globaluniformconvergence.
- Private finite_family_zero_radius handlesfiniteBCFfamilyeachzerooutsidearadius,includingemptyfamily. Transitivelyauditedthroughcompactnessnecessity.

## Next conjecture (unproved and uncounted)
Priority: distant-copy topology andpolarcontinuity classification. Card docs/drafts/pipeline/0-backlog/distant-copy-topology-classification-2026-10-17.md. ForfixedcompactC²positive-massf,correlationradiusD,T>D,a real,g=f-a f(.-T),b=a/(1+a²),exactexistingexpansiongivesHg-Hf=-b(Hf(.-T)+Hf(.+T)). DisjointshiftedcorrelationsupportsshouldgiveEXACTsupnormdifference|b| andHg(T)=-b. ForT_n→infinity,localcorrelationsareeventuallyexactlyHf onanyfixedwindow, andenergiesshould→Ef uniformlyoveramplitudesbecause|b|<=1/2 andexistingexponentialtranslated-packetenergybound. GlobaluniformcorrelationconvergenceandcompactclosureshouldholdIFFb_n→0 (necessityfrompackage11tailcriterion). a_n=1+shortsupportseedshouldyieldpointwiseeventualgridzeros andenergyconvergence butNONcompactcorrelations. Positive survivoristheexactamplitudecriterion.
Polarrefinement: conjectureP(Hg)=(1-2bcosh(T/2))P(Hf),P=positivehalflinecosh-moment. ForPbase!=0,polarcontinuitywouldrequirebcosh(T/2)→0, strongerthanunweightedb→0. Polarattenuationa=exp(-T/2)thenhasuniformcorrelationconvergencebutnonzero-weighteddefectifbasePnonzero. Mustsearchspecificallyforpolarmomentformulaandconstructactualsmoothnonzero-momentseedbeforeclaiming. Nofullgridblindnessassertedforthesefamilies. Paper/noveltyauditsnotcomplete,nonecounted.
Corpus /tmp/signed-grid-pointwise-frontier.txt (5mostlyirrelevanthits), /tmp/signed-grid-copy-frontier.txt (2exactlocalcopytheorems). Currentturnread DistantCopyPolarEnforcement definitions/expansion and185–317energyproofs; LocalCorrelationEnergyStability20–39. Existingreusable: autocorr_subtractCopy, normalized_autocorr_subtractCopy_local, normalizedArchEnergy_subtractCopy_sub, abs_integral_shifted_autocorr_arch_le, normalizedArchEnergy_abs_sub_le_of_local. Do notcountalreadycertifiedalgebra/energyestimatesanew.
Separateunprovedoriginrefinement: fixedfiniteenergyf,Rq_n→0,boundedJq_n shouldimplyJ(f+q_n)-Jf-Jq_n→0 withoutsupportseparation. Splitmixedincrementatpositivea;Youngoriginboundusesfixedfsmallcoreandboundedqenergy,tailusesvanishingmass. Wouldyieldexactprescribeddefects. No newprooforcount.
Package11corpussearch /tmp/signed-grid-trace-research.txt completed76.06sec,older-generationcoverage,semanticunmeasured; lexicalfallback /tmp/signed-grid-trace-lexical.txt foundactualAPIs. Read HTGeometry/BoundedContinuousUniformTailCompactness.lean FULLY. Earlier CompactDetectorNearRadicalAlternative lemmawasnotneeded: original-centerfinite-netlemmaavoidsitsentire-parameterspacevanishingpremise.

## Operational notes
Readattachment eachcontinuation; no hgtl7 orRHwork. USERSTEERING: fieldREADME moved to formal/GaloisForLFunctions/BiScaleUncertainty/README.md and is READ-ONLY FOR US. Readall242lines thisturn, SHA25680c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507; hashunchangedafterownedwork. Old docs/reports/BiScaleUncertainty/README.md removedbyothers. Nine-trapguide: general signedcorrelationstatementsprimary, preserveactualsignednodevalues. Ourallgridconstructionsareverifiedspecialcases/sharpnesswitnesses, notgeneralprime/polarcoercivity. Stay oncurrenttopic; noRHfocus. Scopeupdatedinownpaper/ledger/parentcard; nevereditguide.
Noarchitecture/testingdocs. Formalinstructions previouslyread. Serena symboltools rejectignoredLeanfiles; rg/read/apply_patchfallback. list_memories(topic=biscale)small; neverrawunfilteredlist. update_planunavailable; cardscarryplans. Don'trunresearch/indexconcurrently. Leanfromformal/,oneownedprocess,waitlivehandleevenseveralminutesofpaging. Allownedjobsterminal. No fullbuilds,commits,pushes,numericalexperiments,heartbeatoverrides.
Namesverified: Complex.dist_ofReal DOESNOTexist; use Complex.isometry_ofReal.dist_eq. Filter.Tendsto.finset_sum DOESNOTexist; use root tendsto_finsetSum. MeasureTheory.lintegral_ofReal_ne_top_iff_integrable is NOTinENNRealnamespace (sectionnameonly). measurable_archLevySinhWeight requiresIntegratedOriginCollarLeverageimport. TendstoUniformly.continuous expectsFrequentlycontinuous, useEventually.of_forall(...).frequently. Explicit (f := (s.source:ℝ→ℝ)) on integral_finset_sum_shift_sq_eq avoidsC_c-toContinuousMapcoercionrewrite mismatch. Put @[simp] onSEPARATEline fromtheorem soformalAPIindexincludesit. Oldnamesproberemoved; successfulaxiomauditretained. Noveltyclaimisconnectedcorpusresult, notexhaustiveexternalpriorityclaim.

Package9 Lean notes: integral_mono_set DOESNOTexist; use setIntegral_mono_set with integrable targetset, ae nonnegativity, ae inclusion. In shrinking-set proof rw[hempty] BEFORE simp; simp can convert1/div toinv and block rewrite. After rcases Finset.mem_insert.mp hj with rfl|..., i can be substituted away; use j. Bare have:=@polymorphicName may fail unresolved universe levels; #check @Name verifies actual signatures. GeneratedAPI uses short declaration names plus separate module column, not fullyqualified declaration string. All19 entries checked as exact name/module pairs. Owned temporary names probes removed; final axiom scratch retained.

Package10 Lean notes: abs_add does notexist; useabs_add_le. sq_le_self absent; nlinarith from0<t<=1 suffices. integral_div EXISTS (integral_div_constdoesnot). Type translatedsquareIntegrable explicitly; supplyliteralfunctions onintegral_add toavoidPi coercionrewrite mismatch. integral_add_right_eq_self (funu:ℝ=>q u^2)x handlestranslation. change J(f+q)Pi toliteralfunctionbeforelinarith. abs_sub (u+x)u plus simpa exactidentity handlesradiustriangle. field_simp cancloseidentity alone; trailingring fails. Finalenergy-subsequence simpa requiresFunction.comp_def explicitly. All newnameschecked againstcurrenttoolchain; axiomsscratchincludes#checkFunction.comp_def. Ownednamesprobe/logremovedwithPath.unlink afterexactpath/isfile/nonsymlink check; deletionvia rm rejectedlastturn, safermethodworks.

Package11 Lean notes: exists_finite_cover_balls_of_isCompact_closure hCompact hEpsilon givesfinitecentersINORIGINALSET, notjustclosure. Set.Finite.induction_on syntax: induction t,ht using Set.Finite.induction_on with |empty=>... |@insert a s ha hs ih=>...; dependentzero-radiuspremiseautomaticallygeneralized. BoundedContinuousFunction.dist_coe_le_dist (f:=F)(g:=G)x givespointwisedistance<=supdistance. Set.Finite.exists_le andbddAbove alsoverifiedbutunused. Real.add_one_le_exp T andNat.le_ceil implyN<=ceil(expT) onceN<=T. Tail→gridthresholdmax2(ceil(expA)), logmonotonicity. Afterrewritingcorrelation_abs intriangleinequality, rewriteitINSAMPLINGHYPOTHESISTOO; otherwiselineartacticseestwodifferentatoms. Sourceenergydivision field_simp[f.mass_pos.ne'] succeeds. All3newleavespasswithoutwarnings; finalaudit22declarationsstandardaxioms. TemporarynamesprobeandlogremovedviasafeexactPath.unlink.
