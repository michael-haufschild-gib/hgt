# HCF literal Xi histogram entropy application — COMPLETE 2026-10-10

Active unbudgeted original openai/math application goal, all16live+23candidate routes in docs/reports/rh-current-frontier-map.md, no Weil priority. Source results are PROVEN, no new source conjecture labels. Overall39 focused application reviews incomplete; goal remains ACTIVE. No agents spawned/authorized. No owned live processes at boundary. Previous goal turn=verified progress29newtheorems4modules.

Latest OVERALL audit tmp/hgt-openai-math/hcf-entropy-audits.json. Source pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb rechecked unchanged this turn via hcf-entropy-upstream-head.txt. all-route-applications.json latest_verified_batch points HCF; current_critical_feature_entropy_batch COMPLETE all4plansteps. StableCoordinate tracker latest_verified_batch remains prime-escape-audits.json for that family; latest_overall_application_batch points HCF and previous_goal_turn_classification updated29/4. Do NOT add HCF leaves to stable-coordinate completed_modules: these apply FourierLLogL/Pinsker. Stable totals UNCHANGED117source+153application=270modules,2749public. own-files.txt now600leaves,4891 public theorems/lemmas,6741allpublic. All imported exactly once. No own source-tree objects.

Four new RHTower leaves, namespace ROOT RHTower (module path GaloisForLFunctions.RHTower.*),29theorems12defs=41public. All4 object builds then final PLAIN lake --old env lean <leaf> checks clean/empty; all41 #print axioms standard propext/Classical.choice/Quot.sound only. Exact relpath+name searchback41/41.131 older StableCoordinate source hashes and8 primary input source hashes revalidated unchanged. All8 primary objects at least as recent as source before audit. Ledger unchanged SHA971e9a674d00c1729580931274f49892d9dd181626f288ba5040703847aca0ec. Full lint only1FOREIGN error: HTGeometry.QKrawtchoukCompanionTriangular unreachable from umbrella; not owned, do not touch. No full/umbrella build.

1 PaperCriticalFeatureEntropy.lean 6public=5theorems1def:
- paperCriticalFeatureLawAlias(P:FourierLLogL.Law alpha)(phase:alpha->Real) = expectation of ACTUAL criticalFeatureRealBoundaryPeriodization(phase)-2*pi.
- _tv(P Q)(phase): abs(aliasP-aliasQ)<=37/100*P.tvQ. Native reporter envelope is37/200 (NO extra pi factor), so2M=37/100.
- paperCriticalFeatureLaw_uniform_kl: KL(P||uniform)=log(card alpha)-entropyP.
- paperCriticalFeatureLawAlias_uniform_entropy: abs alias discrepancy <=37/100*sqrt(logcard-H(P)); domination PAID by uniform law positivity.
- _uniform_grid(N): actual uniform expectation over Fin(N+1), uniformNode0 1(N+1)i, equals (criticalFeatureUniformGridAlias(N+1)).re.
- paperCriticalFeatureGridAlias_entropy: literal weighted-grid discrepancy obeys entropy deficit bound.
Input source is PROVEN FourierLLogL.Law.tv_le_sqrt_kl (from Finite.Comparison), entropy_nonneg/entropy_le_log_card etc. Generic paper core reused, not reproved.
API verified /tmp: Fin.sum_univ_eq_sum_range(f:Nat->A)(n). rw could NOT infer f through cast/weights; give explicit f and use simpa only[one_div]. Complex.re_sum,Complex.real_smul,Complex.mul_re etc checked. First5theorems normalizing arbitrary finite law are infrastructure; actual Xi landing below is complete.

2 PaperCriticalFeaturePhaseQuantization.lean11public=8theorems3defs:
- paperCriticalFeaturePeriodization_periodic: actual physical integer tsum has period1, reindex Equiv.addRight(1:Int). Need EXPLICIT function argument to Equiv.tsum_eq; placeholder failed.
- _fract(x): periodization(Int.fract x)=periodization x using hperiod.sub_zsmul_eq floorx.
- paperCriticalFeaturePhaseBin(N)(x):Fin(N+1)=Nat.floor(Int.fractx*(N+1)); well-defined via fract<1.
- paperCriticalFeaturePhaseNode=uniformNode at that bin.
- _mem inIcc0 1; _dist: dist(fractx,node)<1/(N+1).
- paperCriticalFeatureQuantizationError(N): conditional iSup over ALL real x of abs(periodizationx-periodization(nodeNx)).
- paperCriticalFeaturePhaseNode_error_le; error_nonneg; error_le37/100; error_tendsto atTop nhds0.
Uniform continuity on compact[0,1] pays error->0 for all real ordinates uniformly, independent of cutoff, weights and shift. No numerical grid computation. Private reporter_error_bound,bdd not counted public.
API /tmp: Equiv.tsum_eq,Function.Periodic.sub_zsmul_eq,Nat.floor_lt/Nat.floor_le/Nat.lt_floor_add_one,Int.fract_nonneg/lt_one,le_ciSup,ciSup_le,Metric.uniformContinuousOn_iff verified. Native periodic lemma absent, built it. No heartbeat changes.

3 PaperCriticalFeatureXiHistogram.lean15public=9theorems6defs:
- paperCriticalFeatureXiLinePacket(n): actual hcfXiSupportPacket n filtered Re(rho)=1/2.
- paperCriticalFeatureXiWeight(n)(rho): xiSupportMultiplicity rho * SchwartzMap.realCompactIntervalCutoff n rho.im, nonnegative.
- paperCriticalFeatureXiLineMass n=sum weights, nonnegative.
- paperCriticalFeatureXiBinWeight(n N theta)(j): sum ACTUAL weights whose fractional (rho.im+theta) phase lies in bin j; nonnegative and sum exactly mass.
- paperCriticalFeatureXiHistogram n N theta: if mass>0, Law.proportional actual bin weights, otherwise uniform Fin(N+1). Zero-mass convention exact, no unproved nonempty packet assumption.
- _mass: mass*Pj=binWeightj allcases.
- _alias: mass*expected grid reporter=actual weighted binned source.
- paperCriticalFeatureXiQuantizationResidual=sum weight*(physical reporter at actual phase - reporter at its node).
- _source_decomposition: ACTUAL criticalFeatureCompactSourceBoundaryAliasAtPhase =mass*expected grid reporter+residual, using existing hcfXiLineAlias_eq_sourceAlias.
- residual_bound <=mass*uniformQuantizationError.
- paperCriticalFeatureXiAlias_entropy: abs(A_n(theta)-mass_n*uniformGridAlias(N+1).re)<=mass_n*(quantizationErrorN+37/100*sqrt(log(N+1)-entropy(actualHistogram nNtheta))). Completely unconditional in n,N,theta.
Native cutoff lemma exact name SchwartzMap.realCompactIntervalCutoff_nonnegative, not _nonneg.

4 PaperCriticalFeatureEntropyVariance.lean9public=7theorems2defs:
- paperCriticalFeatureXiEntropyDeficit nN =iSup over real theta of log(N+1)-entropy(actual Xi histogram).
- Histogram deficit <=thissup; sup>=0 and<=log(N+1), paid with source Law entropy bounds.
- paperCriticalFeatureXiEntropyBudget nN =mass_n*(abs(uniformGridAlias(N+1).re)+quantizationErrorN+37/100*sqrt(maxdeficit nN)), nonnegative.
- paperCriticalFeatureSourceAlias_entropy_budget: native boundary alias absolute value <=budget uniformly allphase.
- paperCriticalFeatureSourceVariance_entropy_budget: actual criticalFeatureCompactSourceBoundaryAliasRealVariance n <=budget², by integrating continuous native alias² over0..1. No measurability assumption on the histogram needed because only a uniform bound is used.
- paperCriticalFeatureVarianceSaving_entropy_budget: actual variance/native nonnegative upper envelope <=budget²/sameenvelope. Handles totalized zero envelope, no positivity premise added.
Elaboration pitfalls fixed: side-specific add_le_add_right/left resolved in unexpected orientations in this import context; use _root_.add_le_add with explicit scaled inequality. For intervalIntegral.integral_mono_on, give explicit full integral inequality type so volume inferred; bare have h:=... left measure metavariable stuck. All now compile cleanly.

Meaning: new direct HCF candidate landing. Native physical phase alias and variance saving now carry exact histogram entropy cost, with uniform grid alias already tending0 and newly paid quantization error tending0. This quantifies anti-equidistribution requirements; it does NOT provide a cofinal arithmetic entropy estimate or RH closure, and does not exceed the old37/100 saving ceiling. Grid resolution must be coordinated with source cutoff; fine histograms of a fixed finite atomic packet are not an arithmetic producer. No unproved source nonuniformity assumed. Retain exact physical/arithmetic normalization.

Native direct Lean files read this turn:
- HedenmalmCriticalFeatureVarianceSavingCeiling all169lines; native variance/envelope <=37/100totalzero count asymptotically, belowpi/3gap.
- HedenmalmCriticalFeatureUniformGridAliasNoGo all123lines; uniformGridAlias definition and tends0.
- HedenmalmCriticalFeatureSourceAliasBudget18-77: physicalperiodization, nonnegative,<=9, abs ripple37/200, continuity fromactualPoissonrepresentation.
- HedenmalmCriticalFeatureOffLineAliasBalance19-46,54-81,90-105: actual complete/line/offline Xi packets, source weights, sourceAlias identity statement and beginningproof.
- HedenmalmCriticalFeatureBoundaryAliasVarianceSaving61-73: nativevarianceintegral and envelope ((37/200)/(2pi))*zeroMode.
- PaperFourierLLogL/Finite/Comparison1-130 Pinsker; Finite/Law1-62,177-191,394-406 and symbols; Entropy19-31,54-87; Finite/Signal1-112; PaperCirclePosteriorFourierMetric18-76.
Avoid rereading unchanged portions.

Searches: critical-feature-fourier-search.json complete partialfalse/errors[]70263files0pending (candidate/source Lean names inspected). Initial critical-feature-entropy-search.json overly broad642hits because query included criticalFeature with--any; corrected critical-feature-entropy-exact-search.json exact entropy/histogram/Pinsker inHCF returned0. Native reporter TV/Pinsker histogram application not previously present. All exact finalsearchback41 names matched. Search JSON relpath, notpath; actual namespace rootRHTower. No cards/prose read except requested route ledger.

Artifacts hcf-entropy-{manifest,preaudit,proof-audit,searchback-audit,audits}.json;4 clean final leaf logs;axiomslog;4 exactsearchbackJSON;index/lintlogs;upstreamheadtxt. Helper /tmp/paper-hcf-entropy-audit.py completed prepare/proofs/finish then removed itself. Also removed /tmp/paper-hcf-entropy-api.lean, /tmp/paper-hcf-quantization-api.lean,/tmp/paper-hcf-variance-api.lean. Retained /tmp/paper-hcf-entropy-axioms.lean. Scratch cleanup separately verified. No owned process remains.

Additional APF review, no new theorem or APF file claimed:
Search apf-fourier-trace-null-search.json complete partialfalse/errors[]70275files0pending. Source arguments found CCMArithmeticPrimeFredholmTrace.lean. Read that whole99lines and PaperZetaCycleFourierReconstruction whole67lines; CCMConnesConsaniZetaCycles18-44,450-476,690-718. Native CCMArithmeticPrimeFredholmCycle.primeFredholm_sourceTrace_formula and completedXi_horizontalOrientation_eq_zero_iff_sourceTrace ALREADY PROVE exact receiver at source period logp and grade; don't duplicate. Existing paperZetaCycle_common_span_reconstruction reconstructs actual zeta-times-Mellin trace coefficients onone common null set for countable caps and finite complexmixtures. Current ledger already credits this module to APF. Old audit fourier-literal-batch-audits.json32public std3, integration5leaf objectchecks empty; oldmanifest lacks sourcehash, so fresh targetedaudit needed for newcurrentAPFclaim. Recorded all-route-applications.apf_trace_review.
Possible future application (NOTasserted): after pulling different prime-orbit circle periods to one unit circle, use paperendpoint to reconstruct countable family with one commonnullset. Search existing rescaling/common-period infrastructure FIRST. No missing infrastructure pivot permitted once interesting actual target chosen. Reconstruction doesn't annihilate coefficients. Resume all39focusedroute review, other Fourier receivers and TraceCone applications. Overall goal still active.

Mandatory discipline remains: one foreground Lean process at a time; never inspect live logs; no full/umbrella builds; sourceobject builds only .lake/build/lib/lean; final plain lake --old env lean file; #print axioms /tmp only; source results proven, no unpaid RH premises/numerical experiments/heartbeat changes. Search documented corpus command before new math, only Lean hits; no cards. No agents authorized. Comments<=60s. Long Python via guardedrunner. Preserve shared foreign work. All117 StableCoordinate source leaves complete; stale103pending claim already removed.