Batch27 COMPLETE, goal ACTIVE; previous goal turn progress. User's full unbounded corpus experiment persists. Added59theorems/5modules/7defs; cumulative1264theorems/134modules. All5 scratch clean,5 exact-module builds passed,66declarations axiom-audited (only propext/Classical.choice/Quot.sound),66indexed,global formal lintPASS,78prior source hashes unchanged,no own Lean/Lake processes. Artifacts /tmp/hgt-gomes/twentyseventh; modules.json,progress.json,totals.json,build-status.json,axiom-audit.json,corpus-search-audit.json,lint.log. No live sessions. All5 appended to HTGeometry.lean; no umbrella/full builds.

Rules persist: search corpus via scripts/formal_tools.py research, no cards/docs; only Lean/sources. One foreground LEAN_NUM_THREADS=1 lake env lean scratch or lake build exactmodule at a time. No computations (no norm_num/decide/native_decide/#eval); symbolic ring/linarith/etc allowed. No hypotheses supplied as proofs; arbitrary polynomial/data and complete iff classifications; previously accepted positive parameter and finitecharge data subtypes. No commits, no subagents. Do not touch concurrent files or kill others' processes. Source comparison is concrete experimental analogue, NOT literal gauge-category theorem transcription. 2509.25276v7 withdrew earlier equivalence claim; never revive.

Source: re-opened https://arxiv.org/html/2607.24901v1#S4 this turn; invisible-kernel recovery test. Combined with previously verified integer tensor charges from2509.25276v7§5.2. Scalar tensoring = pointwise density multiplication on same base, NOT product measure.

Namespace all GaloisForLFunctions.HTGeometry.
1 GomesDilatonDensityShape.lean (12theorems,1def), import ConnectionReconstruction:
gomesDilatonDensityShape H x :=exp(H.evalx-H.eval0).
_ratio=weightHx/weightH0;_centered=weight(H-C(H0));positive,continuous,origin1.
_eq_iff shapeH=shapeK iff existsc,H=K+Cc.
_connection_iff shapeeq iff superHeqsuperK.
_constant, _amplitude_injective H↦(shapeH,weightH0),_add exactpointwisemultiplication,_neg inverse,_not_injective witness1vs0.
Origin normalization explicitly NOT probability normalization.

2 GomesDilatonMeasureReconstruction.lean (10theorems,1def):
gomesDilatonMeasure H :=volume.withDensity(ofReal(weightH)).
Weight_continuous;measure_null_iff sameLebesguenullsets;mass_ne_zero forALLH includinginfinite.
Measure_injective forALLpolynomials (withDensity equality→ae density equality→continuous full equality→exp/polyinjectivity).
_constant μ(H+Cc)=ofReal(expc)•μH.
_scale_iff μH=ofReal(expc)•μK iffH=K+Cc.
_positive_scale_iff (s:Set.Ioi0) exactshiftlog(s).
_projective_connection_iff existsexpscale iffconnectioneq.
_centered_eq_iff centeredmeasures iffshapeeq.
_tensor μH.withDensity(weightK)=μ(H+K),_dual_cancel returnsvolume.
Imports mathlib Function.AEEqOfLIntegral and Measure.OpenPos.

3 GomesDilatonMassNormalization.lean (8theorems,1def):
gomesDilatonMassNormalized H :=(μH univ)^-1•μH.
_mass=ifμHmass∞then0else1.
_zero_iff normalizedH0 iffrawmass∞.
_probability_iff IsProbability(normalizedH) iffIsFinite(rawH).
_constant invariant underarbitraryconstantshift INCLUDING∞case.
_restore_iff massH•normalizedH=rawH iffIsFinite(rawH).
_eq_iff normH=normK iff(existsc,H=K+Cc) OR(rawHmass∞ANDrawKmass∞).
_connection_iff same withsuperoperator equality asfirstdisjunct.
_mass_record_iff (normH,massH)=(normK,massK) iffH=K ORbothinfinite.
Infinite-mass inputs are zero observations, NOT probabilities; no hidden finiteness premises.

4 GomesPolynomialChargeNormalization.lean (16theorems,2defs), imports massnormal,GaussianChargeMeasure,QuarticChargeGroundState:
gomesDilatonMeasure_gaussian/quartic bridge existing literalintegercharge measures by rfl.
gomesGaussianNormalizedCharge b n, gomesQuarticNormalizedCharge b n :=normalization correspondingtensorlog.
Both_probability_iff effectivecharge(n:ℝ)*b>0;both_zero_iff effectivecharge<=0.
GaussianLogWeight_constant_iff /QuarticLogWeight_constant_iff constantdifference iffcoeffa=b.
GaussianQuarticLogWeight_constant_iff constantdifference iff a0ANDb0 (secondderivativeat0,firstat1).
BothNormalizedCharge_eq_iff acrossarbitrary b,c,n,m: effectivechargesequal ORbothnonpositive.
GaussianQuarticNormalizedCharge_eq_iff iffbothnonpositive.
_distinct forpositivefinitecharge data n,m.
BothNormalizedCharge_dual_iff iff effectivecharge0.
Crossfamily valid probability laws NEVERagree.

5 GomesDilatonNormalizationTensor.lean (13theorems,2defs), imports4:
gomesDilatonNormalizedReweight H K :=normH.withDensity(weightK).
gomesDilatonRenormalizedReweight H K :=inverseownmass•reweightedmeasure.
NormalizedReweight_formula =massH^-1•raw(H+K).
PositiveScale_normalize H(s:Set.Ioi0): normalizingofReal(s)•rawH=normH, also∞.
RenormalizedReweight_formula=ifmassH∞then0elsenorm(H+K).
_commutes_iff twoordersagree iffIsFinite(rawH)ORmass(H+K)∞.
_probability_iff finaloperationprobability iffIsFinite(rawH)ANDIsFinite(raw(H+K)).
Gaussian/QuarticRenormalizedReweight_probability_iff 0<n*bAND0<(n+m)*b.
Gaussian/QuarticNeutralNormalization_failure: normalize0beforepositivechargedensity differsfromcorrectnormalizedpositivecharge.
MassNormalized_zero_profile=0.
Gaussian/QuarticNormalized_tensor_noncongruence: forpositivechargeH, norm0=norm(-H), yetnorm(0+H)≠norm((-H)+H).
MassNormalized_no_tensor_lift: no ANYbinaryT:Measureℝ→Measureℝ→Measureℝ reconstructsnorm(H+K)fromnormHandnormK forALLpolynomials.
No-go positive survivor already exactcommutationandprobabilitycriteria. No card retirement.

Lean API lessons:
- Real.continuous_exp.comp H.continuous; Continuous.exp nonexistent.
- Measure.eq_of_ae_eq (namespaceMeasureTheory.Measure), needs OpenPos import; withDensity_eq_iff_of_sigmaFinite requiresbothAEMeasurable.
- ENNReal.ofReal_inj nonexistent; applycongrArgtoRealandsimp[dilatonWeight,ENNReal.toReal_ofReal positivity].
- Measure.zero_apply nonexistent. Zero-measureevaluation isdefinitionally0; use show(1:ENNReal)=0fromhm or zero_ne_onehm.
- rw through≠ sometimesneeds explicit ne_eq.
- typed hn/hm forcongrArgProd.fst/snd before rw; otherwiseprojectionnotrewritten.
- parenthesize((s*mass)^-1*s)•measure toavoidparsing s•measure asfactorinmultiplication.
- ENNReal.mul_inv (Or.inl hs0)(Or.inl hst) handlesarbitraryotherfactor.
- ENNReal.inv_mul_cancel/mul_inv_cancel requirenonzero,noninfinite.
- ENNReal.toReal_pos nonzero noninfinite;ofReal_toReal noninfinite.
- ENNReal.mul_ne_top,inv_ne_top.mpr,inv_ne_zero.mpr.
- Measure.measure_univ_eq_zero,measure_univ_ne_zero names areMeasure namespace.
- isFiniteMeasure_iff μ then lt_top_iff_ne_top.
Allverifiedcurrenttoolchain /tmp/.../Api.lean andscratch.
No source rereads needed for these5files.

Searches reviewed: dilaton normalized0;dilaton measure1;normalized inGomes34 allpages;polynomial probability29 allpages. Broad noisy queries refined:Gaussian constant→Gomes3;quartic Gaussian→Gomes0;normalized charge→Gomes0. normalization tensor Gomes0;normalized reweight4;normalize withDensity0;tensor normalize Gomes9. Existing RegularizedHerglotzTransform lines195-229 hasconditional generic exists_mass_probability_decomposition (finite nonzero data), not our exact unconditionalclassification. No duplicate.
Next candidates: finite normalized polynomial density tensor operation / exact domain and associativity; general polynomialexp integrability classification (evennegativeleading) if notalreadyformalized, searchfirst. Also broaden reconstruction analogue to reflected quartic kernels in HilbertMetric.SecondLevelConcavityFifthRootNoGo, foundinsearchbut sourceNOTread. Do not count nextcandidates asselected/proved. Goal remainsactive; do notmarkcomplete at batchcheckpoint.