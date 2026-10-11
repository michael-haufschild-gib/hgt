# Edgewise logarithmic correction: mass concentration with persistent extremes

Completed 2026-10-11, local Lean ONLY. No web/papers/numerics, full/umbrella builds, heartbeat hikes, commits, subagents. Endless goal remains ACTIVE. Card docs/drafts/pipeline/3-formalized/finite-weil-edge-correction-concentration.md moved from1-in-progress.

## Result
n=r+1,A=k+2,g_i=adjacent log gap,m_i=edge probability,T_i=(A/n)(1-A g_i). For ALL r,k, T_i belongs to[0,1], and sum m_i T_i equals prior canonical correction Q. Under n^2<=A, |n T_i-i|<=1 (hence |T_i-i/n|<=1/n). R=sum m_i(T_i-1/2)^2, H=existing edge centered second moment about r/2. R<=(4H+4)/n^2. At k=2n^2+t, 0<=R<=8e, e=sqrt((n+1)/2)/n. Thus R->0 for arbitrary offsets t:Nat->Nat. Tail mass beyond error1/(q+1) is <=(q+1)^2R and tends0 for every q:Nat.

Actual plan dispersion cost J_uv is squared local-correction error for u!=v, zero when u=v (stationary diagonal mass carries no transport correction). Symmetric/nonnegative. Canonical coupling cost of J=R; every optimal mixture coupling cost=|a-b|R. Arbitrary varying a,b:Nat->Icc(0,1) therefore have vanishing plan dispersion, with no convergence assumptions.

Boundary: T_first<=1/n for EVERY k; first edge correction tends0 along arbitrary starts k(r). At quadratic starts |T_last-1|<=2/n, so last edge correction tends1. Weighted concentration coexists with persistent extreme edge values. Do not claim uniform convergence of all edge corrections to1/2.

## Six leaves,28 public (4 defs24 theorems)
WeilLogShiftEdgeLogCorrection (5): def finiteWeilCanonicalEdgeLogCorrection; _mem_Icc; _scaled_index_bound; _index_bound; _mean.
WeilLogShiftEdgeCorrectionMoment (4): def finiteWeilCanonicalEdgeLogCorrectionSecondMoment; _nonneg; _edge_bound; _quadratic_bound.
WeilLogShiftEdgeCorrectionLimit (5): line12 tendsto_finiteWeilCanonicalEdgeLogCorrectionSecondMoment_zero; def finiteWeilCanonicalEdgeLogCorrectionTailMass; _nonneg; _bound; line57 tendsto_finiteWeilCanonicalEdgeLogCorrectionTailMass_zero.
WeilLogShiftCorrectionPlanCost (7): def finiteWeilLogCorrectionDispersionCost; _self; _symm; _nonneg; _edge; finiteWeilCanonicalCoupling_log_correction_dispersion; finiteWeilMixtureCoupling_log_correction_dispersion.
WeilLogShiftCorrectionPlanLimit (2): finiteWeilMixtureCoupling_log_correction_dispersion_bounds; line26 tendsto_finiteWeilMixtureCoupling_log_correction_dispersion_zero.
WeilLogShiftEdgeCorrectionExtremes (5): finiteWeilCanonicalEdgeLogCorrection_first_bound; _last_bound; finiteWeil_edge_correction_reciprocal_error; line50 tendsto_finiteWeilCanonicalEdgeLogCorrection_first_zero(k); line63 tendsto_finiteWeilCanonicalEdgeLogCorrection_last_one(t).

## Verification
Six native leaf builds passed with EMPTY logs; final native audit /tmp/hgt-edge-correction-final-audit.lean exited0, ALL28 declarations only[propext,Classical.choice,Quot.sound],8API haves passed. Metadata6modules28globallyunique declarations12incoming imports, issues=[], own/direct object/source freshness verified, native logs empty, whitespace clean. Umbrella RHTower.lean7195-7200 at audit. Root searches four EdgeCorrection roots+one CorrectionPlanLimit root: eligible=total=4 and1, markers=[]. Scoped diffcheck passed. All owned processes terminal.
Artifacts /tmp/hgt-edge-correction-metadata.py; -declarations.json; -incoming-imports.txt; -final-audit.lean/.log; -root-search.json; -plan-root-search.json; -lint.log. Six /tmp/hgt-<Leaf>.log files empty. Terminal handles:37731(first),20514(moment),15848(edge limits),95761(plan cost final),94951(plan limit),12788(extremes final),45029(metadata),81729+60136(root lookup),56970(final audit),96538(lint).

Global lint snapshot exit1:367 size warnings, FIFTEEN FOREIGN errors. Missing14umbrella imports: RHTower.CCMParityTopLayerEvenFloor,CCMParityTopLayerNoGo,CCMParityTopLayerOddModel,CCMParityTopLayerOddTest,CCMParityTopLayerProjection,CCMParityTopLayerTransform,CCMPolarOddPrimeJumps,PaperEulerWoldCompactCharacter,PaperEulerWoldDepthHistory,WeilEvaporationLockRigidity,XiCriticalityEveryScale,XiSliceHeatTransferNoSlack; HTGeometry.PaperConvergentDiagonal,QKrawtchoukCompanionTriangular. One sorry CCMPolarOddPrimeJumps.lean:104 ccmPolarOddSource_eq_core_add_atoms. No error in this closure. Do not repair foreign concurrent files or claim global lint passed.

## APIs / gotchas
8API haves:mul_neg_of_pos_of_neg.{0},sq_pos_of_pos.{0},sq_abs.{0},mul_pow.{0},Ne.symm.{0},div_nonneg.{0},Fin.val_zero,Fin.val_last.
Diagonal `simp only[definition,if_pos rfl]` reduced condition toTrue but left ifTrue plus unused simp warning. Fix `rw[definition,if_pos rfl]`.
linarith cannot infer 2/n<=2(S/n) directly from1/n<=S/n here; use ring equality2/n=2*(1/n), then mul_le_mul_of_nonneg_left.
Actual source filenames WeilLogShiftCanonicalEdgeOrientation.lean and WeilLogShiftCanonicalParity.lean; earlier summary shorthands EdgeOrientation/BinomialParity were not literal filenames.

## Possible next conjecture, UNPROVED
Sharpen coarse concentration to fluctuation scale: H/n ->1/4 and nR->1/4 at quadratic starts. Local profile distortion plus a binomial fourth-moment bound may control weighted second-moment error better than the current uniform test bound. Search corpus before pursuing. No proof or novelty claim for these stronger limits. First-correction means, edge/plan concentration, tail decay, and extreme-edge limits above are DONE; do not redo.
