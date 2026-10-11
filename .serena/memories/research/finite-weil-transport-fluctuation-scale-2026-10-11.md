# Sharp finite-Weil transport fluctuation scale

Completed 2026-10-11 using ONLY local Lean corpus. No external papers/web/numerics, full builds, heartbeat changes, subagents, commits. Active endless goal remains ACTIVE. Card docs/drafts/pipeline/3-formalized/finite-weil-transport-fluctuation-scale.md moved from1-in-progress.

## Proved mathematics
n=r+1,k=2n^2+t(r), arbitrary natural-valued offsets. H=sum edge mass*(i-r/2)^2, R=sum edge mass*(T_i-1/2)^2, T_i=local logarithmic correction from prior increment. NEW unconditional limits H/n->1/4 and nR->1/4. For actual optimal mixture-plan dispersion C (zero on stationary diagonal), C=delta R,delta=|a-b|. For arbitrary varying a,b:Nat->Icc(0,1), nC-delta/4->0, no endpoint convergence assumed.

Proof mechanism: q=arithmetic absolute profile,G=sum q; f=canonical central-rescaled profile,F=sum f; x_i=i-n/2,d_i=i-floor(n/2), S=sqrt((n+1)/2). Reverse local distortion proves f_i>=q_i/2, F>=G/2. Exact fourth binomial moment via Pascal recurrence: sum choose(n,i)(2i-n)^4=(3n^2-2n)2^n. Therefore sum q*x^4<=n^2G. Cauchy with existing sum q*d^2<=S^2G yields sum q*|d|x^2<=GnS. Existing point profile error/n gives sum |f-q|x^2<=GS. Together with |F-G|<=GS/n and arithmetic second moment nG/4, |B-nF/4|<=2GS<=4FS. Thus midpoint second moment differs from n/4 by<=4S. Exact midpoint-edge identity gives |H-r/4|<=4S and |H/n-1/4|<=6S/n.
New edge absolute centered first moment <=4S from weighted Cauchy and H<=(4S)^2. Existing |nT_i-i|<=1 gives point quadratic difference <=3|i-r/2|+4; sum implies |n^2R-H|<=16S. Thus |nR-H/n|<=16S/n and |nR-1/4|<=22S/n. Existing midpoint-binomial error 2S/n->0 proves all roots.
IMPORTANT: H is centered at r/2, R at1/2; these are NOT yet the variances around their actual means. Do not overclaim actual-mean variance limits.

## Eight leaves,21 public theorems
1 WeilLogShiftBinomialFourthMoment (2): finiteWeil_binomial_centered_fourth_moment(n), _half_centered_fourth_moment(n).
2 WeilLogShiftArithmeticFourthMoment (3): finiteWeilArithmeticAbsProfile_half_fourth_moment, _half_fourth_bound, _mixed_third_bound.
3 WeilLogShiftProfileLowerBound (2): finiteWeilCanonicalMassProfile_ge_half_arithmetic, _sum_ge_half (quadratic width).
4 WeilLogShiftMidpointSecondMomentBound (3): finiteWeilCanonicalMassProfile_weighted_second_error, _second_centering_error, finiteWeilCanonicalMixture_midpoint_second_moment_error.
5 WeilLogShiftEdgeVarianceScale (4): finiteWeilCanonicalEdgeCenteredSecondMoment_sharp_bound, _normalized_sharp_bound, _quadratic_sharp_bound; line60 tendsto_finiteWeilCanonicalEdgeCenteredSecondMoment_quarter(t).
6 WeilLogShiftTransportFluctuationComparison (3): finiteWeilCanonicalEdge_centered_first_moment_bound; finiteWeilCanonicalEdgeLogCorrectionSecondMoment_raw_comparison, _scaled_comparison.
7 WeilLogShiftTransportFluctuationLimit (2): finiteWeilCanonicalEdgeLogCorrectionSecondMoment_fluctuation_bound(r t); line29 tendsto_finiteWeilCanonicalEdgeLogCorrectionSecondMoment_fluctuation_quarter(t).
8 WeilLogShiftMixtureFluctuationLimit (2): finiteWeilMixtureCoupling_log_correction_fluctuation_bound; line32 tendsto_finiteWeilMixtureCoupling_log_correction_fluctuation_error_zero(t)(a b).

## Verification
All8 native leaf builds exited0 with EMPTY logs. Final native /tmp/hgt-fluctuation-final-audit.lean exited0: all21 theorems only[propext,Classical.choice,Quot.sound],8API haves pass. Metadata issues=[],21 globally unique names,15 incoming imports exhaustively inspected, own/direct source/object freshness and whitespace checked. Umbrella RHTower.lean7201-7208 at audit, each imported once. Local root lookups1+2=3 eligible roots,markers=[]. Scoped diffcheck passed. All processes terminal.
Artifacts /tmp/hgt-fluctuation-metadata.py; -declarations.json; -incoming-imports.txt; -final-audit.lean/.log; -edge-root-search.json; -transport-root-search.json; -lint.log; eight /tmp/hgt-<Leaf>.log files empty. Final handles:25456,99794,53874,64429,13892,47722,87820,48638(native leaves);51152 metadata;44893+99773 root searches;63799 native axiom/API audit;39450 lint.
Global lint snapshot exit1:367 size warnings, SEVEN FOREIGN errors. Six missing umbrella imports RHTower.CCMParityTopLayerAlternation,CCMParityTopLayerEvenModel,CCMParityTopLayerOddFloor,CCMPolarOddPrimeJumps,XiGaussianHeatHankelWindowCeiling; HTGeometry.QKrawtchoukCompanionTriangular. One sorry CCMPolarOddPrimeJumps.lean:104, ccmPolarOddSource_eq_core_add_atoms. No issue in this closure; do not repair foreign concurrent files or claim global lint passed.

## Gotchas/APIs
`simp only[abs_mul,abs_of_nonneg(sq_nonneg _)]` inside a sum failed type inference. Use sum_congr, intro i, then rw[abs_mul,abs_of_nonneg(sq_nonneg(x i))]. Scalar normalized transport identity closed with field_simp alone; removed trailing ring (No goals to be solved).
API haves:mul_one_div.{0};Finset.sum_choose_succ_mul.{0};Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul.{0,0};Fin.sum_univ_eq_sum_range.{0};mul_le_mul.{0};Nat.sum_range_choose;Real.sq_sqrt;Real.sqrt_nonneg.

## Potential next target, NOT FORMALIZED
Discharge fixed-center versus actual-mean variance gap. A weighted first-moment version of profile error should prove |E-r/2|<=2 uniformly at quadratic starts: arithmetic centered first moment is0, and 2|d||x|<=d^2+x^2 gives sum q|d||x|<=(3n+2)G/8<=nG. Thus sum|f-q||x|<=G, normalize F>=G/2. Then existing |Q-E/n|<=1/n yields |Q-1/2|<=4/n. Generic probability centering identities would give actual edge variance/n->1/4 and n*actual correction variance->1/4; full mixture moving-part law may transfer too. This is an unformalized next route, not a claim of completed results. Search corpus before coding. Current fixed-center H/n,nR and full-mixture fluctuation laws are DONE; do not redo.
