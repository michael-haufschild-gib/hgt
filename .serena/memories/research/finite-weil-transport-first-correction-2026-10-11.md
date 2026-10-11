# Canonical and full-fiber first logarithmic transport correction

Completed 2026-10-11 using ONLY local Lean corpus. No web, papers, numerical experiments, full builds, heartbeat changes, or subagents. Active endless research goal remains active.

Card: docs/drafts/pipeline/3-formalized/finite-weil-transport-first-correction.md. Old in-progress path moved away. Five new leaves,14 public declarations (2 definitions,12 theorems); umbrella RHTower.lean lines7190-7194 at audit. All five native leaf builds exited0 with EMPTY logs. Final native /tmp scratch audit exited0; every declaration has only [propext,Classical.choice,Quot.sound]. Seven API haves type-checked. Metadata issues=[],14 globally unique names,9 incoming imports fully enumerated, own/direct source/object freshness checked. Local index finds exactly two new roots (total=eligible=2,markers=[]). Scoped diffcheck and whitespace audit passed. No owned process remains live.

## Mathematics
n=r+1,A=k+2,U=A+n,K=canonical log transport cost,E=edge mean,D=1-AK,Q=(A/n)D. Local adjacent gap g_i satisfies (A+i)g_i<=1<=(A+i+1)g_i, while Ag_i<=1<=Ug_i. Hence i<=U(1-Ag_i), A(1-Ag_i)<=i+1. Average edge probability m: E<=UD,AD<=E+1;0<=E<=r. Under n^2<=A, D>=0 and AD<=n imply nD<=1. Thus |AD-E|<=1, |Q-E/n|<=1/n. At k=2n^2+t existing mean estimate gives |Q-1/2|<=4 sqrt((n+1)/2)/n. Unconditional limit Q->1/2 for every t:Nat->Nat.

Actual optimal mixture log cost C=delta K,delta=|a-b| in[0,1]. Its first correction (A/n)(delta-AC)=delta Q. Same error bound uniformly across ALL a,b. For arbitrary varying sequences a,b:Nat->Icc(0,1), correction-delta/2->0; no endpoint or offset convergence assumption.

## Exact declarations
WeilLogShiftLogGapIndexBounds (2): finiteWeilClusterLogNodes_adjacent_index_bounds; _adjacent_deficit_bounds.
WeilLogShiftTransportDeficit (3): finiteWeilCanonicalEdgeIndexMean_bounds; finiteWeilCanonicalLogTransportCost_deficit_average(r k)(b:Real) weighted bD identity; _deficit_bounds.
WeilLogShiftTransportCorrection (3): def finiteWeilCanonicalLogTransportCorrection; _mean_bound with width n^2<=A; _quadratic_mean_bound(r t) unconditional.
WeilLogShiftTransportCorrectionLimit (2): finiteWeilCanonicalLogTransportCorrection_quadratic_bound; line38 tendsto_finiteWeilCanonicalLogTransportCorrection_half(t:Nat->Nat).
WeilLogShiftMixtureTransportCorrection (4): def finiteWeilMixtureLogTransportCorrection using ACTUAL cost of finiteWeilMixtureCoupling; _eq =delta Q; _quadratic_bound uniform4e; line49 tendsto_finiteWeilMixtureLogTransportCorrection_error_zero(t)(a b:Nat->Icc(0,1)).

## Verification artifacts
/tmp/hgt-transport-correction-metadata.py generates complete declaration manifest, incoming-import inventory, native audit scratch. JSON /tmp/hgt-transport-correction-declarations.json; imports .txt; /tmp/hgt-transport-correction-final-audit.lean and .log; /tmp/hgt-transport-correction-root-search.json. Five /tmp/hgt-<Leaf>.log files empty. All processes terminal: first leaf64277,deficit8613,correction final82908,endpoint19518,mixture38124,metadata59741,root lookup44408,final audit49623,lint75606.

Repository lint /tmp/hgt-transport-correction-lint.log exited1 with367 size warnings and EIGHT FOREIGN errors: missing umbrella imports RHTower.CCMParityTopLayerEvenFloor,CCMParityTopLayerOddTest,CCMParityTopLayerProjection,CCMParityTopLayerTransform,CCMPolarOddPrimeJumps,ZetaRigidOrdinateWindow; HTGeometry.QKrawtchoukCompanionTriangular; sorry CCMPolarOddPrimeJumps.lean:104 theorem ccmPolarOddSource_eq_core_add_atoms. No issue in new closure. Do not repair concurrent foreign work or claim global lint passed.

## Gotcha
mul_le_mul_left is NOT the positive cancellation iff on this toolchain (type is a covariance function). Attempt .mp failed. Replaced n*(n*D)<=n with by_contra! h; have hp:=mul_pos hn (sub_pos.mpr h); nlinarith only[hsq,hp]. Seven API audit haves: div_le_iff₀.{0},le_div_iff₀.{0},mul_pos.{0},mul_le_mul_of_nonneg_right.{0},Finset.sum_nonneg.{0,0},Filter.Tendsto.const_mul.{0,0},abs_abs.{0}.

Next work may investigate sharper local logarithmic remainder/edge concentration bridges; no such additional conjecture is proved here. Do not redo completed endpoint or full-mixture first-correction results.
