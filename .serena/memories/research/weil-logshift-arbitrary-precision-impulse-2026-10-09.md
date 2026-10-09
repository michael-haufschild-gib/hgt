# Arbitrary precision envelopes permit one strictly upward late error
Verified 2026-10-09. ONLY LOCAL LEAN CORPUS / installed local Lean/mathlib. NO WEB, PAPERS, NUMERICAL EXPERIMENTS, SUBAGENTS, FULL BUILDS OR COMMITS. Indefinite corpus goal remains active. All owned jobs terminal and all scratch cleaned.

## Main result
For EVERY bounded recovery-history center, EVERY strictly positive coordinatewise error envelope epsilon:Nat->Real, and EVERY finite prefix length M, there exist k>=M and a bounded history h such that:
- center(k)<h(k): exactly one STRICTLY UPWARD nonzero error;
- h(j)=center(j) for EVERY j!=k, including all later observations;
- |h(j)-center(j)|<=epsilon(j) for ALL j;
- h agrees with center throughout j<M;
- every real-shift moment has unbounded absolute terms in every tail;
- signed moment Summable fails at EVERY real shift.
No exponential rate restriction. This removes sigma<4-pi for EXISTENCE, and adds exact preservation of all but one observation. Genericity beyond that old threshold is NOT yet formalised; see next task.
Stronger envelope theorem requires only epsilon(j)>=0 everywhere and epsilon(k)>0 at a chosen sufficiently late coordinate k. Every other allowance may be zero.

## Structural insight
There exists K independent of center such that for each fixed k>=K, at most ONE real amplitude t on line center+t*UnitHistory(k) can have eventually bounded moment terms at even one real shift. At most one can admit Summable moments at any history-dependent shift. The exceptional set may be empty; no existence/uniqueness assertion beyond subsingleton.
Distinct amplitudes t!=u have moment-difference norms tending to infinity at every real shift, because their difference is exactly (t-u)*fixed-column Response and the late fixed-column theorem is proved.
Failure of WeilLogShiftUniformNowhereBounded is equivalent to eventual boundedness of origin moments. Thus two exceptional amplitudes would give an eventually bounded difference, contradiction. Comparing delta and delta/2 supplies a positive good amplitude <=delta. Do NOT claim every nonzero error around arbitrary center diverges, or infer infinite codimension from all coordinate-line intersections being at most singletons.

## Files, all final sources compiled/exported cleanly
New:
formal/GaloisForLFunctions/RHTower/WeilLogShiftImpulseLineObstruction.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftArbitraryPrecisionImpulse.lean
Both uniquely wired after WeilLogShiftLateColumnRunaway in RHTower.lean. No old Lean API changed. Generated LEAN_API/GAPS/OVERVIEW refreshed.
Prerequisite details: `mem:research/weil-logshift-late-column-runaway-2026-10-09`.
Prior weighted-parameter machinery: `mem:research/weil-logshift-exponential-precision-2026-10-09`.

## Exact APIs (namespace RHTower, open WeilExcess)
ImpulseLineObstruction has1 def and7 public theorems:
weilLogShiftRecoveryImpulseHistory (center:Nat->boundedContinuous Real)(k:Nat)(t:Real):BCF
 :=center+t smul weilLogShiftRecoveryUnitHistory k.
weilLogShiftRecoveryImpulseHistory_apply center k t j:
 line(t)(j)=center(j)+(if j=k then t else0).
weilLogShiftRecoveryImpulseHistory_sub center k t u:
 line(t)-line(u)=(t-u) smul Unit(k).
weilLogShiftRecoveryImpulseHistory_moment_sub center k t u y n:
 Moment_y(line(t),n)-Moment_y(line(u),n)=(t-u)*Response(y,n,k).
weilLogShiftUniform_not_nowhere_bounded_iff_origin_eventually_bounded h:
 (not WeilLogShiftUniformNowhereBounded h) iff
 exists B:Real, exists N:Nat, forall n>=N, norm(Moment_0(h,n))<=B.
exists_weilLogShiftRecoveryImpulse_moment_separation:
 exists K, forall center k, K<=k -> forall t u,t!=u -> forall y,
 Tendsto (fun n=>norm(Moment_y(line(t),n)-Moment_y(line(u),n))) atTop atTop.
exists_weilLogShiftRecoveryImpulse_exceptional_subsingleton:
 exists K, forall center k,K<=k ->
 Set.Subsingleton {t:Real | not WeilLogShiftUniformNowhereBounded(line(t))}.
exists_weilLogShiftRecoveryImpulse_summable_subsingleton:
 exists K, forall center k,K<=k ->
 Set.Subsingleton {t:Real | exists y:Real,Summable(Moment_y(line(t)))}.

ArbitraryPrecisionImpulse has4 public theorems:
exists_weilLogShiftRecoveryImpulse_two_amplitude_alternative:
 exists K, forall center k,K<=k -> forall t u,t!=u ->
 NowhereBounded(line(t)) OR NowhereBounded(line(u)).
exists_weilLogShiftRecoveryImpulse_positive_amplitude:
 exists K, forall center k,K<=k -> forall delta>0,
 exists t,0<t AND t<=delta AND NowhereBounded(line(t)).
exists_weilLogShiftRecoveryImpulse_within_envelope:
 exists K, forall center epsilon,(forall j,0<=epsilon(j)) ->
 forall k,K<=k ->0<epsilon(k) -> exists h:BCF,
 center(k)<h(k) AND (forall j!=k,h(j)=center(j)) AND
 (forall j,abs(h(j)-center(j))<=epsilon(j)) AND NowhereBounded(h).
exists_weilLogShiftArbitraryPrecision_single_error
 (center:BCF)(epsilon:Nat->Real)(hEpsilon:forall j,0<epsilon(j))(M:Nat):
 exists k h,M<=k AND center(k)<h(k) AND unchanged off k AND componentwise error bound AND
 exact prefix j<M AND NowhereBounded(h) AND forall y,not Summable(Moment_y(h)).
The statement order matches the source. BCF notation needs `open scoped BoundedContinuousFunction`.

## Verification
Both final leaves audited via lake --old env lean <leaf> -o <object>, exit0 with NO diagnostics. ImpulseLine passed first compile with only deprecated push_neg warning; changed to compiler-recommended push Not, final clean. Precision first compile had one if-True simplification mismatch; direct rw instead of restrictive simpa fixed it, next/final compile clean. Paper proof unchanged.
ALL11 public theorem axioms audited exhaustively in /tmp: exactly [propext,Classical.choice,Quot.sound], full name coverage once, exit0/no diagnostics.
Two unique umbrella imports, final source hashes/object freshness, scoped gaps/raised-limit/whitespace checks passed. A naive source scan initially matched English 'admit' in a docstring; corrected scan excludes comments. Do not treat prose as a Lean declaration.
Index exit0,13 modules changed globally,0 removed. ALL12 affected public API rows checked for kind,module,source path,line,no duplicates. Source hashes unchanged after audits.
Latest GLOBAL lint exit1 only for17 unrelated unreachable HTGeometry modules:
PaperGenericSL2Presentation
PaperRationalAdditiveActionBoundary
PaperStabilizedAdditiveAction
PaperStableCoordinate.ActionWeightDerivative
PaperStableCoordinate.CoactionAction
PaperStableCoordinate.DeterminantActionWeights
PaperStableCoordinate.DeterminantGradedObstruction
PaperStableCoordinate.DeterminantGradings
PaperStableCoordinate.DeterminantLiftWeights
PaperStableCoordinate.DeterminantWeights
PaperStableCoordinate.HomogeneousQuotientWeight
PaperStableCoordinate.LNDAction
PaperStableCoordinate.LNDExponential
PaperStableCoordinate.LNDExponentialLaw
PaperStableCoordinate.LaurentWeightObstruction
QKrawtchoukCompanionNormResolvent
QKrawtchoukCompanionOperator
No affected-file diagnostic; unrelated files untouched. Prior6-error list is historical.
All owned handles terminal. Ten explicit /tmp/hgt-weil-impulse-* files removed, absence verified: search.json,generic-search.json,api.lean,axioms.lean,line.log,precision.log,axioms.log,manifest.json,index.log,lint.log. No remaining owned job or scratch.

## Cards
Promoted to: docs/drafts/pipeline/3-formalized/weil-logshift-arbitrary-precision-impulse.md
Former1-in-progress same-name card absent, checked. Late-column and fixed-column cards updated with completed payoff and current destination. Coordinate-zero conjecture remains OPEN on fixed-column card; not retired.
NEXT card: docs/drafts/pipeline/1-in-progress/weil-logshift-arbitrary-precision-genericity.md

## Next task: genericity for arbitrary bounded weights / envelopes
No Lean code for this extension yet. Dependency-closed PAPER proof and novelty check already on next card.
Current local search `research 'precision residual' --mode lexical --module WeilLogShift --no-refresh --json` returned exactly2 eligible declarations, both old ExponentialPrecisionGenericity results. Exhaustive rg found no arbitrary-envelope or fixed-direction genericity theorem. Backend fts5; no partial/coverage fields in lexical output.
Target: exists K, for any center and bounded weight q with q(k)!=0 at some k>=K, H(u)=center+q*u has NowhereBounded moments on a DENSE RESIDUAL subset of the CLOSED SUPREMUM-NORM UNIT BALL of bounded error parameters u.
Paper density proof handles boundary: for u in unit ball and any neighborhood radius, choose0<delta<1 with2delta<radius. uPlus=(1-delta)u+delta Unit(k), uMinus=(1-delta)u-delta Unit(k) both stay in ball and within2delta of u. H(uPlus/minus)=H((1-delta)u) plus distinct amplitudes +/-delta*q(k) at coordinate k. Two-amplitude theorem makes at least one good. Therefore good parameter set itself is dense.
Origin tail-excursion events are open by continuous multiplication and native moment continuity; each contains the dense good set. Existing countable open-dense theorem on complete closed ball gives residuality, then origin-to-all-shifts transfer. Signed nonsummability follows.
For arbitrary positive epsilon and prefix M use q(j)=0 when j<M, else min(1,epsilon(j)). On discrete Nat this defines a bounded continuous function,0<=q(j)<=epsilon(j),positive at every j>=M. Every unit-ball parameter obeys the envelope and exact prefix. Choose k>=max(K,M). This should remove the old sigma<4-pi restriction for GENERICITY too, including all nonnegative exponential rates as a corollary.
IMPORTANT: topology is error-parameter closed unit ball. Do NOT infer residuality in image histories with ambient supremum topology; multiplication by a vanishing envelope need not be open.
Current source inspected: UniformBallGenericity lines72-96 use
 letI CompleteSpace(closedBall center r):=Metric.isClosed_closedBall.completeSpace_coe;
 HTGeometry.dense_and_residual_setOf_forall on q:Nat×Nat tail events;
 result monotonicity and origin-to-all-shifts transfer.
Native helper full name GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall.
Potential generic weighted CLM: ContinuousLinearMap.mul Real BCF q, already verified in earlier exponential-precision increment. Keep actual API/source checks local. Existing old constrained APIs need not be broken.
Further independent exposed questions: strict alternating signs and quadratic-exponent lower growth of late coefficient columns. Neither formalised. Single-coordinate instability alone does NOT prove all finite-support perturbations diverge or stable subspace has infinite codimension.

## Workflow details
Serena formal symbols are ignored; established apply_patch fallback, no need retry ignored-file symbol tools. update_plan unavailable; cards track tasks. hgtl7 skill and Serena initial instructions already read earlier conversation; don't reread unnecessarily. Goal file must be read at start of each continuation as explicitly requested. Session init docs architecture/testing absent on this turn. No new user questions needed.
