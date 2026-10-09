# Uniform-ball generic divergence of reconstructed moments
Verified 2026-10-09. ONLY local Lean corpus. No web, external papers, experiments, subagents, commits or full builds. Indefinite corpus research goal remains active.

## Result and source files
formal/GaloisForLFunctions/RHTower/WeilLogShiftUniformBallPerturbation.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftUniformBallGenericity.lean
Both imported once after BoundedOriginGenericity in RHTower.lean.
Final card: docs/drafts/pipeline/3-formalized/weil-logshift-uniform-ball-genericity.md, moved from 1-in-progress.
Product-origin and smooth-edge cards plus failed bounded-recovery-moment-control card updated.

For EVERY bounded history center (Nat -> boundedContinuous Real) and EVERY radius r>0, a dense residual subset of its closed SUPREMUM-NORM ball has unbounded absolute reconstructed moment terms in EVERY tail at EVERY real shift simultaneously:
forall y B:Real, forall N:Nat, exists n>=N, B<norm(Moment y h n).
Consequently nowhere signed summability is dense residual in each ball. Eventual boundedness at even one history-dependent shift, and signed summability at any shift, each form meagre subsets of every positive-radius ball.
Every bounded center admits arbitrarily small UNIFORM perturbations with nowhere bounded moments. This applies to the bounded zero-deviation arithmetic anchor without needing its norm<=1.

This strengthens the previous unit product-cube result in both topology and allowable center/radius. It does NOT say every perturbation diverges.

## Constructive mechanism / positive survivor
Let h lie in closedBall(center,r), choose delta in (0,1) with 2delta*r<epsilon.
For coordinate unit e_k (norm<=1), let
g_plus=(1-delta)h+delta(center+r*e_k),
g_minus=(1-delta)h+delta(center-r*e_k).
Both remain in original ball; both are within 2delta*r of h.
Their difference is 2delta*r*e_k.
Centered continuous linear moment map gives exact affine cancellation:
Moment(y,h,n)-Moment(y,g,n)=MomentCLM(y,n)(h-g).
At n=k+2, the two origin moment values therefore differ by 2delta*r*DiagonalResponse0(k). The diagonal tends to infinity, so at least one norm exceeds any threshold B after any cutoff.
Each strict origin tail event is consequently open dense in each closed ball, even near its boundary. Closed ball is complete; local CompleteSpace instance supplies Baire.
Countable intersection over Nat thresholds/cutoffs gives arbitrary real thresholds via exists_nat_gt. Outward kernel domination transfers origin excursions to all real shifts without uncountable Baire intersections.
Uniform-near-nowhere-bounded corollary uses the ball centered at the prescribed history with radius epsilon/2.

## Public declarations
Perturbation, four theorems:
continuous_weilLogShiftRecoveryMomentBCF
weilLogShiftRecoveryMoment_sub_eq
norm_weilLogShiftRecoveryUnitHistory_le
exists_weilLogShiftUniformBall_near_large_origin
Abbreviation: WeilLogShiftUniformHistoryBall center r = Metric.closedBall center r.
Genericity, eight theorems:
isOpen_weilLogShiftUniformBallTailExcursion
dense_weilLogShiftUniformBallTailExcursion
dense_and_residual_weilLogShiftUniformBall_nowhere_bounded
weilLogShiftUniform_nowhere_summable_of_nowhere_bounded
dense_and_residual_weilLogShiftUniformBall_nowhere_summable
isMeagre_weilLogShiftUniformBall_some_eventually_bounded_moment
isMeagre_weilLogShiftUniformBall_some_summable_moment
exists_weilLogShiftUniform_near_nowhere_bounded
Definitions: weilLogShiftUniformBallTailExcursion; WeilLogShiftUniformNowhereBounded.
All namespace RHTower, open WeilExcess.

## Verification
Scratch norm/closed-ball/metric API audit exit0, including CompleteSpace and BaireSpace for arbitrary closed history balls.
Perturbation first compile had TWO elaboration issues only: continuous function addition needed explicit lambda via change; real le_abs_self needed explicit norm-to-abs conversion before transitivity. Both repaired; second compilation exported exit0/no diagnostics.
Genericity compiled/exported exit0/no diagnostics FIRST attempt.
Final commands lake --old env lean <leaf> -o .lake/build/lib/lean/... . No later source edits.
All12 public theorems #print axioms audited exactly once, exit0, each exactly [propext, Classical.choice, Quot.sound].
Both unique imports checked. Index exit0; all12 theorem rows +2 defs +1 abbrev verified.
Source whitespace/conflict/gap/forbidden-declaration/limit checks passed. A preliminary raw token scan matched the English word 'admit' in a module comment; comment-aware check passed.
Latest global lint exits1 ONLY for14 unrelated unreachable modules:
RHTower.XiLaguerrePolyaFirstOrderPreimage
HTGeometry.MatrixWienerHopfFredholm
HTGeometry.QKrawtchoukPolynomialCompleteness
HTGeometry.PaperStableCoordinate.AssociatedGradedPresentation
HTGeometry.PaperStableCoordinate.FilteredRees
HTGeometry.PaperStableCoordinate.GradedPresentationKernel
HTGeometry.PaperStableCoordinate.GradedPresentationMap
HTGeometry.PaperStableCoordinate.GradedRelation
HTGeometry.PaperStableCoordinate.ObstructionDefinitions
HTGeometry.PaperStableCoordinate.PrincipalInitialRelation
HTGeometry.PaperStableCoordinate.ReesCoefficientCriterion
HTGeometry.PaperStableCoordinate.WeightedInitial
HTGeometry.PaperStableCoordinate.WeightedInitialIdeal
HTGeometry.PaperStableCoordinate.WeightedInitialKernel
No diagnostics name either new leaf. Outside scope, untouched. Older two/three/other counts historical.

## Limits
No one-sided origin divergence, generic norm convergence to infinity, every-history claim, full positive-real-cutoff control, or RH conclusion.
The near perturbation theorem is uniform closeness, not exact preservation of an arbitrary finite prefix.
Ball radius must be positive; radius0 is not claimed.

## Next conjecture: exponentially shrinking errors
For every 0<sigma<4-pi, bounded center h0, epsilon>0, conjecture existence of bounded h with
forall k, |h(k)-h0(k)|<=epsilon*exp(-sigma*(k+2))
and nowhere bounded moments. Stronger generic formulation: parameterize by unit-ball bounded errors u, h(k)=h0(k)+epsilon*exp(-sigma*(k+2))*u(k); bad parameters should be dense residual in supremum norm.
Local mechanism: sharpen the current smooth-edge envelope by choosing
pi>a>max(0,sigma+2pi-4), then 2pi<b<a+4-sigma.
Resulting inverse diagonal exponent gamma=a+4-b exceeds sigma, so exponentially weighted diagonal still tends to infinity. Reapply affine cancellation/opposite coordinate perturbations in the error parameter ball, then Baire and outward transfer.
The decaying multiplication map is NOT open in ambient supremum topology; current residual result alone does not transfer to this constrained image. Need explicit weighted diagonal argument, not a density shortcut.
No assertion at sigma>=4-pi or optimality of threshold.
Possible further strengthening: set envelope to0 on any prescribed finite prefix; eventual diagonal argument should survive, but audit separately.
Prior search: exact lexical history/exponential query had zero results; broadened recovery/decay query and exhaustive text search within WeilLogShift*.lean found existing recovery/envelope ingredients, no weighted-history precision treatment. This is route-scoped evidence, not corpus-wide novelty claim. No Lean implementation yet.
Current card stores next conjecture and paper mechanism.

Useful Lean details:
- letI : CompleteSpace (WeilLogShiftUniformHistoryBall center r) := Metric.isClosed_closedBall.completeSpace_coe; BaireSpace inferred.
- Metric.dense_iff: Dense s iff forall x r>0, (Metric.ball x r intersect s).Nonempty.
- BCF norm_smul uses Real.norm_eq_abs explicitly.
- module tactic closes affine vector identities without raised limits.
- continuous addition may present as function-level addition: change to explicit lambda before simplifying MomentCLM_apply.

## Terminal cleanup
All owned jobs exited. All seven explicit /tmp/hgt-weil-uniform-* scratch files removed and absence verified. Former in-progress card absent. Final scoped diff checks and final card whitespace/working-plan checks passed. No pending work for this increment; active corpus goal continues with the exponentially shrinking-error conjecture.


## Verified follow-up: exponentially shrinking errors (2026-10-09)
The exponential-precision conjecture is now proved for every 0<=sigma<4-pi and every positive amplitude around every bounded center. Errors obey epsilon*exp(-sigma*(k+2)) coordinatewise, yet yield unbounded absolute moment terms in every tail at every real shift. Bad ERROR PARAMETERS in the closed supremum unit ball are dense residual; no open-map transfer to the ambient image is asserted. Origin lower envelope now exceeds every strict rate below4-pi; the affine ball perturbation mechanism is generalized with original APIs retained. All36 public theorems across all5 affected leaves compiled and passed exact standard-axiom audit;43 public API rows verified. See `mem:research/weil-logshift-exponential-precision-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-exponential-precision.md. No conclusion at/beyond4-pi or optimality claim. Next conjecture tests nonsummability of one FIXED response column, which could remove the rate restriction for signed-divergent witnesses. Latest lint still has14 unrelated errors, but their module list changed; use the new memory/card list.
