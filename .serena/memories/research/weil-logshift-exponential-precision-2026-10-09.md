# Subcritical exponential observation precision still permits generic divergence
Verified 2026-10-09. ONLY local Lean corpus, no external papers/web. Indefinite corpus research goal remains active.

## Main result
For EVERY bounded recovery history center, epsilon>0, and 0<=sigma<4-pi, there exists a bounded history h such that
forall k, |h k-center k|<=epsilon*exp(-sigma*(k+2))
and absolute reconstructed moment terms are unbounded in EVERY tail at EVERY real shift simultaneously.
Stronger category statement: in the closed SUPREMUM-NORM unit ball of bounded error parameters u, the histories
H(u)=center+epsilon*q*u, q(k)=exp(-sigma*(k+2)),
have nowhere bounded moments on a dense residual set of parameters. Eventual boundedness at any history-dependent real shift, or signed summability at any shift, each define a meagre parameter subset.
This proves the previous exponential-precision conjecture, including sigma=0.

Topology is in the ERROR PARAMETER unit ball. Do NOT claim the continuous exponentially decaying multiplication map is open or infer residuality directly in its image with inherited ambient supremum topology. The new proof handles the constrained family explicitly.

## Files / preserved APIs
Modified:
formal/GaloisForLFunctions/RHTower/WeilLogShiftOriginDiagonalDivergence.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftUniformBallPerturbation.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftUniformBallGenericity.lean
New:
formal/GaloisForLFunctions/RHTower/WeilLogShiftExponentialPrecision.lean
formal/GaloisForLFunctions/RHTower/WeilLogShiftExponentialPrecisionGenericity.lean
All five imports unique in RHTower.lean; new leaves immediately after UniformBallGenericity.
All old public theorem types preserved. Original positive origin envelope is a zero-rate specialization of new rate-parametric proof. Original uniform-ball origin excursion theorem specializes a general affine-coordinate criterion. Existing private origin-to-all-shifts helper is now public and all usages updated.
Final card: docs/drafts/pipeline/3-formalized/weil-logshift-exponential-precision.md, moved from1-in-progress.
Uniform-ball and smooth-edge formalized cards plus failed bounded-recovery route updated.

## Exact positive mechanism
For ANY real sigma<4-pi (not necessarily nonnegative), choose
max(0,sigma+2pi-4)<a<pi and 2pi<b<a+4-sigma.
The same native smooth-edge denominator bound and paired-kernel strict-rate bounds give c>0 and gamma=a+4-b>sigma with
D_k>=c*exp(gamma*(k+2)) eventually.
Therefore exp(-sigma*(k+2))*D_k tends to infinity.
For sigma>=0, q is a bounded positive history, q(k)<=1, via ofNormedAddCommGroup.
ContinuousLinearMap.mul Real (Nat -> boundedContinuous Real) q realizes multiplication by q.
Weighted moment map is MomentCLM(y,n).comp(epsilon * multiplicationByq).
Moment_y(H(u),n)=WeightedCLM_y,n(u)+Moment_y(center,n).
WeightedCLM_y,n(unit k)=epsilon*q(k)*Response y n k.
For epsilon>0, the weighted origin diagonal tends to infinity.

General affine ball criterion:
For continuous linear coordinates T_n and baseline b_n, if T_(k+2)(unit k) tends to infinity, every relative neighborhood of every positive-radius closed history ball contains a point with arbitrarily large norm(T_n h+b_n) in any chosen tail.
Same two ball-preserving opposite coordinate perturbations; affine baselines cancel. Existing origin theorem now delegates to this criterion.
Apply criterion to weighted CLMs on the error unit ball; open tail events, Baire, and origin-to-all-shifts transfer yield genericity.
Unit-ball component bound gives the exact coordinatewise error envelope; density at zero parameter gives final witness.

## New / exposed APIs (namespace RHTower, open WeilExcess)
OriginDiagonalDivergence:
exists_weilLogShiftOriginDiagonal_exponential_lower_above {sigma} (sigma<4-pi):
  exists c gamma, 0<c and sigma<gamma and eventually c*exp(gamma*(k+2))<=Response0(k+2,k).
UniformBallPerturbation:
exists_weilLogShiftUniformBall_near_large_affine T b hdiag center r hr h B N epsilon hepsilon.
UniformBallGenericity:
weilLogShiftUniformNowhereBounded_of_origin h hOriginUnbounded.

ExponentialPrecision (8 public theorems, 3 defs):
tendsto_weilLogShiftRecoveryDiagonal_exp_damped
weilLogShiftExponentialEnvelope (sigma) (hSigma:0<=sigma) : BCF
weilLogShiftExponentialEnvelope_apply
weilLogShiftExponentialPerturbation center epsilon sigma hSigma u : BCF
weilLogShiftExponentialPerturbation_apply
continuous_weilLogShiftExponentialPerturbation
weilLogShiftExponentialMomentCLM epsilon sigma hSigma y n
weilLogShiftExponentialPerturbation_moment
weilLogShiftExponentialMomentCLM_unit
tendsto_weilLogShiftExponentialMomentCLM_diagonal
weilLogShiftExponentialPerturbation_bound (unit-ball u).

ExponentialPrecisionGenericity (7 public theorems, 1 def):
weilLogShiftExponentialTailExcursion center epsilon sigma hSigma K N
isOpen_weilLogShiftExponentialTailExcursion
dense_weilLogShiftExponentialTailExcursion
dense_and_residual_weilLogShiftExponential_nowhere_bounded
dense_and_residual_weilLogShiftExponential_nowhere_summable
isMeagre_weilLogShiftExponential_some_eventually_bounded_moment
isMeagre_weilLogShiftExponential_some_summable_moment
exists_weilLogShiftExponentialPrecision_nowhere_bounded.

## Verification
All FIVE affected leaves compiled/exported using lake --old env lean FILE -o .lake/build/lib/lean/...; exit0/no diagnostics.
Both NEW leaves passed FIRST compilation. Origin rate generalization and helper exposure passed first compilation.
Affine generalization initially failed because natural tail cutoff T shadowed map family T; cutoff renamed startIndex, next compilation passed. No proof argument changed. No later source edits.
Bounded multiplication API scratch audit exit0.
Exhaustive #print axioms for ALL36 public theorems in all five affected leaves, including retained old APIs: each exactly [propext, Classical.choice, Quot.sound], checked once, full name coverage, exit0.
Counts per leaf: Origin7, UniformBallPerturbation5, UniformBallGenericity9, ExponentialPrecision8, ExponentialPrecisionGenericity7. Eighteen newly public theorem statements.
Index exit0; all43 public API rows verified for kind, module and exact source line. Five unique imports checked. Scoped source checks passed.
Latest global lint exits1 ONLY for14 unrelated unreachable modules:
RHTower.LaguerrePolyaFirstOrderGapBound
HTGeometry.QKrawtchoukJacobiResolvent
HTGeometry.PaperStableCoordinate.CoordinateLeadingDerivation
HTGeometry.PaperStableCoordinate.FactorialClosure
HTGeometry.PaperStableCoordinate.FiltrationDerivationShift
HTGeometry.PaperStableCoordinate.GradedRelationSanity
HTGeometry.PaperStableCoordinate.LaurentDerivationTransport
HTGeometry.PaperStableCoordinate.LaurentLNDDescent
HTGeometry.PaperStableCoordinate.LaurentPresentation
HTGeometry.PaperStableCoordinate.LaurentWeightedMap
HTGeometry.PaperStableCoordinate.LocalizationLND
HTGeometry.PaperStableCoordinate.ModificationPieces
HTGeometry.PaperStableCoordinate.ReesToDegeneration
HTGeometry.PaperStableCoordinate.SourceLocalizedDerivation
No diagnostic names an affected leaf. Unrelated files untouched. Earlier14 counts referred to DIFFERENT modules and are historical.

## Limits
No claim at sigma>=4-pi or threshold optimality.
No every-error claim, one-sided origin divergence, generic norm convergence to infinity, exact finite-prefix preservation, full positive-real-cutoff control, or RH conclusion.
No new unproved analytic assumptions, axioms, gaps, numerical experiments, raised limits, external sources, full builds, commits or subagents.

## Next conjecture: one FIXED response column
Test:
not Summable (fun n => weilLogShiftRecoveryMomentResponse 0 n 0).
This is distinct from the moving diagonal just proved.
If true, two distinct amplitudes along that fixed history coordinate cannot BOTH have summable origin moments: their difference is a nonzero multiple of that nonsummable column. Any positive precision envelope at that coordinate allows such perturbations. This could remove sigma<4-pi for existence of signed-divergent histories, even with errors supported at one coordinate.
It does NOT automatically prove unbounded individual terms or current residual unboundedness; audit those separately. A sum/partial-panel category argument may yield residual nonsummability if needed.
If fixed column is summable instead, extract its finite-error stability theorem and inspect other columns. Do not presume the diagonal threshold is optimal.
Direct lexical recovery/column search found only norm_weilLogShiftRecoveryMomentPanel_eq_columns; no fixed-column divergence theorem found. Current card records exact conjecture and positive alternative.
No paper proof or Lean code for fixed-column conclusion yet. Re-search corpus before proceeding.
Endpoint sigma=4-pi remains a separate possible target; CriticalEndpoint.lean has critical lower bounds, but their bodies were NOT read this turn. Only declaration inventory was inspected, so no endpoint inference is verified.

## Lean details
ContinuousLinearMap.mul Real BCF q u = q*u by rfl; scaled map continuity works directly.
Weighted map defined by MomentCLM.comp(epsilon smul ContinuousLinearMap.mul...).
Coordinate multiplier identity q*unit(k)=q(k) smul unit(k) proved pointwise with ext and by_cases.
Scalar nesting handled by smul_smul, map_smul, smul_eq_mul; coefficient algebra by module/ring.
Avoid naming numeric cutoffs T when T is a family of maps.

## Terminal cleanup
All owned jobs exited. All seven explicit /tmp/hgt-weil-exp-* scratch files removed and absence verified. Former in-progress card absent. Final scoped diff checks and card whitespace/working-plan checks passed. This increment is closed; active corpus goal continues with the fixed-column conjecture.
