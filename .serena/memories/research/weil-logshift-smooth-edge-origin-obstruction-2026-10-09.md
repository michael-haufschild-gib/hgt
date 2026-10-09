# Smooth cutoff edges: origin obstruction and nowhere signed summability
Verified 2026-10-09. Source constraint: ONLY local Lean corpus; no web searches or external papers. Goal remains active.

## Result
New leaves:
- formal/GaloisForLFunctions/RHTower/WeilLogShiftSmoothEdgeBound.lean (5 public theorems)
- formal/GaloisForLFunctions/RHTower/WeilLogShiftOriginDiagonalDivergence.lean (6 public theorems)
Both imported once in RHTower.lean and indexed.
Final card: docs/drafts/pipeline/3-formalized/weil-logshift-smooth-edge-origin-obstruction.md. Backlog/in-progress versions removed.

Universal bounded-history SIGNED moment summability is false at EVERY real shift, including origin. For any bounded cube history and any finite prefix, a bounded cube extension preserving that prefix has nonsummable signed moments simultaneously at all real shifts. Such histories form a dense set. Every signed finite matrix budget is unbounded. These conclusions strengthen the previous outside-log2 and conditional diagonal obstructions.

## Exact positive survivor
Native smooth cutoff S(x)=glue(x)/(glue(x)+glue(1-x)), glue(x)=exp(-1/x) for x>0, zero otherwise.
For 0<x<=1/2, S(x)<=exp(2-1/x).
For facing cutoff arguments a+b<=1/r, r>=2, S(a)S(b)<=exp(4-4r); nonpositive cases vanish, positive case uses (1/a+1/b)(a+b)>=4.
Consequently truncated autocorrelation KL_L(y)<=exp(4-4r)K(y) if 2L-y<=1/r.
At native recovery cutoff L_n, diagonal separation log n-log2 has overlap log(n+1)-log n<=1/n. Thus sqrt(n)*w_nn<=2 exp(4-4n) P_log2(n).
Critical rates are pi at log2, 2pi at0. Since pi<4 choose max(0,2pi-4)<a<pi and 2pi<b<a+4. Existing paired kernel upper/lower envelopes produce c,gamma>0 with Response 0 (k+2) k >= c exp(gamma*(k+2)) eventually.
Origin diagonal therefore fails summability; the previous prefix-preserving diagonal minorant and inward signed-summability transfer give the simultaneous all-shift result.

## Public API (namespace RHTower, open WeilExcess)
SmoothEdgeBound:
smoothTransition_le_exp_edge
bulkCutoff_product_le_exp_edge
truncatedRiemannAutocorr_le_exp_edge
weilLogShiftRecoveryCutoff_margin_le
weilLogShiftRecoveryWeight_smooth_edge_bound
OriginDiagonalDivergence:
exists_weilLogShiftOriginDiagonal_exponential_lower
not_summable_weilLogShiftRecoveryDiagonal_origin
exists_weilLogShiftBoundedHistory_prefix_nowhere_summable
dense_weilLogShiftBounded_nowhere_summable
not_weilLogShiftBoundedMomentSummable
unbounded_weilLogShiftRecoveryMatrixBudget

## Verification
Both leaves compiled/exported on first compilation using lake --old env lean, no diagnostics, no subsequent source edits.
All 11 public declarations exhaustively axiom-audited, each exactly [propext, Classical.choice, Quot.sound].
Index, unique imports and all 11 API rows verified. Scoped whitespace/conflict/diff checks passed.
Latest global lint exits1 solely for these 3 unrelated unwired modules:
RHTower.CompletedErrorPrimitiveOneSidedLandau
HTGeometry.CauchyDifferenceTwoIntervalBound
HTGeometry.QKrawtchoukMaximalAtomUniqueness
No diagnostic names either new leaf. Do not fix unrelated modules. Older lint counts historical.
No new assumptions/axioms/proof gaps, numerical experiments, raised limits, external papers, web, full builds, commits, or subagents.

Updated finite-matrix, diagonal-obstruction, bounded-cube-genericity, uniform-receiver cards and failed bounded-recovery route with exact survivor and resolved signed interior question.

## Limits / next frontier
Does NOT establish divergence for every bounded history, one-sided origin divergence, residual genericity at origin, or boundedness for every positive real cutoff; no RH conclusion.
Arithmetic anchor remains bounded with zero deviations, norm<=1 not established.
Next: upgrade dense nowhere signed nonsummability to residual using origin exponential diagonal lower and open tail events. Continuity of each inverse coefficient yields open events that a term beyond N exceeds a fixed threshold; prefix extensions give density. Existing HTGeometry.dense_and_residual_setOf_forall category machinery and WeilLogShiftBoundedCubeGenericity provide local models. Stronger possible target: unbounded origin weighted terms via arbitrary thresholds, then inward transfer. Prove dependency-closed paper argument before new Lean and preserve separation from one-sided claims.
See also mem:research/weil-logshift-diagonal-obstruction-2026-10-09 and mem:research/weil-logshift-finite-matrix-receiver-2026-10-09.


## Verified follow-up: product-cube residual origin genericity (2026-10-09)
The origin residual question is now settled by `WeilLogShiftKernelTailOrder` and `WeilLogShiftBoundedOriginGenericity`: absolute moment terms are unbounded in every tail at EVERY real shift on a single dense residual subset of the unit product cube. Even eventual boundedness at one history-dependent shift is meagre; any signed summable moment is also meagre. Positive survivors include arbitrary fixed outward kernel gain, origin diagonal tending to infinity, and finite-prefix bounded extensions with origin norm tending to infinity. All12 new public theorems compiled and axiom-audited with exactly the standard set. This does not assert generic norm convergence to infinity, one-sided origin divergence, or supremum-norm genericity. The latter is the next conjecture. See `mem:research/weil-logshift-bounded-origin-genericity-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-bounded-origin-genericity.md. Latest global lint has only two unrelated wiring errors, recorded there.


## Verified follow-up: supremum-norm ball genericity (2026-10-09)
The stronger uniform-topology conjecture is now proved by `WeilLogShiftUniformBallPerturbation` and `WeilLogShiftUniformBallGenericity`. Every positive-radius closed supremum ball around ANY bounded history has a dense residual subset with absolute moment terms unbounded in every tail at every real shift. Every bounded center admits arbitrarily small uniform perturbations with this property. Thus the arithmetic anchor need not have norm at most one for the local instability result. Exact affine baseline cancellation and opposite ball-preserving coordinate perturbations are the positive mechanism. All12 new public theorems compiled and audited with exactly the standard axioms. No one-sided origin, every-perturbation, generic norm-to-infinity, or full real-cutoff claim. Next conjecture: exponentially shrinking errors at strict rates below 4-pi. See `mem:research/weil-logshift-uniform-ball-genericity-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-uniform-ball-genericity.md; latest global lint has14 unrelated wiring errors, listed there.


## Verified follow-up: exponentially shrinking errors (2026-10-09)
The exponential-precision conjecture is now proved for every 0<=sigma<4-pi and every positive amplitude around every bounded center. Errors obey epsilon*exp(-sigma*(k+2)) coordinatewise, yet yield unbounded absolute moment terms in every tail at every real shift. Bad ERROR PARAMETERS in the closed supremum unit ball are dense residual; no open-map transfer to the ambient image is asserted. Origin lower envelope now exceeds every strict rate below4-pi; the affine ball perturbation mechanism is generalized with original APIs retained. All36 public theorems across all5 affected leaves compiled and passed exact standard-axiom audit;43 public API rows verified. See `mem:research/weil-logshift-exponential-precision-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-exponential-precision.md. No conclusion at/beyond4-pi or optimality claim. Next conjecture tests nonsummability of one FIXED response column, which could remove the rate restriction for signed-divergent witnesses. Latest lint still has14 unrelated errors, but their module list changed; use the new memory/card list.
