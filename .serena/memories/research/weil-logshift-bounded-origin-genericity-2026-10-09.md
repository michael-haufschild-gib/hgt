# Generic nowhere bounded moments in the recovery unit cube
Verified 2026-10-09. ONLY local Lean corpus; no external sources or web. Active indefinite corpus goal remains active. Previous goal increment completed smooth-edge origin obstruction; this increment proves the stronger residual all-shift unboundedness result.

## Final files
- formal/GaloisForLFunctions/RHTower/WeilLogShiftKernelTailOrder.lean (1 public theorem, 56 lines)
- formal/GaloisForLFunctions/RHTower/WeilLogShiftBoundedOriginGenericity.lean (11 public theorems, 3 definitions, 191 lines)
- Both imported exactly once after OriginDiagonalDivergence in RHTower.lean.
- Final card: docs/drafts/pipeline/3-formalized/weil-logshift-bounded-origin-genericity.md, moved from 1-in-progress.
- Smooth-edge and diagonal-obstruction formalized cards, and failed bounded-recovery-moment-control card, updated with the new result and positive survivor.

## Exact conclusions
Inside WeilLogShiftBoundedHistory = Nat -> Icc(-1,1), with PRODUCT topology:
A dense residual set has absolute reconstructed moment terms unbounded in EVERY tail at EVERY real shift simultaneously:
forall y B : Real, forall N : Nat, exists n >= N, B < norm(Moment y (Values height) n).
Thus nowhere signed moment summability is dense and residual.
Histories admitting even one eventually bounded moment sequence at any real shift form a meagre set; histories admitting any summable signed moment also form a meagre set. The exceptional shift can depend on the history.
Origin inverse diagonal tends to infinity. Every finite bounded prefix has a bounded extension whose absolute origin moment terms, indexed k+2, tend to infinity.
New reusable kernel comparison: |y|<|c| implies eventually A*P_y(n)<=P_c(n), for EVERY fixed real multiplier A.

## Proof
Kernel rates r(y)=2pi exp(-|y|). For |y|<|c| choose r(c)<b<a<r(y). Existing paired-kernel bounds give P_y<=C exp(-a n), P_c>=D exp(-b n) eventually. D exp((a-b)n) eventually exceeds AC. Multiply by exp(-a n). A<=0 follows from positivity.
Prior origin diagonal positive exponential lower envelope gives Tendsto diagonal atTop atTop.
Prior prefix diagonal minorant supplies extensions with origin norm tending to infinity. Each strict origin tail event U(K,N) = exists n>=N+2, K<norm(moment0 n) is open by inverse-coefficient continuity, dense via prefix extensions converging coordinatewise.
Baire intersection over (K,N):Nat*Nat gives arbitrary real thresholds using exists_nat_gt.
For each nonzero y, eventual kernel comparison with inner shift0 and A=1 makes norm(moment_y) eventually >= norm(moment0). Transfer origin excursions pointwise to ALL real shifts; no uncountable Baire intersection.
Nonsummability follows by norm terms not tending to zero; meagre exceptions are excluded by the residual set.

## Public names (RHTower)
Kernel:
eventually_mul_pairedLogKernel_le_of_abs_lt
Genericity:
tendsto_weilLogShiftRecoveryDiagonal_origin_atTop
exists_weilLogShiftBoundedHistory_prefix_origin_norm_atTop
isOpen_weilLogShiftBoundedOriginTailExcursion
dense_weilLogShiftBoundedOriginTailExcursion
dense_and_residual_weilLogShiftBoundedOriginUnbounded
weilLogShiftBoundedNowhereBounded_of_origin
dense_and_residual_weilLogShiftBoundedNowhereBounded
weilLogShiftBounded_nowhere_summable_of_nowhere_bounded
dense_and_residual_weilLogShiftBounded_nowhere_summable
isMeagre_weilLogShiftBounded_some_eventually_bounded_moment
isMeagre_weilLogShiftBounded_some_summable_moment
Definitions:
weilLogShiftBoundedOriginTailExcursion K N
WeilLogShiftBoundedOriginUnbounded height
WeilLogShiftBoundedNowhereBounded height

## Verification
Both leaves compiled/exported on FIRST compilation with lake --old env lean FILE -o .lake/build/lib/lean/...; exit0, no diagnostics, no later source edits.
All12 public theorems exhaustively checked exactly once by scratch #print axioms, exit0. Each exactly [propext, Classical.choice, Quot.sound].
Index exited0; all12 theorem and3 definition rows under correct modules, unique imports checked.
Scoped whitespace/forbidden-token checks passed. No gaps, new analytic assumptions/axioms, raised limits, experiments, full builds, commits or subagents.
Latest global lint exits1 solely for TWO unrelated unwired modules:
HTGeometry.PaperIntrinsicFiberClocks
HTGeometry.QKrawtchoukPinnedQuadrature
No diagnostics name new leaves. Earlier3/other counts historical.
API scratch initially failed only because bare polymorphic have := @Name had unresolved universe metavariables; explicit .{0,...} annotations repaired it and audit passed. All actual new proof files compiled first time.

## Limits
Product cube topology only. Generic conclusion is tail UNBOUNDEDNESS, not generic Tendsto norms to infinity. Special prefix extensions do tend to infinity at origin.
No one-sided origin divergence, every-history claim, full positive-real-cutoff bound, or RH conclusion.
Prior residual all-three-moment result at |y|>=log2 remains separate and compatible.

## Next conjecture: stronger supremum-norm genericity
Same nowhere-bounded conclusion should be dense residual in the SUPREMUM-NORM closed unit ball of bounded real histories.
For a unit-ball h and 0<delta<1, histories (1-delta)h +/- delta*unit(k) stay in unit ball and are within 2delta of h in supremum norm. Their moment at k+2 differs by 2delta*Response 0 (k+2) k. Diagonal tends to infinity, so at least one norm exceeds any fixed threshold for k sufficiently large. This should make every origin strict tail event open dense in the uniform topology. Closed-ball completeness gives Baire, then outward comparison transfers all shifts.
Need verify affine difference, norm estimates, closed-ball subtype CompleteSpace/BaireSpace and continuity using local Lean APIs. Existing MomentCLM, Inverse_affine and UnitHistory from UniformMomentReceiver/FiniteMatrixReceiver are the local starting points. No new analytic assumption needed in planned proof.
This is a new conjecture, NOT yet formalized. Current card records it.

## Terminal cleanup
All owned jobs exited. All six /tmp/hgt-weil-residual-* scratch files explicitly removed and absence verified. Former 1-in-progress card absent. Final scoped diff checks passed; every working-plan checkbox completed. Research goal remains active.


## Verified follow-up: supremum-norm ball genericity (2026-10-09)
The stronger uniform-topology conjecture is now proved by `WeilLogShiftUniformBallPerturbation` and `WeilLogShiftUniformBallGenericity`. Every positive-radius closed supremum ball around ANY bounded history has a dense residual subset with absolute moment terms unbounded in every tail at every real shift. Every bounded center admits arbitrarily small uniform perturbations with this property. Thus the arithmetic anchor need not have norm at most one for the local instability result. Exact affine baseline cancellation and opposite ball-preserving coordinate perturbations are the positive mechanism. All12 new public theorems compiled and audited with exactly the standard axioms. No one-sided origin, every-perturbation, generic norm-to-infinity, or full real-cutoff claim. Next conjecture: exponentially shrinking errors at strict rates below 4-pi. See `mem:research/weil-logshift-uniform-ball-genericity-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-uniform-ball-genericity.md; latest global lint has14 unrelated wiring errors, listed there.
