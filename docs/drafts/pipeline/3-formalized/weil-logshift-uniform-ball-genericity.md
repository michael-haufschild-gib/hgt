# Uniformly small history errors and generic moment divergence

Status: formalized and audited. Corpus-only research, 2026-10-09.

## Proved result

In every positive-radius closed ball of the Banach space of bounded real recovery histories, absolute reconstructed moment terms are unbounded in every tail at every real shift on a dense residual set. Topology is the supremum norm. In particular, every bounded history admits arbitrarily small uniform perturbations with nowhere bounded moments.

## Corpus evidence

`WeilLogShiftBoundedOriginGenericity` proves this for the unit cube's weaker product topology. Its origin diagonal tends to infinity. `WeilLogShiftUniformMomentReceiver` constructs each centered moment as a continuous linear map; `WeilLogShiftFiniteMatrixReceiver` identifies its response to a coordinate unit history. `WeilLogShiftKernelTailOrder` transfers origin unboundedness to all real shifts. Direct lexical search found these current results; no uniform-ball version appeared.

## Dependency-closed paper argument

Fix center c, radius r>0, h in the closed ball, neighborhood radius epsilon>0, threshold B, and tail cutoff N. Choose 0<delta<1 with 2delta r<epsilon. Write e_k for the kth coordinate unit history, whose supremum norm is at most one. Set

g_plus=(1-delta)h+delta(c+r e_k),
g_minus=(1-delta)h+delta(c-r e_k).

Both lie in the original closed ball by the triangle inequality; both are within 2delta r of h. Their difference is 2delta r e_k. Affine moment baselines cancel, so their origin moments at k+2 differ by 2delta r D_k, where D_k is the inverse diagonal response. Since D_k tends to infinity, choose k>=N with delta r D_k>B. The triangle inequality forces at least one of the two absolute moments to exceed B.

Thus each strict origin tail-excursion set is open and dense in the closed ball. Closed balls in the bounded-history Banach space are complete, hence Baire. Intersect over natural thresholds and cutoffs. The resulting dense residual set has unbounded origin terms in every tail. Eventual outward kernel domination transfers this to every real shift simultaneously. Eventual boundedness or signed summability at any history-dependent real shift is therefore meagre.

For arbitrarily small uniform perturbations, apply density in the ball centered at the prescribed history with radius epsilon/2. This argument handles arbitrary bounded centers, including the arithmetic zero-deviation anchor, without requiring that center's norm to be at most one.

## Limits

No one-sided origin claim, generic convergence of norms to infinity, full positive-real-cutoff control, or RH conclusion. The new topology and arbitrary ball centers are essential differences from the preceding product-cube result.

## Formal results and verification

- `WeilLogShiftUniformBallPerturbation.lean`: supremum-norm continuity of affine moments, exact cancellation of the affine baseline under differences, unit-history norm bound, and arbitrarily large origin terms inside any relative neighborhood of any positive-radius closed history ball.
- `WeilLogShiftUniformBallGenericity.lean`: open dense tail events; dense residual nowhere-bounded and nowhere-signed-summable histories in every such ball; meagre eventual-boundedness and summability exceptions; arbitrarily small uniform perturbations of every bounded history with nowhere bounded moments.
- Both leaves compiled/exported using `lake --old env lean ... -o ...`, exit 0 and no diagnostics. Perturbation leaf passed after two notation repairs; genericity leaf passed first compilation. No later source edits.
- All twelve public theorems audited exactly once by scratch `#print axioms`, exit 0. Each depends on exactly `[propext, Classical.choice, Quot.sound]`.
- Both imports occur exactly once. Index refresh exited 0; all twelve theorem rows, two definitions, and one abbreviation verified under their correct modules. Scoped source checks passed.
- Global lint exits 1 solely for fourteen unrelated unwired modules: `RHTower.XiLaguerrePolyaFirstOrderPreimage`; `HTGeometry.MatrixWienerHopfFredholm`; `HTGeometry.QKrawtchoukPolynomialCompleteness`; and these eleven `HTGeometry.PaperStableCoordinate` leaves: `AssociatedGradedPresentation`, `FilteredRees`, `GradedPresentationKernel`, `GradedPresentationMap`, `GradedRelation`, `ObstructionDefinitions`, `PrincipalInitialRelation`, `ReesCoefficientCriterion`, `WeightedInitial`, `WeightedInitialIdeal`, `WeightedInitialKernel`. No diagnostic names either new leaf. These modules remain untouched.
- No new analytic premises or axioms, proof gaps, raised limits, numerical experiments, external sources, full builds, commits, or subagents.

## Proved follow-up: exponentially shrinking errors

`WeilLogShiftExponentialPrecision` and `WeilLogShiftExponentialPrecisionGenericity` now prove this conjecture for every 0<=sigma<4-pi, every bounded center h0, and every epsilon>0. There exists a bounded history h with |h(k)-h0(k)|<=epsilon exp(-sigma(k+2)) at every coordinate and unbounded absolute moment terms in every tail at every real shift. Such errors form a dense residual set of unit-ball error parameters u in the supremum topology. See `weil-logshift-exponential-precision.md` for verification.

The proof generalizes the origin exponential envelope and the affine ball-perturbation argument. The decaying multiplication map is not open in the ambient supremum norm, so the new parameter-space category proof is essential. The original APIs remain available as specializations. No claim is made at sigma>=4-pi or that this threshold is optimal.

Next conjecture: nonsummability of the response to one fixed history-coordinate impulse. That could test whether any positive precision envelope allowing that coordinate admits signed-divergent histories, beyond the present diagonal rate range. It remains unproved.

## Working plan

1. [x] Inspect local frontier and close the paper argument.
2. [x] Verify current norm, affine-map, and closed-ball completeness APIs. Scratch audit exited 0, including complete-space and Baire instances for arbitrary closed history balls.
3. [x] Formalise the ball perturbation and dense residual all-shift theorem. Both leaves compiled/exported successfully; genericity leaf passed first compilation.
4. [x] Compile leaf, audit public declarations, wire import, index, lint. Only the fourteen unrelated global wiring errors above remain.
5. [x] Record survivor, next conjecture and memories; clean owned scratch.

## Log

- 2026-10-09 — previous increment proved product-cube residual divergence. Current target strengthens topology and permits any bounded center. No web, external papers, experiments, new analytic assumptions, or subagents.
- 2026-10-09 — local API audit passed. Constructive leaf `WeilLogShiftUniformBallPerturbation.lean` drafted with exact affine cancellation, unit-history norm bound, and a perturbation inside every relative uniform neighborhood. First compilation running. Category consequences will be separated into `WeilLogShiftUniformBallGenericity.lean`.
- 2026-10-09 — first constructive compilation found two elaboration issues: function addition needed an explicit lambda, and the real triangle inequality needed an explicit norm-to-absolute-value conversion. Both repaired without changing the argument; compilation resumed. Genericity leaf drafted for every positive-radius closed ball, with meagre exceptions and arbitrarily small uniform perturbations.
- 2026-10-09 — corrected perturbation leaf compiled/exported with exit 0 and no diagnostics. Both imports are unique and source checks pass. Genericity compilation now running; an exhaustive audit for all twelve public theorems is prepared.
- 2026-10-09 — genericity leaf compiled/exported with exit 0 and no diagnostics on first compilation. Every positive-radius closed supremum ball now has the dense residual nowhere-bounded family. Twelve-theorem axiom audit running. Follow-up search began for exponentially shrinking history errors; the first exact history/exponential query found no declarations and was broadened.
- 2026-10-09 — all twelve axiom audits passed, with exact standard axiom sets and complete name coverage. Imports and all fifteen index rows verified. Latest lint has only the fourteen unrelated wiring errors above. Card moved to formalized; predecessor cards and failed-route positive survivor updated. Next conjecture: exponentially shrinking errors at any strict decay rate below 4-pi.
- 2026-10-09 — dedicated result memory written and three predecessor memories updated. All seven owned scratch files removed and absence verified; former in-progress card absent. All owned jobs terminal. Increment complete; the indefinite corpus research goal remains active.
