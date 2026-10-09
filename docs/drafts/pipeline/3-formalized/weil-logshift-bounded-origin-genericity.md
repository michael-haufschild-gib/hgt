# Generic nowhere bounded moments inside the bounded recovery cube

Status: formalized and audited. Corpus-only research, 2026-10-09.

## Conjecture

Within the unit product cube of recovery histories, a dense residual set has arbitrarily large absolute reconstructed moment terms in every tail at every real shift simultaneously. Even eventual boundedness at one history-dependent real shift is meagre, as is the existence of any summable signed moment. This stronger statement is now compiled and axiom-audited in Lean.

## Corpus evidence and novelty

- `WeilLogShiftOriginDiagonalDivergence.exists_weilLogShiftOriginDiagonal_exponential_lower` proves a positive exponential lower envelope for the origin inverse diagonal.
- `WeilLogShiftDiagonalObstruction.exists_weilLogShiftBoundedHistory_prefix_diagonal_minorant` preserves any finite bounded history prefix while dominating all inverse diagonals on its tail.
- `WeilLogShiftBoundedCubeGenericity` supplies compact-cube continuity and category machinery, but only treats shifts outside the log-2 interval.
- `WeilLogShiftGenericMomentDivergence` proves stronger two-sided genericity in the unrestricted history space. Its construction does not stay inside the bounded cube.
- Local lexical research found the preceding results; no existing bounded-cube residual origin result appeared. Exhaustive scoped name search follows before implementation. No external sources consulted.

## Dependency-closed argument

1. The positive exponential lower envelope tends to infinity; hence the origin inverse diagonal tends to infinity.
2. For natural thresholds K,N, let U(K,N) contain cube histories with some moment norm exceeding K at an index at least N+2. Every term depends continuously on history, so U(K,N) is open.
3. Given any cube history, apply the finite-prefix diagonal-minorant construction to each prefix length M. Each resulting history lies in U(K,N), since its tail dominates the diverging diagonal. These histories converge coordinatewise to the original history. Thus U(K,N) is dense.
4. Countably intersect U(K,N) over both natural indices. Baire gives a dense residual family with arbitrarily large absolute origin terms in every tail. Natural thresholds imply arbitrary real thresholds by the Archimedean property.
5. Summability would force origin terms to zero, contradicting tail excursions. Any summable signed moment at any real shift transfers inward to origin, so the same residual family is nowhere signed-summable. Its complement is meagre, even though the shift may depend on the history.
6. Stronger all-shift unboundedness follows from a new kernel comparison. If |y|<|c|, choose rates r(c)<b<a<r(y). Existing envelopes give P_y(n)<=C exp(-a n) and P_c(n)>=D exp(-b n) eventually, with C,D>0. For any A>0, D exp((a-b)n) eventually exceeds AC, hence A P_y(n)<=P_c(n) eventually. A<=0 is immediate by positivity. Thus larger absolute shifts eventually dominate any fixed multiple of smaller-shift kernels.
7. For each nonzero shift y, use this comparison with inner shift 0 and multiplier 1. Absolute moments at y eventually dominate origin absolute moments. Hence every origin-tail-unbounded history has unbounded absolute terms in every tail at all real shifts simultaneously. No countable intersection over real shifts is used. Histories with even one eventually bounded moment sequence form a meagre set; summable moments are a subset.

## Limits

No claim about every bounded history, one-sided moments at origin, all positive real cutoffs, or RH. Residual refers to the product topology on the fixed unit cube.

## Formal results

`formal/GaloisForLFunctions/RHTower/WeilLogShiftKernelTailOrder.lean`:

- `eventually_mul_pairedLogKernel_le_of_abs_lt`: strict outward shifts eventually dominate every fixed real multiple of an inner kernel.

`formal/GaloisForLFunctions/RHTower/WeilLogShiftBoundedOriginGenericity.lean`:

- Origin inverse diagonal tends to infinity; every finite bounded prefix admits an extension whose absolute origin terms tend to infinity.
- Every strict absolute origin tail-excursion event is open and dense.
- Origin tail unboundedness is dense and residual, and transfers to all real shifts on the same histories.
- Nowhere-bounded and nowhere-signed-summable histories are dense and residual.
- Eventual boundedness at any real shift, and summability at any real shift, each define a meagre exceptional set.

## Verification

- Both new leaves compiled/exported with `lake --old env lean ... -o ...`, exit 0 and no diagnostics on first compilation. No subsequent source edits.
- Both umbrella imports occur exactly once. Index refresh exited 0; all twelve theorem rows and three definition rows appear under their correct modules.
- Scoped whitespace and forbidden-token checks passed; no proof gaps, new axioms or analytic assumptions, raised limits, numerical experiments, external sources, full builds, commits, or subagents.
- Exhaustive twelve-theorem axiom audit exited 0. Every public theorem was checked exactly once and depends on exactly `[propext, Classical.choice, Quot.sound]`.
- Global lint exits 1 solely for two unrelated unwired modules: `HTGeometry.PaperIntrinsicFiberClocks` and `HTGeometry.QKrawtchoukPinnedQuadrature`. No diagnostic names either new leaf. These errors are outside this task and remain untouched.

## Next conjecture: uniform perturbations

This conjecture is now formally proved, in stronger form, by `WeilLogShiftUniformBallPerturbation` and `WeilLogShiftUniformBallGenericity`: nowhere bounded moments form a dense residual set in every positive-radius closed supremum ball around every bounded history. Every bounded observation history therefore admits arbitrarily small uniform perturbations with unbounded absolute moment terms at every real shift. The dedicated follow-up card is `weil-logshift-uniform-ball-genericity.md`. Its next conjecture concerns exponentially shrinking errors; one-sided origin behavior and full real-cutoff control remain separate questions.

## Working plan

1. [x] Inspect local frontier and prove origin category argument.
2. [x] Audit stronger all-shift unboundedness and local API. Paper argument complete above; scratch API check exited 0 after explicit universe annotations.
3. [x] Formalise exact proved statement without new analytic assumptions. Both leaves compiled/exported with exit 0 and no diagnostics on first compilation.
4. [x] Compile leaf, audit every public theorem's axioms, wire umbrella, index and lint. Only the two unrelated global wiring errors above remain.
5. [x] Record conclusions and next conjecture; clean owned scratch.

## Log

- 2026-10-09 — preceding turn completed smooth-edge origin obstruction and persistence. New target is residual unboundedness; no new numerical experiments or external reading.
- 2026-10-09 — two new leaves written: `WeilLogShiftKernelTailOrder.lean` proves arbitrary outward kernel gain; `WeilLogShiftBoundedOriginGenericity.lean` proves the stronger dense residual nowhere-bounded conclusion and meagre exceptions. Both umbrella imports wired. Sequential leaf compilation underway.
- 2026-10-09 — kernel tail-order leaf compiled/exported with exit 0, no diagnostics, on first compilation. Genericity leaf now compiling; exhaustive audit prepared for all twelve new public theorems.
- 2026-10-09 — genericity leaf also compiled/exported with exit 0 and no diagnostics on first compilation. The stronger dense residual nowhere-bounded conclusion is formally proved. Axiom audit and index refresh started; no source changes after successful builds.
- 2026-10-09 — all twelve axiom audits passed with the exact standard set. Imports, all fifteen index rows, and scoped checks passed. Global lint has only the two unrelated wiring errors listed above. Card moved to formalized; predecessor cards and failed-route positive survivor updated. Supremum-norm genericity is the next conjecture.
- 2026-10-09 — dedicated result memory written and three predecessor memories updated. All six owned scratch files removed and absence verified; former in-progress card absent. All owned jobs terminal. Increment complete; indefinite corpus research goal remains active.
