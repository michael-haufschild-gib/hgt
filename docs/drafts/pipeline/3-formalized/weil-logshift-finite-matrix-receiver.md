# Finite matrix receiver for bounded recovery moments

- **ID:** weil-logshift-finite-matrix-receiver
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean corpus only: triangular recovery, affine inverse, uniform moment receiver.
- **Target:** Replace signed-panel operator norms by exact finite sums of absolute column responses; derive an equivalent receiver using finite sign vectors and a triangular response matrix with explicit diagonal. Discharge the separate zero-history summability premise using a bounded arithmetic anchor.

## Dependency-closed paper proof

Equality of the first M history coordinates forces equality of reconstructed coefficients below M+2, by the existing finite triangular injectivity theorem and zero-head normalization. Thus a panel of the first N moment coordinates depends only on history indices below N−2. Truncate a bounded history to those indices and expand it in coordinate histories e_k. Linearity shows that a panel acts as the finite dot product of history values with its responses on e_k.

For a finite-coordinate real linear functional, the supremum norm is the sum of the absolute column responses. The upper bound is the triangle inequality and the supremum bound on history coordinates. A bounded history taking the sign of each column response attains the bound. Consequently the uniform moment receiver is exactly zero-history summability plus one bound on these finite signed matrix expressions, uniform in cutoff and finite sign choice.

The response to e_k vanishes in coefficient rows n<k+2. At n=k+2, triangular first-difference gives coefficient change 1/w_nn, so the weighted centered moment response is P_y(n)/(sqrt(n)*w_nn), strictly positive. This identifies the matrix entries on and above its shifted diagonal without any analytic assumption.

### Stronger receiver: remove the affine baseline premise

The corpus's fixed-probe limit theorem applies to λ=von Mangoldt because every deviation is zero. Composing with cofinal recovery cutoffs yields a convergent, hence bounded, arithmetic recovery history b. Reconstruction preserves its zero deviation. For every bounded history h, its moment sequence is therefore exactly the centered linear response at h−b. A uniform signed-panel norm bound C consequently bounds every absolute partial moment by C‖h−b‖, and by C(1+‖b‖) on the unit cube. This proves universal summability without separately assuming the zero-history moment. Thus the sole finite-matrix bound is an exact receiver; zero-history summability follows from it.

The previous card's claim that the baseline premise could not be omitted was too strong: the affine structure explains why the first proof retained it, but does not establish independence. This anchor argument resolves that gap.

## Plan and gates

1. [x] Corpus novelty search and installed Lean API checks.
2. [x] Formalize finite-prefix dependence, unit histories, response matrix support and diagonal.
3. [x] Prove exact finite-column norm formula and equivalent finite-sign receiver with baseline.
4. [x] Prove bounded arithmetic anchor and remove baseline premise; expose shared centered partial-sum bound rather than duplicate it.
5. [x] Compile touched leaves, audit all public declarations, wire umbrella, refresh index, run lint.
6. [x] Update memory and clean scratch.

## Final statement

Let R_y(n,k) be the centered weighted inverse response to the unit history at k. For a finite sign vector σ of length N, define

`B_y(N,σ) = Σ_{k<N−2} |Σ_{n<N} ε_σ(n) R_y(n,k)|`, where ε is +1 or −1.

For every real y, the following are equivalent:

1. Every unit-bounded history has a summable signed moment at y.
2. All finite signed centered moment panels have uniformly bounded operator norms on bounded histories.
3. There exists C≥0 such that `B_y(N,σ)≤C` for every N and every finite sign vector σ.

No separate zero-history summability premise remains. The finite norm formula is exact, not a sufficient majorant. In particular, it must not be replaced by an entrywise absolute matrix sum or by diagonal summability without a further proof.

## Formal results

New leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteMatrixReceiver.lean`, 285 lines, eighteen public declarations (four definitions, fourteen theorems).

- `weilLogShiftRecoveryInverse_prefix`, `weilLogShiftRecoveryMomentCLM_prefix`: agreement through the first M history coordinates determines reconstructed coefficients and centered moment rows below M+2.
- `weilLogShiftRecoveryUnitHistory`, `weilLogShiftRecoveryUnitHistory_apply`: bounded coordinate histories.
- `weilLogShiftRecoveryMomentResponse`: weighted response matrix.
- `weilLogShiftRecoveryMomentResponse_eq_zero`: zero for n<k+2.
- `weilLogShiftRecoveryMomentResponse_diagonal`, `_diagonal_pos`: exact positive entry `P_y(k+2)/(sqrt(k+2)*w_(k+2,k+2))`.
- `weilLogShiftRecoveryMomentPanel_eq_columns`: exact finite history-coordinate expansion, using only k<N−2.
- `norm_weilLogShiftRecoveryMomentPanel_eq_columns`: exact sum of absolute column responses, attained by a sign history in the unit cube.
- `weilLogShiftRecoveryMatrixBudget`, `norm_weilLogShiftRecoveryMomentPanel_eq_matrix`: expression using only finite indices and a `Fin N → Bool` sign vector, equal to the panel operator norm.
- `exists_bound_weilLogShiftArithmeticHistory`, `weilLogShiftArithmeticHistoryBCF`: bounded history of the von Mangoldt coefficient sequence.
- `weilLogShiftRecoveryMoment_arithmetic_zero`: all reconstructed weighted moments of this anchor vanish.
- `weilLogShiftRecoveryMomentCLM_sub_arithmetic`: full moment at h equals centered linear response at h minus the anchor.
- `weilLogShiftBoundedMomentSummable_iff_panel_bound`, `_iff_matrix_bound`: unconditional exact receiver equivalences, with baseline premise discharged.

Existing leaf: `WeilLogShiftUniformMomentReceiver.lean`, now 270 lines, fourteen public declarations. Promoted the existing centered partial-sum estimate to `sum_norm_weilLogShiftRecoveryMomentCLM_le` and updated all three callers. Its proof and all previous public statements are unchanged.

## Verification

- Both touched leaves compile/export with `lake --old env lean <leaf> -o <olean>`, exit 0 and no diagnostics. No source edits after successful final compilation.
- Every one of the 32 public declarations across both leaves has exactly `[propext, Classical.choice, Quot.sound]`; exhaustive scratch audit exited 0, with complete name coverage verified.
- Nineteen new public declarations: eighteen in the new leaf and one exposed helper. Thirteen previous public statements retained.
- Both umbrella imports unique; index refresh exited 0; all 32 API rows checked for unique names and correct modules.
- Scoped whitespace, conflict-marker and `git diff --check` checks passed.
- Global lint exited 1 on exactly five unrelated unwired `HTGeometry` modules: `BandKernelOperators`, `ConeCrossedProductFaithful`, `ConeKernelCrossedProduct`, `QKrawtchoukEdgeIndeterminacy`, `RealGroupCStarFaithful`. No diagnostic names either touched leaf. Those modules were not changed.
- No new analytic assumptions, proof gaps, axioms, experiments, limit increases, web searches, external papers, full builds, commits, or subagents.

## Limits and next work

This exact receiver is now resolved negatively: `WeilLogShiftOriginDiagonalDivergence` proves the finite matrix budgets unbounded at every real shift, including the origin. Smooth cutoff suppression forces exponential growth of the origin inverse diagonal, and every finite bounded prefix admits a single extension with nonsummable signed moments at every shift. The prior diagonal-obstruction result supplied the necessary comparison and dense extension mechanism. Diagonal summability has not been shown sufficient for a different recovery setup. Boundedness of the arithmetic anchor does not establish a summable history inside the specific unit cube. One-sided origin moments and boundedness on the entire real-cutoff axis remain separate questions.

## Log

- 2026-10-09 — previous turn classified verified progress. Began finite matrix reduction from the compiled uniform moment receiver.
- 2026-10-09 — direct lexical corpus search returned 3,250 hits, 1,436 eligible. Inspected relevant recovery-prefix and panel results; no existing exact finite response-matrix norm formula found. Installed APIs checked successfully in scratch, including bounded-function norm bounds and finite-sum conversion.
- 2026-10-09 — new 217-line leaf drafted: sharp prefix dependence, response matrix support and diagonal, exact column norm identity, finite-sign matrix receiver. Thirteen public declarations prepared for exhaustive axiom audit. First leaf compilation running.
- 2026-10-09 — two finite-sum elaboration issues corrected. Complete 227-line leaf compiled/exported with exit 0 and no diagnostics. Corpus probe-limit theorem then exposed bounded zero-deviation arithmetic anchor; extending the target to discharge the previously retained baseline premise.
- 2026-10-09 — direct anchor search returned 3,447 hits, 1,479 eligible; existing fixed-probe convergence and inverse-deviation preservation supply the anchor proof. Exposed the existing centered partial-sum bound as `sum_norm_weilLogShiftRecoveryMomentCLM_le`; all three previous callers use it, and the uniform-receiver leaf recompiles/exports cleanly. Stronger 283-line finite-matrix leaf is compiling; exhaustive audit now covers all 32 public declarations across both touched leaves.
- 2026-10-09 — final bounded-history coercion made explicit. Stronger 285-line leaf compiled/exported with exit 0 and no diagnostics. Both operator and finite-matrix equivalences now omit the baseline summability premise. Umbrella wired; 32-declaration axiom audit and integration checks next.
- 2026-10-09 — all 32 public axiom audits passed with the exact standard set. Index/import checks passed; latest lint has the five unrelated wiring errors listed above. Prior card corrected: affine structure alone did not justify claiming the baseline premise indispensable, and the bounded arithmetic anchor now discharges it formally.
- 2026-10-09 — cross-session memory written, prior memory corrected, all jobs terminal, seven explicitly owned scratch files removed and absence verified. Goal remains active.
