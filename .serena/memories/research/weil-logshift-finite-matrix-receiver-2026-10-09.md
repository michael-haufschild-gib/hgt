# Finite matrix receiver + baseline premise discharged — verified progress

ONLY local Lean corpus and installed Lean API checks. No web or external papers. Previous turn and this turn made verified progress. Endless corpus goal remains ACTIVE. No subagents. All owned jobs terminal and seven owned scratch files removed, absence verified.

## New leaf
`formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteMatrixReceiver.lean`, 285 lines, imports UniformMomentReceiver. Eighteen public declarations (4 defs,14 theorems), namespace RHTower:
1. `weilLogShiftRecoveryInverse_prefix h g M hh n hn`: if histories agree at every k<M and n<M+2, normalized inverse coefficients agree at n.
2. `weilLogShiftRecoveryMomentCLM_prefix y M h g hh n hn`: same causal property for centered CLM coordinates, bounded histories.
3–4. `weilLogShiftRecoveryUnitHistory k : ℕ→ᵇℝ`, `_apply k j`: if j=k then1else0.
5. `weilLogShiftRecoveryMomentResponse y n k := MomentCLM y n (UnitHistory k)`.
6. `weilLogShiftRecoveryMomentResponse_eq_zero y n k hn`: zero when n<k+2.
7–8. `weilLogShiftRecoveryMomentResponse_diagonal y k`: response y(k+2)k = pairedLogKernel y(k+2)/(sqrt(k+2)*RecoveryWeight(k+2)(k+2)); `_diagonal_pos y k`.
9. `weilLogShiftRecoveryMomentPanel_eq_columns y N sign h`: Panel h = sum_{k<N−2} h k * Panel(UnitHistory k).
10. `norm_weilLogShiftRecoveryMomentPanel_eq_columns y N sign`: norm Panel = sum_{k<N−2} norm(Panel(UnitHistory k)). Exact norm, attained by a sign history in proof.
11. `weilLogShiftRecoveryMatrixBudget y N (sign:Fin N→Bool) := sum_{k:Fin(N−2)} |sum_{n:Fin N} (if sign n then1else−1)*Response y n k|`.
12. `norm_weilLogShiftRecoveryMomentPanel_eq_matrix y N sign`: norm Panel = MatrixBudget y N (fun n=>sign n).
13. `exists_bound_weilLogShiftArithmeticHistory`: ∃C,∀k,norm(RecoveryHistory (fun n=>(ArithmeticFunction.vonMangoldt n:ℝ)) k)≤C.
14. `weilLogShiftArithmeticHistoryBCF : ℕ→ᵇℝ`: canonical bounded arithmetic history; constructor chooses only its bound.
15. `weilLogShiftRecoveryMoment_arithmetic_zero y n`: Moment y ArithmeticHistoryBCF n=0.
16. `weilLogShiftRecoveryMomentCLM_sub_arithmetic y n h`: MomentCLM y n (h−ArithmeticHistoryBCF)=Moment y h n.
17. `weilLogShiftBoundedMomentSummable_iff_panel_bound y`: universal unit-cube summability iff ∃C≥0,∀N sign,norm(Panel y N sign)≤C. NO baseline moment premise.
18. `weilLogShiftBoundedMomentSummable_iff_matrix_bound y`: universal unit-cube summability iff ∃C≥0,∀N (sign:Fin N→Bool),MatrixBudget y N sign≤C. NO baseline moment premise.

## Existing leaf change
`WeilLogShiftUniformMomentReceiver.lean` now270 lines/14 public declarations. Promoted private `sum_norm_le_panel_bound` to public `sum_norm_weilLogShiftRecoveryMomentCLM_le`, docstring added; same proof and all3 callers renamed. It says: hC:∀N sign,norm Panel≤C ⇒ ∀bounded h,N,sum_{n<N}norm(MomentCLM y n h)≤C*norm h. All13 previous public statements retained. New leaf reuses this estimate instead of duplication.

## Mechanism / correction
Triangular finite injectivity + zero head gives causality. Expand truncated bounded histories in coordinate histories. Finite functional norm is the sum of absolute columns: triangle inequality gives upper bound, matching coordinate signs attain it. No dependence on infinite sign tails remains. Diagonal formula follows first-difference with unit sample change1.
CRITICAL STRONGER DISCOVERY: the former zero-history summability premise is REDUNDANT. For λ=vonMangoldt all deviations vanish, so `tendsto_logShift_probe_of_summable_sample (m:=2)` applies unconditionally. Compose with `tendsto_weilLogShiftRecoveryCutoff`; convergent sequence has bounded norm range. Restrict to k+2 to construct arithmeticHistoryBCF. Normalized inverse preserves deviations (`weilDeviation_recoveryInverse_history`), so its moments vanish. Subtract this bounded anchor: full affine moment is centered linear response at h−b. Uniform panels therefore bound absolute partial moments for every bounded h, giving summability without a baseline hypothesis.
The prior card/memory assertion that baseline summability could not be omitted merely because inverse is affine was too strong. Both corrected; older iff-with-baseline remains true but redundant. Prior memory points here.

## Verification
Both touched leaves final compile/export with `lake --old env lean <leaf> -o <olean>` exit0/no diagnostics; no subsequent source edits. First finite-matrix pass needed two finite-sum elaboration fixes; anchor extension needed explicit BCF coe equality. All32 public declarations across both leaves exactly [propext,Classical.choice,Quot.sound], exhaustive scratch audit exit0/name coverage verified. Nineteen new public declarations, thirteen old retained. Both unique umbrella imports and all32 unique/correct API rows checked after index exit0. Scoped source/card whitespace/conflict/diff checks passed. Seven owned /tmp files cleaned after all jobs terminal.
LATEST GLOBAL LINT exit1 ONLY FIVE unrelated unwired HTGeometry modules: BandKernelOperators, ConeCrossedProductFaithful, ConeKernelCrossedProduct, QKrawtchoukEdgeIndeterminacy, RealGroupCStarFaithful. No diagnostics for touched leaves, no edits to these unrelated files. This supersedes prior snapshots.
Cards: new 3-formalized/weil-logshift-finite-matrix-receiver.md; old uniform-moment card updated/corrected, original verification labeled historical. No new assumptions/axioms/gaps, numerical experiments, limit hacks, full/umbrella builds, commits, or subagents.

## Lean details
- BCF finite-sum evaluation did not simplify using root sum_apply/smul_apply alone. `simp [historyTruncation, weilLogShiftRecoveryUnitHistory_apply, mul_ite, hj]` solved it.
- `Fin.sum_univ_eq_sum_range` needs explicit function and N for these nested sums; generic simp could not infer the natural-index function. Use two explicit conversions.
- In final summability proof, make coercion equality explicit: `have hcoe : (weilLogShiftBoundedHistoryBCF h : ℕ→ℝ)=weilLogShiftBoundedHistoryValues h := rfl`; then `simpa only [MomentCLM_sub_arithmetic,hcoe] using sum_norm_...`.
- `ht.norm.bddAbove_range` checked in scratch for real sequence convergence atTop. Anchor proof does not need to simplify the actual finite limit.

## Next frontier / limits
Actual universal convergence for any |y|<log2, including0, STILL OPEN. Exact criterion now only finite matrix budgets; no separate affine baseline obstruction remains. Investigate quantitative inverse matrix bounds. A candidate next step is necessary diagonal summability from antipodal recovery, then assess off-diagonal responses; diagonal summability has NOT been shown sufficient. Do NOT replace ∞→1 finite-sign budget by entrywise absolute sum without proof. Bounded arithmetic anchor may have norm>1, so this alone does not exhibit a convergent history inside the fixed unit cube. No new full-real-cutoff boundedness result or RH claim.

## Verified follow-up: smooth-edge origin obstruction (2026-10-09)
Earlier statements that origin/interior universal signed summability remained open are historical. The new smooth cutoff edge bound proves exponential growth of the inverse diagonal already at origin. Universal bounded-history SIGNED moment summability now fails at EVERY real shift. Every finite cube prefix has an extension with nonsummable signed moments simultaneously at all real shifts; these histories are dense, and each finite matrix budget is unbounded. No residual-origin, one-sided-origin, every-history, or full-positive-real-cutoff claim follows. Exact positive survivor, 11 compiled/axiom-audited theorems, and current three unrelated lint wiring errors are recorded in `mem:research/weil-logshift-smooth-edge-origin-obstruction-2026-10-09`. Final card is docs/drafts/pipeline/3-formalized/weil-logshift-smooth-edge-origin-obstruction.md; old backlog/in-progress copies removed. Next frontier: residual signed nowhere summability using open tail excursions and origin exponential growth.


## Verified follow-up: supremum-norm ball genericity (2026-10-09)
The stronger uniform-topology conjecture is now proved by `WeilLogShiftUniformBallPerturbation` and `WeilLogShiftUniformBallGenericity`. Every positive-radius closed supremum ball around ANY bounded history has a dense residual subset with absolute moment terms unbounded in every tail at every real shift. Every bounded center admits arbitrarily small uniform perturbations with this property. Thus the arithmetic anchor need not have norm at most one for the local instability result. Exact affine baseline cancellation and opposite ball-preserving coordinate perturbations are the positive mechanism. All12 new public theorems compiled and audited with exactly the standard axioms. No one-sided origin, every-perturbation, generic norm-to-infinity, or full real-cutoff claim. Next conjecture: exponentially shrinking errors at strict rates below 4-pi. See `mem:research/weil-logshift-uniform-ball-genericity-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-uniform-ball-genericity.md; latest global lint has14 unrelated wiring errors, listed there.


## Verified follow-up: exponentially shrinking errors (2026-10-09)
The exponential-precision conjecture is now proved for every 0<=sigma<4-pi and every positive amplitude around every bounded center. Errors obey epsilon*exp(-sigma*(k+2)) coordinatewise, yet yield unbounded absolute moment terms in every tail at every real shift. Bad ERROR PARAMETERS in the closed supremum unit ball are dense residual; no open-map transfer to the ambient image is asserted. Origin lower envelope now exceeds every strict rate below4-pi; the affine ball perturbation mechanism is generalized with original APIs retained. All36 public theorems across all5 affected leaves compiled and passed exact standard-axiom audit;43 public API rows verified. See `mem:research/weil-logshift-exponential-precision-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-exponential-precision.md. No conclusion at/beyond4-pi or optimality claim. Next conjecture tests nonsummability of one FIXED response column, which could remove the rate restriction for signed-divergent witnesses. Latest lint still has14 unrelated errors, but their module list changed; use the new memory/card list.
