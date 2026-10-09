# Uniform bounded-history moment receiver — verified progress

Only local Lean corpus and installed Lean API checks; NO web/external papers. Active endless corpus goal remains ACTIVE. Previous acknowledgment-only turn was classified no progress; this turn made verified progress.

## New leaf
`formal/GaloisForLFunctions/RHTower/WeilLogShiftUniformMomentReceiver.lean`, 269 lines, imports BoundedCubeGenericity plus Mathlib Bounded.Normed and Operator.BanachSteinhaus. Thirteen public declarations (five definitions, eight theorems), all namespace RHTower:
- `weilLogShiftRecoveryInverse_affine c d h g`: Inv(c*h+d*g)=c*Inv(h)+d*Inv(g)+(1-c-d)*Inv(0). Exact normalized affine inverse.
- `weilLogShiftRecoveryMoment y h n := weilDeviation (Inv h) n * pairedLogKernel y n`.
- `weilLogShiftRecoveryMomentCLM y n : (ℕ →ᵇ ℝ) →L[ℝ] ℝ`, evaluates to Moment(y,h,n)−Moment(y,0,n); `_apply` theorem.
- `weilLogShiftRecoveryMomentPanel y N sign`, sign:ℕ→Bool, finite sum of ± centered coordinate CLMs over range N; `_apply` theorem.
- `weilLogShiftBoundedHistoryBCF h`: cube history embedded as bounded continuous real sequence; `norm_weilLogShiftBoundedHistoryBCF_le h` gives norm≤1.
- `WeilLogShiftBoundedMomentSummable y`: every unit-cube history has Summable signed weighted moments at y.
- `weilLogShiftRecoveryMomentPanel_bounded hs`: universal cube summability forces ∃C≥0,∀N sign, norm(panel)≤C.
- `weilLogShiftBoundedMomentSummable_iff_operator_bound y`: universal cube summability iff zero-history summability AND that uniform panel operator-norm bound.
- `weilLogShiftBoundedMomentSummable_iff_uniform_bound y`: universal cube summability iff ∃B,∀cube h,N, sum_{n<N} norm(Moment(y,h,n))≤B.
- `weilLogShiftBoundedMomentSummable_lipschitz hs`: ∃C≥0,∀bounded h,g,N, sum_{n<N} norm(Moment(y,h,n)−Moment(y,g,n))≤C*norm(h−g).

## Proof and interpretation
Affine finite probe formula + uniqueness gives inverse affine law. Centered coordinates linear and continuous via product inverse and continuous bounded-sequence coordinate evaluations. Scaling arbitrary bounded h by norm(h)+1 into cube and subtracting zero-history moments yields centered summability. Signed finite panels pointwise bounded by absolute centered series. Banach–Steinhaus yields common operator-norm bound. Choose signs matching centered terms to bound sums of their norms; add baseline absolute moment. Converse uses summable_of_sum_range_le. CLM subtraction gives Lipschitz differences.
This is an unconditional EXACT receiver equivalence; no new analytic assumption is used to assert convergence. Interior convergence |y|<log2 is STILL OPEN, including y=0. CORRECTION: the baseline premise is now FORMALLY DISCHARGED by the bounded arithmetic anchor in WeilLogShiftFiniteMatrixReceiver. The prior proof retained it; affine structure did not establish independence. See mem:research/weil-logshift-finite-matrix-receiver-2026-10-09. No full-real-cutoff boundedness result or RH claim.

## Verification
Full new leaf compile/export `lake --old env lean GaloisForLFunctions/RHTower/WeilLogShiftUniformMomentReceiver.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilLogShiftUniformMomentReceiver.olean` exit0/no diagnostics on first compilation. All13 public declarations exactly [propext,Classical.choice,Quot.sound], complete scratch audit exit0. Unique umbrella import and all13 correct unique API rows verified after index refresh exit0. Source/card whitespace/conflict/diff checks passed. No source changes after successful compile.
LATEST GLOBAL LINT exit1, exactly NINE unrelated unwired modules: RHTower.JensenTrivialZeroProducts; HTGeometry.BandKernelOperators, ConeKernelCrossedProduct, GibbsSizeBiasEntropy, HyperbolicSineScaleMonotonicity, PaperStableCoordinate.Stabilization, PaperStableCoordinate.StabilizationEmbedding, QKrawtchoukEdgeMoments, RealGroupCStarFaithful. No diagnostic names new leaf. These were not changed. Full captured stderr audit supersedes prior lint snapshots.
Cards: new 3-formalized/weil-logshift-uniform-moment-receiver.md; bounded-cube-genericity card updated with follow-up. No agents, full/umbrella builds, commits, experiments, raised limits, new axioms or proof gaps.

## APIs and next frontier
Current global `sum_apply` and `smul_apply` replace deprecated ContinuousLinearMap aliases. Use `norm_add_le`; `abs_add` is not present. `continuous_of_discreteTopology` generic positional args include DiscreteTopology after source topology; concrete example avoids misapplication. BCF.ofNormedAddCommGroup constructs cube embedding, BCF.evalCLM ℝ k gives coordinate continuity. CompleteSpace of ℕ→ᵇℝ inferred. Summable.sum_le_tsum works via hs.sum_le_tsum range (fun n _=>norm_nonneg _).
Next conjecture: finite triangular-prefix dependence makes each panel's operator norm exactly a finite sum of absolute column responses on coordinate histories. This would turn the operator receiver into explicit finite matrix inequalities. Not proved yet; no claim about actual interior estimates. A nontrivial quantitative bound on inverse remains needed.

Owned scratch cleanup is recorded in the card after this memory write; all jobs are terminal.

## Verified follow-up
The existing private centered partial-sum bound is now public as `sum_norm_weilLogShiftRecoveryMomentCLM_le`; all three old callers use it. This leaf is now270 lines/14 public declarations; all original public statements unchanged. Recompiled/exported cleanly and all14 re-audited as part of32 declarations across this and FiniteMatrixReceiver. The finite matrix receiver and bounded arithmetic anchor are now proved; see the follow-up memory for current state and the newer five-error lint snapshot.


## Verified follow-up: smooth-edge origin obstruction (2026-10-09)
Earlier statements that origin/interior universal signed summability remained open are historical. The new smooth cutoff edge bound proves exponential growth of the inverse diagonal already at origin. Universal bounded-history SIGNED moment summability now fails at EVERY real shift. Every finite cube prefix has an extension with nonsummable signed moments simultaneously at all real shifts; these histories are dense, and each finite matrix budget is unbounded. No residual-origin, one-sided-origin, every-history, or full-positive-real-cutoff claim follows. Exact positive survivor, 11 compiled/axiom-audited theorems, and current three unrelated lint wiring errors are recorded in `mem:research/weil-logshift-smooth-edge-origin-obstruction-2026-10-09`. Final card is docs/drafts/pipeline/3-formalized/weil-logshift-smooth-edge-origin-obstruction.md; old backlog/in-progress copies removed. Next frontier: residual signed nowhere summability using open tail excursions and origin exponential growth.
