# Exact antipodal gain and simultaneous diagonal obstruction — verified progress

ONLY local Lean corpus and installed Lean API/definition checks. NO web or papers. Previous and current turns made verified progress. Goal stays ACTIVE. No subagents. All owned jobs terminal; eight explicit owned scratch files removed, absence verified.

## Exact gain, existing leaf
`formal/GaloisForLFunctions/RHTower/WeilLogShiftBoundedRecoveryNoGo.lean` now191 lines/seven public theorems.
NEW `exists_antipodal_recovery_after_prefix_with_gain height M`: ∃λ, Qλ(k+2)=height k for k<M; |Qλn|=1 for n≥M+2; and for every n≥M+2,
`w_nn * |λn−Λn| = 1 + |Q_n (RecoveryPrefix Λ λ n)|`.
Same adaptive builder; target +1 if current probe≤0, else−1. Absolute correction is exactly1+|q|. Original `exists_antipodal_recovery_after_prefix` now specializes this result plus prior diagonal/full-kernel bound. All SIX old public statements retained, including both counterexamples.

## New leaf
`formal/GaloisForLFunctions/RHTower/WeilLogShiftDiagonalObstruction.lean`,162 lines, imports FiniteMatrixReceiver. Seven public declarations (one def,six theorems):
- `half_le_weilLogShiftRecoveryMomentResponse_log_two k`: 1/2≤Response(log2)(k+2)k.
- `not_summable_weilLogShiftRecoveryDiagonal_log_two`: ¬Summable(fun k=>Response(log2)(k+2)k).
- `exists_weilLogShiftBoundedHistory_prefix_diagonal_minorant height M`: ∃extended cube history, agrees with height at k<M; |Values extended k|=1 for k≥M; ∀k≥M,∀real y, Response y(k+2)k≤norm(Moment y (Values extended)(k+2)). Single extension works at every real shift.
- `weilLogShiftBoundedMomentSummable_diagonal hs`: universal cube summability at y forces Summable(fun k=>Response y(k+2)k).
- `WeilLogShiftDiagonalObstruction height`: ∀real y, nonsummable diagonal series⇒nonsummable Moment y(Values height).
- `exists_weilLogShiftBoundedHistory_prefix_diagonal_obstruction height M`: ∃extended matching every k<M and satisfying that simultaneous obstruction.
- `dense_weilLogShiftDiagonalObstruction`: these histories form a dense set in the bounded product cube. NO new residual/category-measure claim.

Proof: divide exact positive gain by sqrt(n)*w_nn, multiply P_y(n)>0, use inverse-history preservation of deviations. Summability descent removes first2 then firstM terms using summable_nat_add_iff and nonnegative comparison. Prefix extensions converge coordinatewise as M→∞, yielding density. Diagonal log2≥1/2 is direct from existing w_nn≤2P_log2/sqrt; terms cannot tend0.

## Verification / scope
Both touched leaves final compile/export `lake --old env lean <leaf> -o <olean>` exit0/no diagnostics, each on first compilation. No later source edits. All14 public declarations across both exactly [propext,Classical.choice,Quot.sound]; exhaustive scratch audit exit0 and coverage checked. Eight new public declarations; six old retained. Both imports unique, index exit0, all14 unique/correct API rows checked. Scoped source/card whitespace/conflict/diff checks passed. No new analytic assumptions, gaps, axioms, numeric experiments, raised limits, full builds, commits, or agents.
LATEST GLOBAL LINT exit1 ONLY TEN unrelated unwired HTGeometry modules: BandKernelOperators, CircleSymbolGroupCStar, ConeCrossedProductFaithful, ConeKernelCrossedProduct, PaperStableCoordinate.ZeroFiber, PaperStableCoordinate.ZeroFiberExact, PaperStableCoordinate.ZeroFiberSpecialization, PaperStableCoordinate.ZeroFiberTransport, QKrawtchoukCompanionDeterminacy, RealGroupCStarFaithful. No diagnostics for touched leaves. No edits to those modules. This supersedes prior lint snapshots.
Cards: new3-formalized/weil-logshift-diagonal-obstruction.md; prior bounded-recovery-no-go and finite-matrix cards updated; failed-route bounded-recovery-moment-control card records exact new positive survivor and paper/Lean status.

## PRIORITY NEXT: actual smooth edge may kill origin control
Backlog card already written: `docs/drafts/pipeline/0-backlog/weil-logshift-smooth-edge-origin-obstruction.md`. READ before new work. No Lean code for it yet. This is a real analytic target, not another receiver reformulation.
Observed exact corpus definitions:
- TruncatedRiemannKernelWeilEnergy.lean:33 bulkCutoff L u = smoothTransition(L−u)*smoothTransition(L+u).
- WeilFullConeRiemannKernelRigidity.lean:96 truncated real kernel=riemannKernelReal u*bulkCutoff L u.
- WeilPositivityMajorantRigidity.lean:436 truncatedAutocorr=integral of two truncated real kernels.
- Actual installed Mathlib Analysis/SpecialFunctions/SmoothTransition.lean read:39 expNegInvGlue x=ifx≤0then0else exp(−x⁻¹);146 Real.smoothTransition x=glue x/(glue x+glue(1−x)). Local RiemannKernelFloquetBlockTests.lean:172 unfolds this quotient.
- WeilLogShiftLocalDecayThreshold.lean:40 `exists_paired_logKernel_upper_of_lt_rate {y a}(ha0:0<a)(ha:a<logKernelCriticalRate y)` gives∃C>0,∀n≥1,P_y(n)≤Cexp(−a*n).
- same:77 `exists_paired_logKernel_lower_of_rate_lt {y b}(hb:logKernelCriticalRate y<b)` gives∃D>0,∀ᶠn atTop,Dexp(−b*n)≤P_y(n).
Critical rates areπ atlog2 and2π at0.
Search `research 'smoothTransition expNegInvGlue' --any --mode lexical --no-refresh --json` already completed:21hits11eligible, no exponential edge bound found. Exhaustive source rg had72hits, mostly NonperturbativeQuantumRecurrenceSeparationLaw glue flatness; no needed cutoff product estimate. Do NOT reread same searches unnecessarily.

PROPOSED, NOT PROVED: overlap margin at diagonal δ_n=log(n+1)−logn≤1/n. Two small cutoff arguments a=L−t,b=L+t−z sumδ_n; positive a,b≤1/2 for n≥2. Quotient formula should imply S(a)≤exp(2−1/a). Product≤exp(4−1/a−1/b)≤exp(4−4/δ_n)≤exp(4−4n); other two cutoff factors≤1; outside overlap one factor0. Integrating should give K_Ln(z_n)≤exp(4−4n)K(z_n). Thus sqrt(n)w_nn≤2exp(4−4n)P_log2(n). Choose0<a<π and2π<b<a+4, possible sinceπ<4. Existing upper/lower kernel envelopes then give origin diagonal≥c exp((a+4−b)n) eventually, hence nonsummable. Antipodal domination would imply dense bounded histories with no summable moment at ANY shift (use inward transfer from any y to0). Residual genericity needs a separate proof.
This cutoff estimate and origin conclusion are CONJECTURAL, not Lean results; verify all inequalities/integration hypotheses and actual dependencies. No numerical experiments. Goal is to discharge the genuinely open origin question. Current verified state STILL leaves interior convergence open, including0. Diagonal summability is necessary, NOT proved sufficient. Do not replace finite-sign ∞→1 matrix budgets by entrywise sums without proof.

## API details
summable_nat_add_iff k : Summable(fun n=>f(n+k)) ↔ Summable f. Use .mpr to drop finite heads, .mp to restore. Summable.of_nonneg_of_le arguments are nonnegative minorant, pointwise bound, summable majorant. Dense proof copied existing bounded-cube coordinate convergence API. Exact gain proof handles q≤0 andq>0 by abs_of_nonpos/abs_of_pos; no new builder.

## Verified follow-up: smooth-edge origin obstruction (2026-10-09)
Earlier statements that origin/interior universal signed summability remained open are historical. The new smooth cutoff edge bound proves exponential growth of the inverse diagonal already at origin. Universal bounded-history SIGNED moment summability now fails at EVERY real shift. Every finite cube prefix has an extension with nonsummable signed moments simultaneously at all real shifts; these histories are dense, and each finite matrix budget is unbounded. No residual-origin, one-sided-origin, every-history, or full-positive-real-cutoff claim follows. Exact positive survivor, 11 compiled/axiom-audited theorems, and current three unrelated lint wiring errors are recorded in `mem:research/weil-logshift-smooth-edge-origin-obstruction-2026-10-09`. Final card is docs/drafts/pipeline/3-formalized/weil-logshift-smooth-edge-origin-obstruction.md; old backlog/in-progress copies removed. Next frontier: residual signed nowhere summability using open tail excursions and origin exponential growth.


## Verified follow-up: product-cube residual origin genericity (2026-10-09)
The origin residual question is now settled by `WeilLogShiftKernelTailOrder` and `WeilLogShiftBoundedOriginGenericity`: absolute moment terms are unbounded in every tail at EVERY real shift on a single dense residual subset of the unit product cube. Even eventual boundedness at one history-dependent shift is meagre; any signed summable moment is also meagre. Positive survivors include arbitrary fixed outward kernel gain, origin diagonal tending to infinity, and finite-prefix bounded extensions with origin norm tending to infinity. All12 new public theorems compiled and axiom-audited with exactly the standard set. This does not assert generic norm convergence to infinity, one-sided origin divergence, or supremum-norm genericity. The latter is the next conjecture. See `mem:research/weil-logshift-bounded-origin-genericity-2026-10-09` and docs/drafts/pipeline/3-formalized/weil-logshift-bounded-origin-genericity.md. Latest global lint has only two unrelated wiring errors, recorded there.
