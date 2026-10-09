# Generic nowhere-summability of recovery histories — verified progress

ONLY local Lean corpus and installed Lean API checks; no web or external papers. Goal remains ACTIVE. This completes the category conjecture left by the previous density increment, not the global research goal.

## New leaf
`formal/GaloisForLFunctions/RHTower/WeilLogShiftGenericMomentDivergence.lean`, imports RecoveryDomainDensity and `GaloisForLFunctions.HTGeometry.CountableResidualIntersection`. Four definitions and eight public theorems:
- `weilDeviation_recoveryInverse_history lam n`: `weilDeviation (Inverse (History lam)) n = weilDeviation lam n`, every n.
- `weilLogShiftRecoveryOriginTerm height n := weilDeviation (Inverse height) n * pairedLogKernel 0 n`.
- `continuous_weilLogShiftRecoveryOriginTerm n`.
- `weilLogShiftRecoveryTailExcursion negative K N := {height | ∃n≥N+2, (K:ℝ) < (if negative then -1 else 1)*OriginTerm height n}`; negative : Bool.
- `isOpen_weilLogShiftRecoveryTailExcursion`, `dense_weilLogShiftRecoveryTailExcursion`.
- `WeilLogShiftTwoSidedExcursions height := ∀negative K N, height∈TailExcursion negative K N`.
- `dense_and_residual_weilLogShiftTwoSidedExcursions`: explicit excursion family dense AND a member of residual(ℕ→ℝ).
- `WeilLogShiftNowhereSummable height := ∀real y, ¬Summable(a(Inverse height)_n P_y(n)) ∧ ¬Summable(excess_n P_y(n)) ∧ ¬Summable(deficit_n P_y(n))`.
- `weilLogShiftNowhereSummable_of_twoSidedExcursions`.
- `dense_and_residual_weilLogShiftNowhereSummable`.
- `isMeagre_weilLogShift_some_summable_moment`: IsMeagre of histories admitting ANY of these three summable moments at ANY real y, even y depending on height.

## Mechanism
Continuous inverse coefficient coordinates make strict one-coordinate signed excursion events open. For density choose sign ε=±1 and coefficient lift of v_n=ε*(K+1)/P_0(n). Splice arbitrary finite target history onto that baseline. At n=M+N+2 its weighted deviation is exactly ε*(K+1), and the histories approach the arbitrary target as M grows. The inverse preserves deviations despite resetting invisible coordinates.
Apply existing `GaloisForLFunctions.HTGeometry.dense_and_residual_setOf_forall` to index Bool×ℕ×ℕ. Positive/negative excursions contradict excess/deficit term→0 at origin. Signed summability implies excess summability by corpus lemma, so fails too. Inward transfer (`summable_kernelPotential_of_abs_le`) reduces convergence at any shift to origin. No uncountable-union category argument.
All realizable profiles remain dense (previous theorem), while the all-empty triple is residual. Category statement, not probability; arbitrary coefficient histories, no RH conclusion. Full real-cutoff boundedness remains unresolved.

## Verification
Final leaf compile/export exit0/no diagnostics. Scratch #print axioms all12 exactly `[propext, Classical.choice, Quot.sound]`, exit0/no diagnostics. New mathlib/category names checked in /tmp with `have := @Name` and BaireSpace(ℕ→ℝ) inferred successfully. Import wired; index refreshed; all12 API rows verified. Scoped whitespace/conflict and git diff checks passed.
LATEST global lint exit1 ONLY unrelated unwired `GaloisForLFunctions.HTGeometry.BandKernelOperators` (one error; tail output duplicated it). Do not repeat earlier two-module snapshots. No modifications to that module.
Card: `docs/drafts/pipeline/3-formalized/weil-logshift-generic-moment-divergence.md`. Prior density card updated from conjecture to proved. No agents/commits/full builds/limits/numerical experiments. All owned jobs terminal; all seven /tmp hgt-weil-moment-category-* scratch files removed and absence verified. Final source/card/diff checks passed.

## Lean details
Use `simp [weilDeviation, hn]` for inverse-history normalization; overly restrictive `simp only [if_pos,if_neg,hn]` left `if False` unsimplified. After `cases negative`, `norm_num [ε]` closes the sign arithmetic; trailing linarith was redundant and removed. `neg_mul` can leave a factor1 in negative-side normalization; include one_mul.
Verified category APIs: `isOpen_iUnion`, `isOpen_lt`, `residual_of_dense_open`, `dense_of_mem_residual`, `countable_iInter_mem`, `Filter.mem_of_superset`, `IsMeagre`. `IsMeagre s` unfolds to `sᶜ ∈ residual X`. `exists_prop` has no explicit universe argument; @exists_prop works.

## Next conjecture — NOT FORMALIZED
Within the compact product cube [-1,1]^ℕ, are all three log-2 moments nonsummable residually? Candidate proof: extend any finite bounded prefix with adaptive antipodal targets, guaranteeing all later absolute log-2-weighted terms≥1/2 and all history values bounded by1. Strict tail events |term|>1/4 should be open and dense in the cube; countable intersection gives signed nonsummability. Then bounded cofinal mesh values + local one-sided divergence laws rule out finite excess and deficit at log2. Requires generalizing the existing antipodal construction to preserve a chosen finite prefix; do not copy the builder. DO NOT infer nowhere summability at every real shift within the bounded cube. The unrestricted-history proof does not imply that.
