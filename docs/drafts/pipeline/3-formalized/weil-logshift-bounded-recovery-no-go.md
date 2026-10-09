# Bounded recovery samples do not control local moments

- **ID:** weil-logshift-bounded-recovery-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean corpus, `WeilLogShiftRecoveryHomeomorphism`, `WeilLogShiftCutoffReconstruction`, `WeilLogShiftLocalExcessDomain`, `WeilLogShiftReflection`.
- **Statement:** There exists a coefficient sequence whose every visible recovery sample is ±1, while its signed, excess, and deficit potential moments at log 2 are all nonsummable.

## Goal
Separate exact coefficient recovery from analytic moment control. No RH claim, extra analytic premise, numerical evidence, external paper, or web source.

## Plan
1. Extract the existing triangular construction into an adaptive recovery API; retain the fixed-history homeomorphism as a specialization.
2. Formalize the diagonal kernel bound, adaptive antipodal construction, and cofinal recovery sampling.
3. Prove all three nonsummability conclusions, audit axioms, wire imports, refresh index, run lint, and record the exact positive survivor.

## Dependency-closed paper proof
[PROVED HERE] Start with the von Mangoldt coefficient sequence. At step n≥2, previous steps have changed only indices below n, so the current nth coefficient is still Λ(n). Let q be the current nth recovery sample. Set its target to +1 when q≤0, and −1 otherwise. Its distance from q is at least 1. The positive diagonal recovery weight w_nn permits one correction at n; triangular support preserves all earlier samples. Stabilization gives a coefficient sequence λ with every recovery sample in {−1,+1} and |λ(n)−Λ(n)|w_nn≥1.

The existing diagonal identity and truncated-to-full kernel comparison give
w_nn ≤ 2 P_log2(n)/sqrt(n). Hence |weilDeviation λ n|P_log2(n)≥1/2 for every n≥2. Terms of the signed moment therefore fail to tend to zero, so the signed series is not summable.

Recovery cutoffs L_n=(log(n+1)−log2)/2 tend to infinity. If the excess moment were summable, the existing local-excess divergence theorem would force the actual probe to tend to −∞, contradicting its ±1 values on this cofinal mesh. The dual local-deficit theorem similarly excludes a summable deficit moment.

## No-go closure
- **Exact killing mechanism:** uniformly bounded samples on an injective cofinal mesh coexist with nonvanishing weighted arithmetic terms and both divergent one-sided moments.
- **Strongest positive survivor:** adaptive triangular realization: any state-dependent target policy is realized exactly, with its input state equal to the final earlier coefficient prefix and an untouched baseline tail. Fixed policies recover the existing homeomorphism.
- **New insight:** injectivity and product-topology continuity of recovery do not imply moment control from bounded history values; one-sided moment hypotheses remain substantive even on the recovery mesh.
- **Status:** paper proof and exact Lean formalization closed using only local Lean results. No statement about boundedness at intervening real cutoffs.

## Original formal results

`formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryAdaptive.lean`:
- `weilLogShiftRecoveryPrefix`: final earlier coefficients with baseline tail.
- `weilLogShiftRecoveryAdaptive`: stabilized adaptive construction.
- `weilLogShiftRecoveryAdaptive_head`: invisible coordinates retain the baseline.
- `weilLogShiftRecoveryAdaptive_probe`: every policy is realized exactly on its final-prefix/baseline-tail state.
- `continuous_weilLogShiftRecoveryAdaptive_height`: continuous dependence for state-independent policies.
- The existing affine-probe and continuity lemmas moved here, retaining names and statements. `WeilLogShiftRecoveryHomeomorphism.lean` now specializes this builder instead of duplicating it; all existing public results remain available.

`formal/GaloisForLFunctions/RHTower/WeilLogShiftBoundedRecoveryNoGo.lean`:
- `tendsto_weilLogShiftRecoveryCutoff`: mesh cofinality.
- `weilLogShiftRecoveryWeight_diagonal_le`: exact diagonal/full-kernel comparison.
- `exists_antipodal_recovery_with_large_terms`: every sample has absolute value 1 and every absolute potential term is at least 1/2.
- `exists_bounded_recovery_with_divergent_excess_and_deficit`: all three local series are nonsummable despite bounded recovery samples.

## Original verification

- All three leaf compile/export checks exited 0, with no diagnostics on final checks.
- All 21 public declarations across these leaves have exactly `[propext, Classical.choice, Quot.sound]`; scratch axiom audit exited 0.
- Nine new public declarations; the original twelve remain available, including two moved to the adaptive leaf.
- Imports wired; index refreshed; every one of the 21 API rows checked for unique name and correct module.
- Scoped whitespace/conflict-marker checks and `git diff --check` passed.
- Global lint exited 1 only for two unrelated unwired modules: `RHTower.LeeYangSplitCountDifference` and `RHTower.PaperSuzukiCayleyReconstruction`. Neither was modified. This supersedes prior lint snapshots for this increment.
- One local binding was renamed because `prefix` is reserved Lean syntax. No proof gaps, new axioms, numerical experiments, increased heartbeat/recursion limits, external sources, umbrella builds, or commits.

## Gates
- [x] Well posed; source-pure corpus search completed.
- [x] Dependency-closed paper proof.
- [x] Exact Lean declarations compiled and axiom-audited.
- [x] Imports/index/lint checked; failure card and formalized positive survivor recorded.

## Log
- 2026-10-09 — adaptive antipodal proof extracted from the recovery homeomorphism and one-sided local moment divergence laws.
- 2026-10-09 — adaptive realization and the homeomorphism specialization compiled successfully; exact toolchain-name checks passed. Bounded-history theorem compiling; audit pending.
- 2026-10-09 — all four bounded-history theorems compiled; all 21 public declarations axiom-audited. Exact adaptive positive survivor formalized; no-go retired with both mathematical outputs preserved.

## Remaining frontier

Boundedness on the entire positive real cutoff axis remains unresolved. The proved obstruction controls only the recovery mesh. A next corpus-only audit should determine whether stronger real-cutoff regularity forces a one-sided moment condition or admits a different counterexample; do not assume either conclusion.

Verified follow-up: [recovery-domain density](weil-logshift-recovery-domain-density.md) proves that every finite recovery prefix admits arbitrary open or closed moment domains with finite total excess, and every realized signed/excess/deficit profile is dense in history space. This settles the finite-data topology question while leaving the full real-cutoff question above open.

Further verified follow-up: [bounded-cube genericity](weil-logshift-bounded-cube-genericity.md) makes failure of all three moments at |y|≥log 2 generic within [-1,1]^ℕ. This leaf now exposes finite-prefix antipodal realization and the bounded-mesh one-sided implication; the original counterexamples specialize them. Signed and either one-sided summability at log 2 are equivalent for every unit-bounded history. Updated compilation and 35-declaration axiom audit are recorded in the follow-up card.

Further verified positive statement: [diagonal obstruction](weil-logshift-diagonal-obstruction.md) factors the exact antipodal gain `w_nn|λ_n−Λ_n| = 1+|Q_n(prefix)|`. The original bound is now its specialization. The leaf has seven public theorems and 191 lines; all seven were recompiled and axiom-audited with the new diagonal-obstruction leaf. Every finite bounded prefix admits one extension dominating the entire family of weighted inverse diagonals, and universal moment summability forces diagonal summability. The follow-up records the latest fourteen-declaration audit and lint snapshot.
