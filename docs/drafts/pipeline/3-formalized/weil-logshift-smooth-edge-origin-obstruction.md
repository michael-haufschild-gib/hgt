# Smooth cutoff edges destroy universal signed moment control

- **ID:** weil-logshift-smooth-edge-origin-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean corpus and installed Lean definitions only.
- **Statement:** The origin inverse diagonal has a positive exponential lower envelope and is nonsummable. Every finite bounded history prefix admits one bounded extension with nonsummable signed moments at every real shift. These histories are dense; universal bounded-history signed moment summability fails at every shift, and every exact finite matrix budget is unbounded.

## Evidence inspected

- `TruncatedRiemannKernelWeilEnergy.lean:33`: `bulkCutoff L u = smoothTransition(L−u)*smoothTransition(L+u)`.
- `WeilFullConeRiemannKernelRigidity.lean:96`: truncated real kernel is the full real kernel times that cutoff.
- `WeilPositivityMajorantRigidity.lean:436`: truncated autocorrelation is the integral of the two truncated kernels.
- `WeilLogShiftCutoffReconstruction.lean`: `2L_n = log(n+1)−log 2`; diagonal separation `z_n = log n−log 2`; diagonal weight is `2K_Ln(z_n)/sqrt n`.
- `WeilLogShiftLocalDecayThreshold.lean:40`: every positive a below the local critical rate gives `P_y(n)≤C exp(−a n)` for n≥1.
- Same file:77: every b above the local critical rate gives `D exp(−b n)≤P_y(n)` eventually, D>0.
- `logKernelCriticalRate y = 2π exp(−|y|)`, giving rates π at log 2 and 2π at 0.
- Installed `Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`: `expNegInvGlue x = if x≤0 then0 else exp(−x⁻¹)`; smoothTransition is its quotient by the sum of the two complementary glue functions. Local `RiemannKernelFloquetBlockTests.lean:172` unfolds this definition to prove the complementary partition identity.

Direct corpus search `research 'smoothTransition expNegInvGlue' --any --mode lexical --no-refresh --json`: 21 hits, 11 eligible. No exponential edge estimate appeared. Exhaustive source matches found the glue's flatness in `NonperturbativeQuantumRecurrenceSeparationLaw.lean`, but no cutoff-product bound. Search and definition reads are complete; do not repeat them unnecessarily.

## Dependency-closed paper proof

At the recovery diagonal, the overlap width is `δ_n = log(n+1)−log n ≤ 1/n`. The two small cutoff arguments are `a=L_n−t` and `b=L_n+t−z_n`; their sum is δ_n. Where both are positive, each is at most 1/2 for n≥2. The transition formula gives

`smoothTransition(a) ≤ exp(2−1/a)` and similarly for b.

Using `1/a+1/b ≥ 4/(a+b)`, their product is at most `exp(4−4n)`. The other two cutoff factors are at most one. Outside the overlap, a factor vanishes. Existing integrability lemmas permit integration of this global pointwise estimate, yielding

`K_Ln(z_n) ≤ exp(4−4n) K(z_n)`.

Thus `sqrt(n)*w_nn ≤ 2 exp(4−4n) P_log2(n)`. Choose rates `0<a<π` and `2π<b<a+4`, possible because π<4. Existing upper/lower envelopes then give

`P_0(n)/(sqrt(n)*w_nn) ≥ c exp((a+4−b)n)` eventually, c>0.

This proves nonsummability of the origin diagonal. Antipodal diagonal domination gives one bounded history after every finite prefix whose origin signed moment is nonsummable; inward transfer excludes signed summability at every real shift on those same histories. The previous dense diagonal-obstruction set is therefore a dense set of simultaneous counterexamples. The exact finite-matrix equivalence then implies unbounded budgets at every shift. Stronger residual genericity and one-sided origin moments require separate arguments.

## Proof obligations discharged

1. Transition quotient and analytic APIs verified against installed Lean definitions.
2. Global cutoff-product estimate proved, including nonpositive edge arguments and integrability.
3. Logarithmic overlap bound and its exact relation to the recovery mesh proved.
4. Existing strict-rate envelopes combined with π<4, without numerical experiments.
5. Exact paper conclusions compiled and axiom-audited; scoped integration checks passed and global lint limitations recorded below.

## Formal results

`formal/GaloisForLFunctions/RHTower/WeilLogShiftSmoothEdgeBound.lean`: 158 lines, five public theorems.

- `smoothTransition_le_exp_edge`: explicit edge envelope for 0<x≤1/2.
- `bulkCutoff_product_le_exp_edge`: facing cutoff product ≤exp(4−4r) whenever r≥2 and overlap width ≤1/r.
- `truncatedRiemannAutocorr_le_exp_edge`: the same factor bounds truncated against full autocorrelation.
- `weilLogShiftRecoveryCutoff_margin_le`: native diagonal overlap ≤1/n.
- `weilLogShiftRecoveryWeight_smooth_edge_bound`: `sqrt(n)w_nn ≤ 2exp(4−4n)P_log2(n)` for n≥2.

`formal/GaloisForLFunctions/RHTower/WeilLogShiftOriginDiagonalDivergence.lean`: 156 lines, six public theorems.

- `exists_weilLogShiftOriginDiagonal_exponential_lower`: ∃c,γ>0, eventually `c exp(γ(k+2)) ≤ Response_0(k+2,k)`.
- `not_summable_weilLogShiftRecoveryDiagonal_origin`: origin diagonal nonsummable.
- `exists_weilLogShiftBoundedHistory_prefix_nowhere_summable`: one extension after every finite bounded prefix with nonsummable signed moments at every real shift.
- `dense_weilLogShiftBounded_nowhere_summable`: these simultaneous counterexamples form a dense subset of the unit cube.
- `not_weilLogShiftBoundedMomentSummable y`: universal signed moment receiver fails at every real shift y.
- `unbounded_weilLogShiftRecoveryMatrixBudget y C`: some finite matrix and finite sign vector exceeds every proposed bound C, for every real shift y.

## No-go closure and limits

Retired receiver: bounded samples on this exact recovery mesh might force signed moment summability at some interior shift, including the origin. The strongest positive survivor is the explicit overlap-resolution law and positive exponential lower envelope for the inverse diagonal, together with finite-prefix-preserving dense simultaneous counterexamples. Both paper proof and exact Lean statements are closed. The failed-route card `weil-logshift-bounded-recovery-moment-control` records the new survivor.

This does not say every bounded history diverges. It does not settle one-sided origin moments, residual genericity at the origin, boundedness on the entire positive real-cutoff axis, or RH. The arithmetic anchor remains a bounded history with zero deviations, but its norm has not been shown at most one.

## Verification

- Both new leaves compile/export using `lake --old env lean <leaf> -o <olean>`, exit 0 and no diagnostics, each on its first compilation. No subsequent source edits.
- All eleven public theorems have exactly `[propext, Classical.choice, Quot.sound]`; exhaustive scratch axiom audit exited 0 and complete name coverage was checked.
- Both umbrella imports unique; index refresh exited 0; all eleven API rows unique and in the correct modules.
- Scoped source/card whitespace, conflict-marker, and `git diff --check` checks passed.
- Global lint exited 1 on three unrelated unwired modules: `RHTower.CompletedErrorPrimitiveOneSidedLandau`, `HTGeometry.CauchyDifferenceTwoIntervalBound`, `HTGeometry.QKrawtchoukMaximalAtomUniqueness`. No diagnostics name the new leaves; those unrelated modules were not changed.
- No new analytic assumptions, proof gaps, axioms, numerical experiments, raised limits, web searches, papers, full builds, commits, or subagents.

## Next research

The residual upgrade is now formally proved in `WeilLogShiftBoundedOriginGenericity`, and the supremum-norm upgrade in `WeilLogShiftUniformBallGenericity` holds in every positive-radius closed ball around any bounded history. The origin envelope is now sharpened by `exists_weilLogShiftOriginDiagonal_exponential_lower_above`: every rate below 4-pi is exceeded by a proved exponential lower envelope. `WeilLogShiftExponentialPrecisionGenericity` consequently proves generic all-shift unbounded moments under errors bounded by epsilon exp(-sigma(k+2)), for 0<=sigma<4-pi. See `weil-logshift-exponential-precision.md`. The endpoint and larger rates, one-sided origin behavior, full real-cutoff control, and the next fixed-column conjecture remain separate questions.

## Working plan

1. [x] Verify analytic APIs; prove transition and cutoff-product suppression.
2. [x] Integrate the bound and specialize it to the exact recovery mesh.
3. [x] Combine strict-rate kernel envelopes to prove positive exponential growth of the origin diagonal and its nonsummability.
4. [x] Transfer the obstruction to bounded histories at every real shift, preserving finite prefixes; close no-go with the quantitative positive statement.
5. [x] Compile all touched leaves, audit every public declaration, wire imports, refresh index, run lint, update cards.
6. [x] Update memory and clean scratch.

## Log

- 2026-10-09 — previous turn classified verified progress. Promoted the inspected smooth-edge conjecture to active work. No repeated external research or searches; existing corpus audit and exact definitions supply the starting point.
- 2026-10-09 — dependency-closed paper argument confirmed, including the nonpositive-edge cases and integrability supplied by existing kernel lemmas. New analytic APIs checked in scratch. `WeilLogShiftSmoothEdgeBound.lean` drafted with explicit transition, product, integral, mesh-margin, and diagonal estimates; first compilation running. Next: strict-rate envelopes and origin consequences.
- 2026-10-09 — smooth-edge leaf compiled/exported with exit 0 and no diagnostics on first compilation. New origin-divergence leaf drafted: positive exponential diagonal growth, origin nonsummability, prefix-preserving dense simultaneous signed-moment counterexamples, failure of the universal receiver at every real shift, and unbounded finite matrix budgets. Compilation running. These consequences concern signed moments; one-sided origin moments and residual genericity require separate arguments.
- 2026-10-09 — origin-divergence leaf also compiled/exported with exit 0 and no diagnostics on first compilation. The signed universal interior question is now resolved negatively at every real shift. Eleven public declarations across the two new leaves prepared for exhaustive axiom audit; imports wired.
- 2026-10-09 — all eleven axiom audits passed with the exact standard set. Import and index checks passed. Global lint has only the three unrelated wiring errors listed above. Earlier cards and the failed-route survivor updated to distinguish this resolved signed receiver from still-open one-sided, residual, and full-cutoff questions.
- 2026-10-09 — dedicated result memory written and four predecessor memories corrected. All five owned scratch files removed and absence verified; all owned jobs terminal. This increment is closed; the research goal remains active, with residual signed nowhere summability as the next conjecture.
