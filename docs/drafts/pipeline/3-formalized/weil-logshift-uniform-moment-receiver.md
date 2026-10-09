# Uniform moment control from pointwise bounded-history summability

- **ID:** weil-logshift-uniform-moment-receiver
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean corpus only: recovery homeomorphism, affine probes, bounded cube, corpus Banach–Steinhaus applications.
- **Target:** For every real shift y, summability for every unit-bounded recovery history is equivalent to one uniform bound on all finite absolute moment sums. Equivalently, the zero-history moment is summable and the finite signed centered moment functionals have uniformly bounded operator norms on bounded sequences.

## Why this advances the open question

Interior convergence remains unproved. The target replaces a pointwise universal analytic receiver with a quantitative operator-norm receiver and yields uniform stability whenever the receiver holds. No claim that either condition holds for an interior shift. Outer shifts already fail by the bounded-history counterexample.

## Dependency-closed paper proof

The finite affine probe formula and uniqueness of normalized recovery imply that the centered inverse h ↦ Inv(h)−Inv(0) is linear. Its coordinates are continuous in product topology. Therefore each centered weighted deviation coordinate is a continuous linear functional on the Banach space of bounded real sequences, using continuous coordinate evaluation.

Assume every unit-bounded history has a summable weighted deviation sequence. The zero history does too. Scale any bounded history into the unit cube and subtract the zero-history sequence. Linearity implies absolute summability of its centered terms. Every finite signed sum of these terms is therefore bounded pointwise by their absolute series. Banach–Steinhaus gives one bound on the norms of all finite signed functionals. For a history in the unit cube, choose each sign to match its centered term; the resulting sum is the finite sum of absolute centered terms. Adding the absolute zero-history moment gives a common bound for all absolute partial moments. Conversely, a common bound implies summability for each history by the existing nonnegative partial-sum criterion.

The same argument gives an exact operator formulation: zero-history summability plus a uniform norm bound for all finite signed centered panels. This condition suffices for each bounded history, with affine norm growth, and controls differences linearly in the history supremum norm.

## Plan and gates

1. [x] Corpus novelty search; verify exact installed Lean APIs in scratch.
2. [x] Formalize affine recovery identities and centered continuous linear coordinates.
3. [x] Prove pointwise/uniform/operator equivalences and difference control.
4. [x] Compile leaf, audit every public declaration, wire umbrella, refresh index, run lint.
5. [x] Update memory and clean owned scratch.

## Original formal results

`formal/GaloisForLFunctions/RHTower/WeilLogShiftUniformMomentReceiver.lean`:
269 lines, thirteen public declarations (five definitions, eight theorems).

- `weilLogShiftRecoveryInverse_affine`: exact arbitrary two-history affine combination, with the remaining weight on the zero-history inverse.
- `weilLogShiftRecoveryMoment`: signed weighted deviation at an arbitrary real shift.
- `weilLogShiftRecoveryMomentCLM`, `weilLogShiftRecoveryMomentCLM_apply`: centered moment coordinates as continuous linear functionals on bounded real histories.
- `weilLogShiftRecoveryMomentPanel`, `weilLogShiftRecoveryMomentPanel_apply`: finite signed sums of centered coordinates.
- `weilLogShiftBoundedHistoryBCF`, `norm_weilLogShiftBoundedHistoryBCF_le`: cube histories embedded with supremum norm at most one.
- `WeilLogShiftBoundedMomentSummable`: every unit-cube history has a summable signed moment at the chosen shift.
- `weilLogShiftRecoveryMomentPanel_bounded`: that pointwise condition forces uniform bounds on all finite signed panel operator norms.
- `weilLogShiftBoundedMomentSummable_iff_operator_bound`: exact equivalence with zero-history summability plus the panel norm bound.
- `weilLogShiftBoundedMomentSummable_iff_uniform_bound`: exact equivalence with one common bound on absolute partial moments, uniform over all cube histories and cutoffs.
- `weilLogShiftBoundedMomentSummable_lipschitz`: the same receiver forces a common Lipschitz bound on every partial sum of absolute moment differences between arbitrary bounded histories, using their supremum distance.

## Original verification

- Final leaf compile/export: `lake --old env lean GaloisForLFunctions/RHTower/WeilLogShiftUniformMomentReceiver.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilLogShiftUniformMomentReceiver.olean`, exit 0, no diagnostics, first compilation.
- All thirteen public declarations have exactly `[propext, Classical.choice, Quot.sound]`; scratch axiom audit exited 0 and complete name coverage was checked.
- Umbrella import unique; index refresh exited 0; all thirteen API rows unique and correct.
- Scoped whitespace, conflict-marker, and `git diff --check` checks passed.
- Global lint exited 1 on nine unrelated unwired modules: `RHTower.JensenTrivialZeroProducts`; `HTGeometry.BandKernelOperators`, `ConeKernelCrossedProduct`, `GibbsSizeBiasEntropy`, `HyperbolicSineScaleMonotonicity`, `PaperStableCoordinate.Stabilization`, `PaperStableCoordinate.StabilizationEmbedding`, `QKrawtchoukEdgeMoments`, and `RealGroupCStarFaithful`. No diagnostics name the new leaf. These modules were not changed.
- No new axioms, proof gaps, analytic assumptions, experiments, limit increases, web searches, external papers, full builds, commits, or subagents.

## Interpretation and next conjecture

This is an unconditional equivalence and an exact change of receiver language. It does not discharge the interior moment condition. The first proof retained the zero-history moment to account for the affine offset. The subsequent finite-matrix receiver discharges that premise using a bounded arithmetic history with zero deviations. The earlier assertion that the premise could not be omitted was too strong and is corrected here.

The finite-matrix card proves the exact finite-column norm formula and removes the baseline premise. The subsequent smooth-edge origin result proves that the resulting matrix bound fails at every real shift. Thus the universal signed interior receiver is refuted, including at the origin; the exact equivalences here remain valid.

## Follow-up change

The existing private centered partial-sum estimate is now public as `sum_norm_weilLogShiftRecoveryMomentCLM_le`, allowing the arithmetic-anchor proof to reuse it. All three previous callers use the same proof. The leaf now has fourteen public declarations and 270 lines; its recompilation/export passed. The follow-up card records the combined 32-declaration audit and latest lint snapshot.

## Log

- 2026-10-09 — previous turn only acknowledged corpus-only constraint: no research progress. Resumed quantitative inverse investigation. No web, papers, experiments, new analytic premises, or subagents.
- 2026-10-09 — lexical corpus search returned 1,114 hits, 669 eligible; inspected ranked declarations and relevant exhaustive source matches. No equivalent recovery operator receiver found. New mathlib APIs verified against installed toolchain in scratch; current global `sum_apply` and `smul_apply` replace deprecated CLM aliases.
- 2026-10-09 — complete new leaf compiled/exported with exit 0 and no diagnostics on its first compilation. Uniform finite moments, exact operator receiver, and Lipschitz difference control are formalized. Umbrella wired; axiom/index/lint checks pending.
- 2026-10-09 — all thirteen public axiom audits and index/import checks passed. Final lint capture confirmed exactly nine unrelated unwired modules, listed above. Prior generic-cube card now links this stronger receiver. Next task: finite column-response norm formula, then quantitative interior estimates.
- 2026-10-09 — cross-session memory written. All jobs terminal. Nine explicitly owned scratch paths (including three inherited inverse-control search files) removed and absence verified. Goal remains active.
