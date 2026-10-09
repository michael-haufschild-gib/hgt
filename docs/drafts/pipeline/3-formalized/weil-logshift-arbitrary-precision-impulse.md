# Arbitrary precision envelopes and a single late history error

Status: formalised and audited. Corpus-only research, 2026-10-09. Global lint has 17 unrelated import-reachability errors, recorded below.

## Target

For every bounded center history, every strictly positive coordinatewise error envelope, and every prescribed finite prefix, a bounded history exists which strictly increases exactly one later coordinate, preserves every other observation, obeys the envelope, and has unbounded absolute reconstructed moment terms in every tail at every real shift. Signed moment summability fails everywhere.

Stronger structural result: along every sufficiently late impulse line center+t*unit(k), at most one real amplitude has eventually bounded moment terms at even one real shift. At most one amplitude admits a summable moment series at any shift.

## Existing local inputs

- `WeilLogShiftLateColumnRunaway.lean`: sufficiently late fixed impulse columns have absolute moment responses tending to infinity at every real shift. Final leaf compilation, axiom audit and index verification passed; exact global lint limitation is recorded on the formalised late-column card.
- `weilLogShiftRecoveryMoment_sub_eq`: subtracting two histories removes the affine moment baseline.
- `weilLogShiftUniformNowhereBounded_of_origin`: origin tail-unboundedness transfers to every real shift.
- `weilLogShiftUniform_nowhere_summable_of_nowhere_bounded`: signed summability fails at every shift.
- `weilLogShiftRecoveryUnitHistory_apply`: exact single-coordinate support.

## Paper proof

Fix an impulse index k beyond the unconditional late-column threshold. Suppose two distinct amplitudes t,u both fail the property of unbounded moment terms in every tail at every shift. Contraposition of origin-to-all-shifts transfer gives an eventual finite bound on each origin moment sequence. Their difference is eventually bounded by the sum of those bounds. The exact affine difference identity makes its norm equal to |t-u| times the fixed origin response column, which tends to infinity. Contradiction. Hence at most one amplitude is exceptional.

Given positive envelope epsilon and finite prefix length M, choose k beyond both M and the late-column threshold. The amplitudes epsilon(k) and epsilon(k)/2 are distinct, nonzero, and both within the allowed coordinate error. At least one gives nowhere tail-unboundedness. Its history is bounded because a finite-coordinate perturbation of a bounded history is bounded. All other coordinates are unchanged, so the entire prefix and every other envelope constraint hold exactly. No envelope decay restriction is used.

## Scope and limits

- This proves existence under arbitrary positive precision envelopes, including errors supported at exactly one arbitrarily late coordinate.
- The at-most-one-exception conclusion concerns each affine impulse line. It does not assert every nonzero perturbation of every center diverges.
- Genericity in a full weighted parameter space and almost-sure statements require separate proofs.
- Coordinate-zero response remains open; the result needs only the proved late-column threshold.

## Plan

1. [x] Search local corpus for this exact affine-line/precision conclusion before new Lean.
2. [x] Formalise the at-most-one exceptional amplitude statement.
3. [x] Derive arbitrary-envelope, exact-prefix, single-coordinate witnesses.
4. [x] Compile each leaf, audit all public axioms, wire imports, refresh index and run lint.
5. [x] Record further conjectures; clean owned scratch.

## Further exposed question

The same half-tail estimate should force strict alternating signs in every sufficiently late impulse column, and the one-step gain should yield a quadratic-exponent lower bound. These are new strengthening targets, not currently claimed as formalised.

## Current log

- 2026-10-09 — Fresh direct lexical corpus search (arbitrary precision, impulse, exceptional amplitude, finite prefix) returned the existing exponential-precision, prefix and fixed-column APIs, with no affine-line exceptional-amplitude or arbitrary-envelope witness theorem. Exhaustive rg over WeilLogShift source files found no duplicate conclusion. Native difference, origin transfer and late-column theorem statements were checked against current source.
- 2026-10-09 — Stronger envelope formulation needs only a nonnegative envelope and one positive allowance at a chosen sufficiently late coordinate. All other envelope values may be zero. Its proof is the same two-amplitude argument and exact single-coordinate support. The originally requested strictly positive envelope is a specialization, with k beyond any prescribed prefix. This generalization adds no analytic premise.
- Planned leaves: `WeilLogShiftImpulseLineObstruction.lean` for exact impulse identities, divergent separation and exceptional-amplitude rigidity; `WeilLogShiftArbitraryPrecisionImpulse.lean` for two-amplitude witnesses and arbitrary-envelope/prefix conclusions. No old public API needs changing.
- 2026-10-09 — Impulse-line leaf passed first compilation: exact history/moment differences, equivalence between failure of the global unboundedness property and eventual origin boundedness, divergent separation, at most one amplitude with any eventually bounded moment, and at most one amplitude with a summable moment series at any shift. Replaced deprecated `push_neg` with compiler-recommended `push Not` before final audit. Arbitrary-envelope leaf is written and next to compile; its witness is strictly upward at the chosen coordinate.
- 2026-10-09 — Final impulse-line compilation passed without diagnostics. First arbitrary-envelope compilation found one conditional simplification mismatch (`if True then t else 0`) in the selected coordinate's error bound; replaced the overly restricted simp call with direct rewrites. No mathematical argument changed. Final check running.
- 2026-10-09 — Arbitrary-envelope leaf now compiles/exports without diagnostics. Stronger final witness increases exactly one sufficiently late observation, preserves every other observation and any requested finite prefix, obeys the entire precision envelope, and has unbounded moment terms in every tail at every real shift. Signed summability fails everywhere. Both new leaves are wired; all 11 public theorem axiom audits are next. No old Lean API changed.

## Verified APIs

`WeilLogShiftImpulseLineObstruction.lean` defines `weilLogShiftRecoveryImpulseHistory center k t` and proves seven public theorems: pointwise evaluation, centered history difference, exact fixed-column moment difference, the eventual-origin-boundedness certificate, divergent separation of distinct amplitudes, at most one exceptional amplitude, and at most one amplitude with summability at any shift.

`WeilLogShiftArbitraryPrecisionImpulse.lean` proves four public theorems:

- `exists_weilLogShiftRecoveryImpulse_two_amplitude_alternative`
- `exists_weilLogShiftRecoveryImpulse_positive_amplitude`
- `exists_weilLogShiftRecoveryImpulse_within_envelope`
- `exists_weilLogShiftArbitraryPrecision_single_error`

The third theorem requires only a nonnegative envelope and one positive allowance at a selected sufficiently late coordinate. All other allowances may be zero. The fourth specialises to arbitrary positive envelopes and returns the explicit finite-prefix, strictly upward single-error, and nowhere-summability conclusions together.

## Final verification

- Both final leaves compiled/exported with `lake --old env lean <leaf> -o <object>`; exit0 without diagnostics.
- Exhaustive /tmp axiom audit for all 11 public theorems: exactly `[propext, Classical.choice, Quot.sound]` for every theorem; exit0 without diagnostics.
- Two unique umbrella imports; source/object freshness and unchanged final hashes checked. Scoped source-gap, raised-limit and whitespace checks passed. Source-gap scan excludes comments: the English word `admit` in a docstring is not a Lean declaration.
- Index refresh exit0 (13 changed modules globally, none removed). All 12 affected public API entries verified for exact kind, module, source path and line, without duplicates.
- Global lint exit1 only for the following 17 unrelated unreachable HTGeometry modules. No affected-file diagnostic; unrelated files were not changed.

```text
PaperGenericSL2Presentation
PaperRationalAdditiveActionBoundary
PaperStabilizedAdditiveAction
PaperStableCoordinate.ActionWeightDerivative
PaperStableCoordinate.CoactionAction
PaperStableCoordinate.DeterminantActionWeights
PaperStableCoordinate.DeterminantGradedObstruction
PaperStableCoordinate.DeterminantGradings
PaperStableCoordinate.DeterminantLiftWeights
PaperStableCoordinate.DeterminantWeights
PaperStableCoordinate.HomogeneousQuotientWeight
PaperStableCoordinate.LNDAction
PaperStableCoordinate.LNDExponential
PaperStableCoordinate.LNDExponentialLaw
PaperStableCoordinate.LaurentWeightObstruction
QKrawtchoukCompanionNormResolvent
QKrawtchoukCompanionOperator
```

The previous subcritical-exponential restriction is removed for existence. Genericity under arbitrary envelopes is a separate next theorem, with a dependency-closed paper proof in `docs/drafts/pipeline/1-in-progress/weil-logshift-arbitrary-precision-genericity.md`. Its topology is explicitly the bounded error-parameter ball, not an inferred topology on the image histories.

All owned command handles are terminal. Ten explicit `/tmp/hgt-weil-impulse-*` scratch/log/manifest files were removed; absence verified. Final source hashes, unique imports and card promotion were checked before cleanup. The indefinite corpus-research goal remains active.
