# WP02 — Exposing-ray archimedean positivity

Status: open direct RH route. Mode: paper research, then Lean. Read [shared contract](/Users/michael/Documents/code/hgt/docs/reports/weil-work/README.md).

## Single objective

Prove the right-hand side of `RHTower.riemannHypothesis_iff_forall_weilDualBound_archimedean`:

```lean
∀ (N : ℕ) (A : ℝ), N ≤ ⌊Real.exp (2 * A)⌋₊ →
  RHTower.WeilDualBound A (RHTower.exposingWeightTrunc N)
    (RHTower.archimedeanExposingThreshold - RHTower.exposingTail N)
```

This is a stronger dual positivity task than ordinary zero-atom PBAP. The corpus already proves its equivalence to RH. The missing work is the inequality, not another equivalence.

## Starting evidence

- [Exact archimedean exposing-ray receiver](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPolarConeExposedDuality.lean:604). Read the underlying `WeilDualBound` definition and its imports before selecting test families.
- [Threshold identity](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilPolarConeExposedDuality.lean:585): the archimedean threshold equals the exposing value; its construction is already formalized.
- [Exposedness](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeExposedPoint.lean:523) and [nonnegative atom-pairing receiver](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeExposedPoint.lean:585): full positivity gives one direction of the bound; attainment at the desired endpoint is not supplied.
- [Prefix receiver](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeCompactness.lean:177): RH iff every finite Λ-prefix has a **full-positive extension**.
- [One-sided cone receivers](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeOneSidedCriterion.lean:410) are alternate formulations to compare, not additional independent assignments.

## First research milestone

For one cofinal family of cutoffs and levels, isolate an exact energy decomposition or certificate whose residual has a proved sign or a proved vanishing bound. Identify which estimate would extend that family to every `(N,A)` required by the receiver, and prove the reduction if valid. Do not assume cofinality alone is sufficient.

Finite-dimensional experiments may guide the certificate. Before claiming a theorem, control the full function space, all omitted coefficients, aperture dependence and approximation errors. Compare against [existing numerical pinning work](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/certified-producer-pinning.md) so this package contributes a new analytic estimate rather than more decimal agreement.

## Exclusions and traps

- Proving a functional exposes Λ does not prove Λ belongs to the cone or that its exposed value is attained.
- Compactness produces an extremizer only after nonemptiness and the relevant continuity are established; it does not identify the extremal value.
- A finite list of test inequalities is weaker than `WeilPositiveFull`. Matching Λ on finitely many coefficients in a relaxation does not satisfy the prefix receiver.
- Ordinary PBAP handles the zero atom-vector. Do not silently use it at a nonzero exposing ray.
- A bound with fixed positive loss does not reach the stated threshold. An asymptotically vanishing loss requires a proved passage to the exact receiver, including all quantifiers.
- Keep the exact polar/full test conventions of each imported theorem when transferring between formulations.

## Search entry points

```sh
scripts/formal_tools.py research 'WeilDualBound' --mode lexical --exact --per-module 0
scripts/formal_tools.py research 'exposing ray archimedean threshold tail bound' --mode deep --module Weil --budget-seconds 300
scripts/formal_tools.py research 'full positive prefix compactness' --module Weil
```

## Completion and handoff

`CLOSED` requires the universal inequality with no unproved analytic premise, and a compiled application of the existing RH receiver. A new finite-level inequality or a proved extension lemma with a remaining uniform estimate is `CONDITIONAL ADVANCE`. State the unpaid estimate exactly.

WP01 may reuse sign decompositions. WP03–WP06 may supply a route to endpoint attainment, but WP02 can proceed without them. Do not create duplicate general detector theorems here.

Owned result directory: `/Users/michael/Documents/code/hgt/docs/reports/weil-work/results/02-exposing-ray/`.

Owned initial card: `/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/weil-work-02-exposing-ray.md`.

Reserved new Lean scope: `/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilWorkExposingRay*.lean`. Existing modules are read-only. Output `RESULT.md`, `PROOF.md`, `EVIDENCE.md`.
