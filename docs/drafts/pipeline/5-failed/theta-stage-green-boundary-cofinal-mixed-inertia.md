# Theta-stage Green boundary cofinal mixed inertia

- **ID:** `theta-stage-green-boundary-cofinal-mixed-inertia`
- **Stage:** 5-failed
- **Type:** NO-GO + POSITIVE SURVIVOR
- **Route:** GTA (`ORIENT` arithmetic-selector audit)
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Goal

Decide whether eventual positive- or negative-semidefiniteness of actual theta-stage complete Green
boundaries can supply upstream one-sided arithmetic selection for Schur quartic charge. Preserve
strongest cofinal inertia law if not.

## Gates

- [x] 0 → 1 in-progress: exact limit form, source vectors, constants, and falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed paper proof and novelty audit
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, lint, and axiom audit
- [x] 3 → 5 failed: one-sided semidefinite selector class retired; positive survivor preserved

## Parent corpus

- `[LEAN-PROVED]` Actual complete Green boundary operators converge in operator norm to
  `pinnedBoundaryCLM`.
- `[LEAN-PROVED]` Fixed source vectors `pinnedPositiveMode` and `pinnedNegativeMode` evaluate the
  limiting quadratic form to `1/6` and `-1/6`.
- `[LEAN-PROVED]` Zero Green charge on every nonzero actual-stage eigenmode is equivalent to real
  spectrum and hence to the GTA zero-charge stage flag.

## Frozen conjecture `[GTA-PQ4-P]`

For the two fixed source vectors `v₊=pinnedPositiveMode` and `v₋=pinnedNegativeMode`, eventually

`Re⟨B_k v₊,v₊⟩ > 1/12` and `Re⟨B_k v₋,v₋⟩ < -1/12`,

where `B_k=thetaSourceSignedStageGreenBoundary k`. Consequently every sufficiently late actual
boundary form is genuinely indefinite on the same two-dimensional source plane. In particular,
neither eventual positivity nor eventual negativity can be the missing arithmetic selector.

## Hostile attacks

- Operator-norm versus only strong convergence: corpus theorem is operator-norm convergence.
- Complex inner product: compare real parts, not `Complex` order.
- Moving witnesses: theorem must retain the same two source vectors for all late stages.
- Self-adjointness of finite-stage boundaries is unnecessary for the two strict quadratic signs.
- This no-go does not claim Green neutrality impossible; it excludes only one-sided semidefinite
  source laws as its producer.

## Dependency-closed proof plan

Continuous evaluation `T ↦ Re⟨Tv,v⟩` transports operator-norm convergence of `B_k` to scalar
convergence for each fixed `v`. The two limit values are exactly `±1/6`. The open neighborhoods
`(1/12,∞)` and `(-∞,-1/12)` therefore hold eventually. Intersect the two eventual sets to retain
the same stage tail. Positive semidefiniteness contradicts the negative witness; positivity of the
negated form contradicts the positive witness.

## Novelty audit

- Exact corpus search found limiting mixed inertia and actual-stage norm convergence separately,
  but no cofinal fixed-witness mixed-inertia theorem for actual theta stages.
- Exact arXiv searches through 2026-08-27 found recent finite-core Volterra/Weyl positivity work and
  older semi-local scaling-Hamiltonian work, but no actual theta-stage operator-norm limit theorem
  with fixed-witness cofinal mixed inertia. Priority remains unverified.

## Open core

`[OPEN CORE]` A surviving GTA selector must use genuinely indefinite, mode-sensitive incidence;
neither sign of a semidefinite Green boundary can hold cofinally.

## Positive survivor

`[LEAN-PROVED]` The same two source vectors witness quantitative mixed inertia for every
sufficiently late actual theta stage: positive quadratic value above `1/12` and negative value
below `-1/12`. Each witness has squared norm `13/12`, so every cofinal boundary stays at operator-
norm distance strictly greater than `1/13` from both the positive and negative operator cones.
This excludes approximate as well as exact semidefinite descent and gives a stable two-channel
orientation boundary for future indefinite selectors.

## Log

- 2026-08-27 — frozen from the actual-stage Green limit and explicit pinned mixed inertia.
- 2026-08-27 — dependency-closed proof completed; exact scratch Lean passed; literature audit found
  no matching theorem.
- 2026-08-27 — formalized in `HedenmalmThetaStageGreenBoundaryCofinalMixedInertia`; wired into
  `RHTower`, targeted build, formal lint, and axiom audit passed. Semidefinite selector class retired.
- 2026-08-27 — strengthened to exact witness norms and uniform `> 1/13` operator-norm separation
  from both semidefinite cones; targeted build, lint, and axiom audit re-passed.
