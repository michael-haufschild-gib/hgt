# Composition of proper compact-support pullback

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Generic categorical infrastructure for enhanced ind-sheaf
operations.

## Target

Prove ordinary sheaf inverse image and its compact-support restriction compose contravariantly.

## Dependency-closed paper proof

Sheaf inverse image is left adjoint to direct image. Successive inverse images are therefore left
adjoint to successive direct images, while direct image along a composite is definitionally the
successive direct image. Uniqueness of left adjoints gives the sheaf-level comparison.

For proper maps, each inverse image preserves compact support. Whisker the two compact-support
comparison isomorphisms with the fully faithful inclusion into all sheaves, insert the sheaf-level
composition comparison, and cancel that inclusion. This yields the compact-support comparison.

## Lean target

Canonical identity and composition comparisons for sheaf pullback and compact-support proper
pullback.

## Log

- 2026-08-24 — corpus search found no composition law; paper proof closed; Lean formalization started
- 2026-08-24 — formalized sheaf and compact-support composition comparisons in
  `StokesProperPullbackComposition.lean`; direct Lean check and targeted module build pass; both
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`
- 2026-08-24 — added identity-pullback comparisons needed for translation-action coherence; direct
  Lean check and targeted build pass; new declarations use standard axioms only
