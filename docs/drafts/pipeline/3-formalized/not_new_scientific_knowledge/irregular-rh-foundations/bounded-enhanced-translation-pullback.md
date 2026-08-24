# Bounded enhanced translation pullback

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Standard bounded enhanced ind-sheaf operation.

## Target

Restrict enhanced translation pullback to bounded derived ind-sheaves and descend it to the bounded
generated enhanced Verdier quotient.

## Dependency-closed paper proof

Exact translation pullback preserves both canonical cohomological bounds, hence restricts to the
bounded derived category. After applying the fully faithful inclusion into the unbounded derived
category, the bounded projection-translation composite becomes the already-proved unbounded
composite. Cancelling the inclusion gives the bounded comparison. It maps projection-pulled
generators to projection-pulled generators, so the triangulated-envelope and Verdier-localization
arguments descend translation to the bounded quotient.

## Lean target

Bounded derived translation, inclusion and projection comparisons, negligible preservation, and
quotient descent.

## Log

- 2026-08-24 — unbounded translation action formalized; bounded paper proof closed; Lean
  formalization started
- 2026-08-24 — formalized bounded derived translation, projection comparison, negligible
  preservation, and quotient descent in `StokesBoundedEnhancedTranslationPullback.lean`; direct
  Lean check and targeted module build pass; all new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`
