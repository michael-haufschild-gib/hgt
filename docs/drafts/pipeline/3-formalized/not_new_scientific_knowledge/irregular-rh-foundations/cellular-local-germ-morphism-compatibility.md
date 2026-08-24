# Cellular local-germ morphism compatibility

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Necessary morphism-level descent law.

## Target

Identify compatibility forced on a simultaneous family of local germ morphisms by a global cyclic
boundary morphism.

## Dependency-closed paper proof

The arc labelled `nextWall v` is represented twice: as the left arc of the germ indexed by `v`
and the right arc of the germ indexed by `nextWall v`. Both components are restrictions of the
same global natural-transformation component, so they agree exactly.

## Lean target

Compatibility predicate and proof that every restricted global morphism satisfies it.

## Log

- 2026-08-24 — formalized in `StokesCellularGermCompatibility.lean`; direct Lean check and targeted
  module build pass; both declarations use only `propext`, `Classical.choice`, and `Quot.sound`

## Survivor

Compatibility is proved necessary. Sufficiency and Hom equivalence remain on the active descent
card; no fullness claim is made.
