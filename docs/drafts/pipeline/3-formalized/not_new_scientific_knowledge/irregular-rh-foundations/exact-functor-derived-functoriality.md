# Functoriality of exact functors on derived categories

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Generic derived-category infrastructure.

## Target

Prove that exact-functor descent to unbounded derived categories respects natural isomorphisms and
composition.

## Dependency-closed paper proof

A natural isomorphism of exact additive functors prolongs degreewise to an isomorphism of cochain
complex functors. The localization universal property uniquely lifts it to the derived categories.

For composable exact additive functors, the composite of their derived functors is induced by the
successive degreewise complex functors. Degreewise prolongation identifies those with prolongation
of the composite. Lifting this comparison through the source quasi-isomorphism localization gives
the derived composition isomorphism.

## Lean target

Generic `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso` declarations.

## Log

- 2026-08-24 — corpus and mathlib searches found no existing derived composition comparison; paper
  proof closed; Lean formalization started
- 2026-08-24 — formalized natural-isomorphism and composition descent in
  `StokesExactFunctorDerivedFunctoriality.lean`; direct Lean check and targeted module build pass;
  both declarations use only `propext`, `Classical.choice`, and `Quot.sound`
