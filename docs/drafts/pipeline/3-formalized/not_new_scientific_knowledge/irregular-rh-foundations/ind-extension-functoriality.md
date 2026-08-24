# Functoriality of covariant ind-extension

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Generic categorical infrastructure for ind-sheaf operations.

## Target

Prove that the presheaf-left-Kan-extension model of `Ind.map` respects natural isomorphisms,
identity functors, and composition.

## Dependency-closed paper proof

Naturally isomorphic functors `F,G : C ⥤ D` induce naturally isomorphic precomposition functors on
presheaves. Their left Kan extensions are therefore isomorphic by uniqueness of left adjoints.
Restricting these Kan extensions to ind-objects and cancelling the fully faithful presheaf
inclusion gives `Ind.map F ≅ Ind.map G`.

Precomposition along an identity functor is isomorphic to the identity, so uniqueness of left
adjoints identifies its Kan extension with the identity; cancellation yields
`Ind.map (𝟭 C) ≅ 𝟭 (Ind C)`. For composable `F` and `G`, precomposition along `(F ⋙ G)ᵒᵖ` is
canonically isomorphic to successive precomposition along `Gᵒᵖ` and `Fᵒᵖ`. Composition of the two
Kan-extension adjunctions and uniqueness of left adjoints gives
`Lan(Fᵒᵖ) ⋙ Lan(Gᵒᵖ) ≅ Lan((F ⋙ G)ᵒᵖ)`, hence
`Ind.map F ⋙ Ind.map G ≅ Ind.map (F ⋙ G)` after restriction and cancellation.

## Lean target

Precomposition, Kan-extension, and ind-extension comparison isomorphisms for natural isomorphism,
identity, and composition.

## Log

- 2026-08-24 — paper proof closed; Lean formalization started
- 2026-08-24 — formalized natural-isomorphism, identity, and composition laws in
  `StokesIndFunctoriality.lean`; direct Lean check and targeted module build pass; all new
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`
