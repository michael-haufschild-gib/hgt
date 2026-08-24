# Derived enhanced pullback on compact-support small models

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Derived-functor infrastructure below the ind-extension.

## Claim

Enhanced-projection pullback on universe-small compact-support sheaf models preserves homology.
Degreewise application to nonnegative chain complexes maps quasi-isomorphisms to
quasi-isomorphisms and therefore descends to their quasi-isomorphism localizations.

## Paper proof

The small-model pullback preserves finite limits and finite colimits between abelian categories.
It therefore preserves zero morphisms, binary biproducts, epimorphisms, and kernels, hence is
additive and preserves homology. A quasi-isomorphism is characterized degreewise by isomorphisms on
homology, so degreewise pullback preserves it. The composite with the target localization thus
inverts every source quasi-isomorphism and factors uniquely through the source localization.

## Lean artifact

`formal/GaloisForLFunctions/HTGeometry/StokesDerivedSmallEnhancedPullback.lean` defines the additive
and homology-preservation instances, nonnegative complex functor, quasi-isomorphism preservation,
derived localization functor, and localization factorization isomorphism.

Direct Lean elaboration and targeted build
`lake build GaloisForLFunctions.HTGeometry.StokesDerivedSmallEnhancedPullback` pass. Axiom audit of
every new declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Dependency audit

- `StokesProperPullbackExact` finite-limit and finite-colimit preservation.
- Mathlib preservation-of-homology and homological-complex quasi-isomorphism APIs.
- Mathlib categorical localization universal property.
- No exactness claim for `Ind.map`, bordered-space quotient, Stokes, arithmetic, or RH assumption.

## Hostile audit

- Source and target are derived categories of universe-small compact-support sheaf models, not
  derived ind-sheaf categories.
- Complexes use `ComplexShape.down Nat`; unbounded derived categories are not claimed.
- Localization produces a functor canonical up to the standard localization isomorphism; it does
  not construct resolutions.

## Next step

Prove exactness of ind-extension or build a compatible derived ind-extension by a separate
argument.
