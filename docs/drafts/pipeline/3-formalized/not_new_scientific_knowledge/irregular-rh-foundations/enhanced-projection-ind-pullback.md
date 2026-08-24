# Enhanced-projection pullback on ind-sheaves

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Functorial ind-sheaf infrastructure.

## Claim

For every topological space `X`, compact-support sheaf pullback along the proper projection
`X × EReal → X` induces a covariant functor
`IndSheaf(X) → IndSheaf(X × EReal)`. On compactly supported sheaves embedded as representable
ind-objects, this functor agrees canonically with ordinary proper pullback.

## Paper proof

Transport proper pullback across the chosen equivalences between compactly supported sheaves and
their small models. Apply covariant ind-extension to that small functor. The generic Yoneda
comparison for ind-extension is an isomorphism. Whiskering it with the small-model equivalences,
then cancelling equivalence functor followed by inverse, yields the comparison with the canonical
compact-sheaf embeddings.

## Lean artifact

`formal/GaloisForLFunctions/HTGeometry/StokesEnhancedIndProjectionPullback.lean` defines:

- `smallEnhancedProjectionPullback`;
- `enhancedIndProjectionPullback`;
- `compactToSmallCompSmallEnhancedProjectionPullbackIso`;
- `enhancedIndProjectionPullback_compactSheafIso`.

Direct Lean elaboration and targeted build
`lake build GaloisForLFunctions.HTGeometry.StokesEnhancedIndProjectionPullback` pass. Axiom audit of
all four declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Dependency audit

- `StokesERealEnhancedProjection.enhancedProjectionPullback`.
- `StokesIndFunctorExtension.Ind.map` and `Ind.mapYonedaIso`.
- `StokesCompactSheafToInd.compactSheafToIndSheaf`.
- No derived, enhanced-quotient, Stokes, arithmetic, or RH assumption.

## Hostile audit

- This is an ind-sheaf functor on compact ambient spaces, not yet a functor on bordered spaces.
- Agreement on representables does not by itself prove exactness or preservation of
  quasi-isomorphisms.
- Small-model transport is choice-dependent but unique up to canonical categorical isomorphism.

## Next step

Establish finite-limit and finite-colimit preservation needed for exactness and derived descent.
