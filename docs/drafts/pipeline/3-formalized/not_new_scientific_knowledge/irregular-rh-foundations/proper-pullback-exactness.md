# Exactness of proper pullback on compact-support models

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Exact-functor infrastructure for ind-sheaf derived descent.

## Claim

For a proper map `f : X → Y`, compact-support sheaf pullback preserves finite limits and finite
colimits. The enhanced projection pullback and its transport between universe-small compact-support
models preserve finite limits and finite colimits as well.

## Paper proof

Inverse image of integer-module sheaves preserves finite limits and, as a left adjoint, all
colimits. Compact support is a Serre property: it is closed under kernels and cokernels. Therefore
the full compact-support inclusion preserves kernels and cokernels; between abelian categories this
implies preservation of all finite limits and finite colimits. The composite of restricted
pullback with inclusion is canonically isomorphic to ordinary pullback after source inclusion, so
the restricted functor preserves finite limits and colimits because target inclusion reflects
them. Finally, equivalence functors preserve all limits and colimits, so transport to small models
retains both properties.

## Lean artifact

`formal/GaloisForLFunctions/HTGeometry/StokesProperPullbackExact.lean` defines finite-limit and
finite-colimit preservation instances for compact-support inclusion, generic proper pullback,
enhanced projection pullback, and its small-model transport.

Direct Lean elaboration and targeted build
`lake build GaloisForLFunctions.HTGeometry.StokesProperPullbackExact` pass. Axiom audit of every new
instance reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Dependency audit

- `StokesCompactIndSheaf` Serre closure and abelian structures.
- `StokesProperPullbackCompactSupport.properPullbackCompιIso`.
- `StokesDerivedEpigraphDirectImage.intModuleSheafPullback_preservesFiniteLimits`.
- Mathlib left-adjoint preservation of colimits and preadditive kernel/cokernel criteria.
- No ind-extension exactness, derived, Stokes, arithmetic, or RH assumption.

## Hostile audit

- Properness is needed only to restrict pullback to compact-support objects; ordinary sheaf
  pullback exactness itself does not use properness.
- This proves exactness before ind-extension. Exactness of the chosen `Ind.map` remains a distinct
  theorem.
- Preservation is categorical and does not identify supports more sharply than containment in a
  compact preimage.

## Next step

Lift exactness across the ind-extension.
