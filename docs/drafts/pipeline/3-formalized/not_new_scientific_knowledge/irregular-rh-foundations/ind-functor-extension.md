# Functorial extension to ind-categories

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Standard universal-property infrastructure for ind-categories.

## Claim

Let `C` and `D` be locally small categories in the same universes and assume `D` has finite
colimits. Every functor `F : C → D` has a canonical chosen extension
`Ind(F) : Ind(C) → Ind(D)`, defined as the pointwise left Kan extension of
`F ; y_D` along `y_C`. Its comparison map on representables
`F ; y_D → y_C ; Ind(F)` is an isomorphism.

## Paper proof

Every ind-object `X` is a filtered colimit of representables and the comma category `(y_C / X)`
is filtered and finally small. Since `D` has finite colimits, `Ind(D)` has all small colimits.
Therefore the diagram `(y_C / X) → C → D → Ind(D)` has a colimit for every `X`, giving the
pointwise left Kan extension. The Yoneda embedding `y_C` is full and faithful. At `y_C(c)`, the
identity arrow is terminal in `(y_C / y_C(c))`; hence the Kan-extension unit at `c` is an
isomorphism.

## Lean artifact

`formal/GaloisForLFunctions/HTGeometry/StokesIndFunctorExtension.lean` defines:

- `CategoryTheory.Ind.yonedaHasPointwiseLeftKanExtension`;
- `CategoryTheory.Ind.map`;
- `CategoryTheory.Ind.mapYonedaHom` and its isomorphism instances;
- `CategoryTheory.Ind.mapYonedaIso`.

Direct Lean elaboration and targeted build
`lake build GaloisForLFunctions.HTGeometry.StokesIndFunctorExtension` pass. Axiom audit of every new
declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Dependency audit

- Mathlib ind-category presentation, filtered-colimit, finally-small, and pointwise Kan-extension
  APIs.
- Finite colimits in `D`, used only to obtain all small colimits in `Ind(D)`.
- No sheaf-specific, analytic, arithmetic, or RH input.

## Hostile audit

- This is the covariant ind-extension, not restriction of presheaves along `Fᵒᵖ`; those have
  opposite variance.
- Chosen Kan extensions are canonical only up to unique isomorphism, which is the correct categorical
  notion.
- No claim is made yet that `Ind(F)` preserves finite limits, finite colimits, filtered colimits, or
  quasi-isomorphisms. Those require separate proofs or hypotheses.

## Next step

Instantiate the construction for proper enhanced-projection pullback, then establish preservation
properties needed for derived descent.
