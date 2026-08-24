# Proper inverse image preserves compactly supported sheaves

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Foundational infrastructure for the standard ind-sheaf model used by
irregular Riemann--Hilbert theory.

## Claim

Let `f : X → Y` be a proper continuous map. For every sheaf `F` of integer modules on `Y` whose
stalks vanish outside a compact set, the inverse-image sheaf `f⁻¹F` has stalks vanishing outside a
compact set. Consequently sheaf inverse image restricts to a functor from compactly supported
integer-module sheaves on `Y` to compactly supported integer-module sheaves on `X`.

## Paper proof

Choose compact `K ⊆ Y` such that `F_y = 0` for every `y ∉ K`. Properness gives compactness of
`f⁻¹(K)`. For `x ∉ f⁻¹(K)`, one has `f(x) ∉ K`, hence `F_{f(x)} = 0`. The canonical stalk
isomorphism `(f⁻¹F)_x ≅ F_{f(x)}` then gives `(f⁻¹F)_x = 0`. Thus `f⁻¹F` is supported inside the
compact set `f⁻¹(K)`. Mapping morphisms by ordinary sheaf inverse image defines the claimed
restricted functor because compact support is an object property and the subcategory is full.

## Lean artifact

`formal/GaloisForLFunctions/HTGeometry/StokesProperPullbackCompactSupport.lean` defines:

- `sheafPullbackStalkIso`;
- `pullback_hasCompactSupport`;
- `properPullback`;
- `properPullbackCompιIso`.

Direct Lean elaboration and targeted build
`lake build GaloisForLFunctions.HTGeometry.StokesProperPullbackCompactSupport` pass. Axiom audit of
all four new declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Dependency audit

- `StokesCompactIndSheaf.HasCompactSupport`: stalkwise compact-support predicate.
- Mathlib sheaf inverse image and its stalk-pullback isomorphism.
- Mathlib `IsProperMap.isCompact_preimage`.
- No conjectural hypotheses, arithmetic inputs, choice of compactification, or RH-equivalent input.

## Hostile audit

- Continuity alone is insufficient: inverse images of compact sets need not be compact. Properness
  is essential in the proof.
- This proves inverse image only for compactly supported ordinary sheaves. It does not yet construct
  its ind-extension, derived functor, enhanced quotient, or any six-operation identity.
- Compact support is defined by stalk vanishing, so no unsupported identification with closed
  topological support is used.

## Sources

- Kashiwara--Schapira, *Ind-sheaves*, Astérisque 271 (2001): compactly supported sheaves and
  ind-sheaf foundations.
- Mathlib topology and sheaf libraries: proper-map compact-preimage theorem and pullback stalk
  comparison.

## Next step

Instantiate the proper projection `X × EReal → X`, then extend its compact-support pullback functor
to ind-objects and the corresponding derived category.
