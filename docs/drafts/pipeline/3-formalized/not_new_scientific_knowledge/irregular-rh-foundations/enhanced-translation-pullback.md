# Enhanced translation pullback and quotient action

## Status

Formalized in Lean 4.

## Classification

Not new scientific knowledge. Standard enhanced ind-sheaf operation.

## Target

Construct exact pullback by finite translations of the compactified enhanced variable, derive it,
prove it preserves projection-generated negligible objects, and descend it to the enhanced Verdier
quotient.

## Dependency-closed paper proof

Each finite enhanced translation is proper, so sheaf inverse image restricts to compactly
supported sheaves. Transport through the universe-small equivalence and covariantly extend to
ind-objects. Exactness of proper pullback passes through both transports, hence the ind-functor
derives to an exact triangulated endofunctor.

Translation followed by enhanced projection equals enhanced projection. Contravariant pullback
composition therefore identifies projection pullback followed by translation pullback with
projection pullback. The comparison transports through the small model, `Ind.map`, and derived
functoriality. Thus derived translation maps every projection-pulled generator to another such
generator. Since inverse image of a thick triangulated subcategory under a triangulated functor is
again thick triangulated, the universal property of the triangulated envelope extends preservation
to all generated-negligible objects. Verdier functoriality then descends translation to the
generated enhanced quotient.

## Lean target

Compact, small, ind, derived, and quotient translation functors; exactness instances; comparison
with enhanced projection pullback; preservation of `GeneratedNegligible`.

## Log

- 2026-08-24 — topology, proper pullback composition, Ind functoriality, and derived functoriality
  dependencies closed; Lean formalization started
- 2026-08-24 — formalized compact, small, ind, derived, and quotient translation pullback in
  `StokesEnhancedTranslationPullback.lean`; proved exactness and preservation of the
  projection-generated thick negligible subcategory; direct Lean check and targeted module build
  pass; all new declarations use only `propext`, `Classical.choice`, and `Quot.sound`
