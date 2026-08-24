# Hausdorff bordered-space foundation (2026-08-24)

- Module: `formal/GaloisForLFunctions/HTGeometry/StokesBorderedSpace.lean`, imported by `HTGeometry.lean`.
- Defines `TopologicalBorderedSpace`, open-subset constructor, ambient graph/closure/projection, and exact D'Agnolo--Kashiwara proper closed-graph predicate `IsBorderedMorphism`.
- Defines strict ambiently extending morphisms and proves identity/composition laws plus every strict morphism into a Hausdorff ambient target is graph-proper.
- New proper-map infrastructure: closed subtype inclusion, pairing proper+continuous into Hausdorff target, codomain restriction, continuous graph homeomorphism, fiber products, proper base change, and descent through surjective proper maps.
- `isBorderedMorphism_comp` proves general graph-proper composition using closed fiber product and proper image relation.
- `HausdorffBorderedSpace` with `BorderedHom` has a verified `Category` instance.
- Direct `lake env lean` and targeted `lake build GaloisForLFunctions.HTGeometry.StokesBorderedSpace` pass. Axiom audit for every new theorem reports only `propext`, `Classical.choice`, `Quot.sound`.
- Card promoted to Stage 2 at `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/irregular-rh-foundations/irregular-rh-bordered-space-foundation.md`; Stage 3 blocked by unrelated existing repo lint failures.
- Next layer: constant coefficient sheaf on locally closed exponential support, open extension-by-zero, proper-support direct image, external tensor/derived convolution. Corpus search found ordinary sheaf pushforward/pullback/skyscrapers but not these operations.
- No subanalytic site, enhanced ind-sheaf category, D-module correspondence, or RH proof yet.