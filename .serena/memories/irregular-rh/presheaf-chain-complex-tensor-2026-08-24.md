# Presheaf module chain-complex tensor (2026-08-24)

- Added `formal/GaloisForLFunctions/HTGeometry/StokesPresheafComplexTensor.lean`.
- For small `C` and `A : Cᵒᵖ ⥤ CommRingCat`, proved additivity of curried tensor on `PresheafOfModules (A ⋙ forget₂ ...)`.
- Instantiated mathlib total tensor monoidal structure on nonnegative chain complexes; exposed tensor functor, unit, associator, unitors.
- Direct check and targeted module build passed; no umbrella build.
- Nine declarations use only `[propext, Classical.choice, Quot.sound]`.
- Wired into `GaloisForLFunctions/HTGeometry.lean`.
- Card: `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/irregular-rh-foundations/presheaf-module-chain-complex-tensor.md`.
- Exact boundary: chain-level only. Mathlib corpus search found no K-flat machinery or general tensor/quasi-isomorphism preservation theorem. Next open theorem is bounded projective/K-flat quasi-isomorphism invariance, then sheafification descent.
- RH remains unproved.