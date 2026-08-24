# Projective module-presheaf tensor flatness (2026-08-24)

Module `GaloisForLFunctions.HTGeometry.StokesProjectivePresheafTensorFlat` closes degree-zero projective-cell flatness.

Exact argument: for a module presheaf `P`, define its canonical free presentation with `PresheafOfModules.freeObjDesc (𝟙 _)` on `P.presheaf ⋙ forget _`. It is epic via `PresheafOfModules.epi_of_surjective`, preimage `ModuleCat.freeMk p`, and `ModuleCat.freeDesc_apply`. If `[CategoryTheory.Projective P]`, `Projective.factorThru (𝟙 P) presentation` supplies a section. Evaluating the split identity and applying `Module.Flat.of_retract` makes every `P.obj X` flat. Evaluation preservation plus joint reflection proves left tensor preserves finite limits; braiding gives right tensor; homology preservation gives degreewise quasi-isomorphism preservation.

Verification: direct Lean check passed; targeted module build passed `8664/8664` in 21s. Axiom audit of all 12 created declarations: `[propext, Classical.choice, Quot.sound]`. Umbrella import wired but umbrella build intentionally not run.

Boundary: this proves tensoring by one projective object concentrated in degree zero. Total tensor by a bounded complex of projectives/K-flat objects, closure under shifts/cones/coproducts/retracts of complexes/bounded totalizations, exact sheafification, enhanced tensor, and zero-independent arithmetic source remain open. RH remains unproved.

Card: `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/irregular-rh-foundations/projective-presheaf-tensor-flatness.md`.