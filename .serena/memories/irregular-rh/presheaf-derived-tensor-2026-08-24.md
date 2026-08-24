# Presheaf-module projective resolutions and degreewise derived tensor (2026-08-24)

Module: `formal/GaloisForLFunctions/HTGeometry/StokesPresheafDerivedTensor.lean`

Built:
- Free Yoneda module presheaves are projective using `PresheafOfModules.freeYonedaEquiv`, pointwise epi detection, and module epi-surjectivity.
- `PresheafOfModules R` has enough projectives via `freeYonedaCoproduct` and `fromFreeYonedaCoproduct`.
- Projective resolutions follow for the abelian presheaf category.
- Tensoring on either side over a commutative-ring presheaf is additive: tensor preserves all colimits, hence initial objects/binary coproducts, zero morphisms, and binary biproducts.
- Defined degreewise `leftDerivedTensorLeft` and `leftDerivedTensorRight` via mathlib `Functor.leftDerived n`.

Verification:
- Direct Lean check passed.
- Targeted module build passed (8661/8661; no umbrella build).
- Created declarations only axiom-audited: `[propext, Classical.choice, Quot.sound]`.
- Scratch files removed.
- Wired into `formal/GaloisForLFunctions/HTGeometry.lean`.

Boundary:
- Standard `[BRIDGE]`, no novelty claim.
- Does not assert enough projectives for sheaves.
- Does not construct K-flat sheaf resolutions, a derived-category tensor bifunctor, or full enhanced `Rμ_!!`.
- Next dependency: honest sheafification/K-flat comparison.
- RH open core remains zero-independent arithmetic source/derived completion; no unconditional RH proof.
