# Presheaf-module projective resolutions and degreewise derived tensor

## Classification

- Stage: 3 — formalized
- Status: `[LEAN-PROVED]`; exact theorem surface verified
- Scientific status: `[BRIDGE]` / standard category-theoretic infrastructure
- Route: irregular microlocal Riemann--Hilbert foundations
- Novelty claim: none

## Exact claim

Let `C` be a small category and `R : Cᵒᵖ ⥤ RingCat` a presheaf of rings. Then
`PresheafOfModules R` has enough projective objects. If `A : Cᵒᵖ ⥤ CommRingCat`,
then tensoring on either side by a fixed `A`-module presheaf is additive, so each
such tensor functor has the degreewise left-derived functors supplied by projective
resolutions.

This claim does **not** construct a left-derived functor between bounded-above
derived categories, a K-flat replacement, a derived bifunctor on complexes, or a
derived tensor product in the sheaf category.

## Dependency and duplication audit

- `scripts/formal_tools.py research "free Yoneda projective presheaf enough projectives"`:
  no existing corpus theorem.
- `scripts/formal_tools.py research "coproduct projective objects enough projectives"`:
  no existing corpus theorem.
- `scripts/formal_tools.py research "left derived tensor presheaf sheafification"`:
  only the underived Stokes tensor and unrelated CDGA-derived constructions.
- Mathlib already provides the free-Yoneda hom/evaluation equivalence, the canonical
  epimorphism from a coproduct of free Yoneda module presheaves, projectivity of
  coproducts of projectives, the pointwise monoidal structure, colimit preservation
  by tensoring on either side, and degreewise `Functor.leftDerived`.
- Mathlib does not currently provide `leftDerivedFunctorMinus`; its left-derived API
  here is homology-degree-valued.

## Paper proof

Fix `X : C`. The free Yoneda module presheaf `P_X` represents evaluation at `X`:

`Hom(P_X, M) ≃ M(X)`.

Given an epimorphism `e : E ⟶ M` and `f : P_X ⟶ M`, pointwise epimorphism detection
for module presheaves makes `e_X : E(X) ⟶ M(X)` an epimorphism of modules, hence a
surjective map. Choose `y : E(X)` mapping to the section corresponding to `f`.
The inverse free-Yoneda equivalence sends `y` to a lift `P_X ⟶ E`; naturality of
the equivalence proves its composite with `e` is `f`. Thus every `P_X` is projective.

For any module presheaf `M`, mathlib's `M.freeYonedaCoproduct` is the coproduct of
one `P_X` for every section of `M`, and `M.fromFreeYonedaCoproduct` is epic. Arbitrary
coproducts of projective objects are projective, so this is a projective presentation
of `M`. Therefore `PresheafOfModules R` has enough projectives and, being abelian,
has projective resolutions.

For a presheaf of commutative rings, tensoring by a fixed module presheaf preserves
all colimits. It therefore preserves the initial object and binary coproducts. In
the preadditive module-presheaf category this yields preservation of zero morphisms
and binary biproducts, hence additivity. Applying mathlib's projective-resolution
construction produces `leftDerived n` for every `n : ℕ`, on either tensor side.

## Hostile review

- General sheaf categories need not have enough projectives; no sheaf-category
  instance is asserted.
- Surjectivity is used only after converting the presheaf epimorphism to a component
  epimorphism.
- Infinite coproduct projectivity is required and available; finite sums would not
  cover arbitrary section sets.
- Tensor additivity is derived from actual colimit preservation, not assumed.
- Degreewise derived functors are weaker than a derived-category tensor bifunctor.
  Calling this `⊗ᴸ` on enhanced sheaves would overstate the result.

## Lean certificate plan

1. Prove each free Yoneda module presheaf projective using `freeYonedaEquiv`.
2. Build `EnoughProjectives` from `freeYonedaCoproduct` and its canonical epi.
3. Derive additive instances for left and right tensor functors.
4. Define both families of degreewise left-derived tensor functors.
5. Check only axioms of declarations created here; run direct file check and targeted
   module build.

## RH relevance and boundary

This supplies honest projective-resolution input below the irregular-RH tensor step.
It does not yet identify the result with tensor in the sheaf/enhanced derived category,
and it does not provide the missing arithmetic source theorem needed for RH.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesPresheafDerivedTensor`
- Direct check: `lake env lean GaloisForLFunctions/HTGeometry/StokesPresheafDerivedTensor.lean`
- Targeted build: `lake build GaloisForLFunctions.HTGeometry.StokesPresheafDerivedTensor`
- Result: both passed on 2026-08-24.
- Created declarations: free-Yoneda projectivity, enough projectives, projective
  resolutions, left/right tensor additivity, and both degreewise left-derived tensor
  families.
- Batched axiom audit of those declarations only: `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration introduced.
- Authoritative repository lint passed on 2026-08-27.
