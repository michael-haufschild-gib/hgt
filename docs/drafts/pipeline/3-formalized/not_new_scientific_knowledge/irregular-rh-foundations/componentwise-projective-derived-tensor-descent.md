# Componentwise-projective derived tensor descent

- **ID:** IRRH-DERIVED-KFLAT-TENSOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Stacks Project, Tags [06XY](https://stacks.math.columbia.edu/tag/06XY) and [04VB](https://stacks.math.columbia.edu/tag/04VB); internal K-flat card `nonnegative-projective-total-tensor-k-flat.md`
- **Statement:** For a nonnegative complex `P` of module presheaves whose terms are projective, total left tensor by `P` descends canonically through localization at quasi-isomorphisms to an endofunctor of the localized category.

## Goal
Construct the fixed-argument derived tensor functor needed before derived sheaf tensor and enhanced operations. This is standard infrastructure, not new scientific knowledge.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean definitions and theorems in `StokesProjectiveDerivedTensor.lean`, targeted `lake build` green, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Let `C = Ch≥0(PShMod(A))`, let `W` be its quasi-isomorphisms, and let `Q : C ⟶ C[W⁻¹]` be the chosen localization. Fix `P` with every `Pₙ` projective. Write `Tₚ = P ⊗ᵗᵒᵗ -`.

The K-flat theorem proves that `Tₚ(f)` is a quasi-isomorphism for every `f ∈ W`. Hence `Q(Tₚ(f))` is an isomorphism, because `Q` inverts every member of `W`. Therefore the composite `Tₚ ⋙ Q` inverts `W`. By the universal property of localization, it factors through a functor

`LTₚ : C[W⁻¹] ⟶ C[W⁻¹]`

with a natural isomorphism `Q ⋙ LTₚ ≅ Tₚ ⋙ Q`. This factorization is unique up to unique natural isomorphism. No resolution-existence claim is needed: `P` itself is already K-flat.

**[PROVED HERE]** All proof obligations reduce to the formalized K-flat theorem and localization universal property. No conjectural or analytic hypothesis enters.

## Lean realization
- Module: `formal/GaloisForLFunctions/HTGeometry/StokesProjectiveDerivedTensor.lean`
- Chain-level preservation: `tensorLeftFunctor_map_quasiIso`
- Localization inversion: `tensorLeftThenQ_inverts_quasiIso`
- Descended functor: `derivedTensorLeft`
- Canonical factorization: `derivedTensorLeftFactors`
- Verification: direct `lake env lean`, targeted module build, and `#print axioms` for all new definitions/theorems passed. Dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Scope boundary
This theorem constructs derived left tensor for a fixed componentwise-projective representative. It does not yet prove every derived object has such a resolution, bifunctoriality in the first variable, sheaf-level monoidality, or any irregular Riemann–Hilbert equivalence.

## Log
- 2026-08-24 — paper proof completed; internal corpus and external standard construction audited
- 2026-08-24 — formalized localization descent; direct check, targeted build, and new-declaration axiom audit passed
