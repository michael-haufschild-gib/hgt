# Derived exact sheafification descent

- **ID:** IRRH-DERIVED-SHEAFIFICATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Stacks Project, Tags [03CX](https://stacks.math.columbia.edu/tag/03CX) and [04VB](https://stacks.math.columbia.edu/tag/04VB); internal exact-sheafification theorem
- **Statement:** Degreewise exact sheafification of nonnegative integer-module presheaf complexes descends through quasi-isomorphism localization to a functor from the localized presheaf-complex category to the localized sheaf-complex category.

## Goal
Construct the derived sheafification bridge needed to transport chain-level presheaf models into the sheaf-side category. Standard infrastructure; no new scientific claim.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean definitions and theorems in `StokesDerivedExactSheafification.lean`, targeted build green, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Let `P` be the category of nonnegative complexes of integer-module presheaves on `Y`, `S` the corresponding sheaf-complex category, and `Wₚ`, `Wₛ` their quasi-isomorphisms. Let `a : P ⟶ S` be degreewise sheafification and let `Qₚ`, `Qₛ` be the localization functors.

Exact sheafification preserves homology, so `a(f) ∈ Wₛ` for every `f ∈ Wₚ`. Therefore `Qₛ(a(f))` is an isomorphism. Thus `a ⋙ Qₛ` inverts `Wₚ`; localization universality yields

`La : P[Wₚ⁻¹] ⟶ S[Wₛ⁻¹]`

and a canonical natural isomorphism `Qₚ ⋙ La ≅ a ⋙ Qₛ`.

**[PROVED HERE]** Exactness and quasi-isomorphism preservation are formalized; descent is the universal property of localization. No added hypothesis beyond chosen localization categories.

## Lean realization
- Module: `formal/GaloisForLFunctions/HTGeometry/StokesDerivedExactSheafification.lean`
- Chain-level functor: `sheafificationFunctor`
- Quasi-isomorphism preservation: `sheafificationFunctor_map_quasiIso`
- Localization inversion: `sheafificationThenQ_inverts_quasiIso`
- Descended functor: `derivedSheafification`
- Canonical factorization: `derivedSheafificationFactors`
- Verification: direct `lake env lean`, targeted module build, and `#print axioms` for all new definitions/theorems passed. Dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Scope boundary
This is integer-module sheafification on universe-zero topological spaces. It does not yet supply sheaf-level derived tensor compatibility, ringed-site generality, enhanced sheaves, or six operations.

## Log
- 2026-08-24 — paper proof completed; exact sheafification and localization sources audited
- 2026-08-24 — formalized descent; direct check, targeted build, and new-declaration axiom audit passed
