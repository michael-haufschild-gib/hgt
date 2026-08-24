# Abstract enhanced Verdier quotient

- **ID:** IRRH-ABSTRACT-ENHANCED-QUOTIENT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** D’Agnolo–Kashiwara enhanced ind-sheaf quotient construction; Verdier localization formalism
- **Statement:** The essential image of a full triangulated functor `F : C ⟶ D` defines a triangulated negligible subcategory; localizing `D` at morphisms whose cones lie in that image gives a triangulated quotient that kills every object in the image and has the expected localization universal property.

## Goal
Supply category-theoretic quotient kernel used by enhanced ind-sheaves while making exact scope visible. This is standard infrastructure, not construction of ind-sheaves themselves.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean definitions and theorems in `StokesAbstractEnhancedVerdier.lean`, targeted build green, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Let `F : C ⟶ D` be full and triangulated between pretriangulated categories. Its essential image `N` contains zero, is shift-stable, and is closed under distinguished-triangle extensions: fullness lifts the third map needed to realize an extension inside `C`. Hence `N` is triangulated.

Let `W_N` consist of morphisms in `D` whose cone belongs to `N` up to isomorphism. Verdier’s calculus gives left and right fractions for `W_N`; the localization `Q : D ⟶ D[W_N⁻¹]` inherits a triangulated structure.

For `X ∈ N`, the zero map `X ⟶ 0` belongs to `W_N`, since it occurs as the second map of the contractible distinguished triangle on `X`. Thus `Q(0 : X ⟶ 0)` is an isomorphism. Because `Q` is additive, this is an invertible zero morphism, forcing `QX` to be a zero object.

Any functor `G : D ⟶ E` that inverts `W_N` factors through `Q` by localization universality, with canonical factorization isomorphism.

**[PROVED HERE]** Every step is categorical and dependency-closed.

## Lean realization
- Module: `formal/GaloisForLFunctions/HTGeometry/StokesAbstractEnhancedVerdier.lean`
- Negligible subcategory: `Negligible`
- Quotient and functor: `EnhancedQuotient`, `quotientFunctor`
- Triangulated quotient: `enhancedQuotient_isTriangulated`
- Kernel theorem: `quotient_obj_isZero_of_negligible`, `quotient_obj_isZero`
- Universal descent: `descend`, `descendFactors`
- Verification: direct `lake env lean`, targeted module build, and `#print axioms` for every new declaration passed. Dependencies are only `propext`, `Classical.choice`, and `Quot.sound`; `Negligible` itself is axiom-free.

## Scope boundary
Actual enhanced ind-sheaves require `D = Dᵇ(Ik_{M×ℝ∞})` and `F = π⁻¹`, plus ind-sheaves, bounded constructibility, proof that `π⁻¹` is fully faithful and triangulated, quotient adjoints, and six operations. None is claimed here.

## Log
- 2026-08-24 — paper proof completed after hostile corpus audit identified absence of actual enhanced quotient
- 2026-08-24 — formalized quotient kernel; direct check, targeted build, and new-declaration axiom audit passed
