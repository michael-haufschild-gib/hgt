/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseFiniteness

/-!
# Hasse descent for reduced algebras

Reducedness descends through an injective scalar-extension map.  Thus if the completed scalar
extensions of a commutative global-field algebra are reduced, then the global algebra is reduced.
The converse is deliberately not asserted: reducedness need not survive arbitrary scalar
extension without a geometric-reducedness hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A commutative algebra is reduced if one field scalar extension is reduced. -/
theorem isReduced_of_tensorProduct_isReduced {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    [IsReduced (L ⊗[K] A)] :
    IsReduced A := by
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
    (Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective K L))

/-- A commutative algebra over a number field is reduced if all completed scalar extensions are
reduced. -/
theorem numberField_isReduced_of_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A]
    (h : ∀ p : NumberFieldPlace K, IsReduced (completion K p ⊗[K] A)) :
    IsReduced A := by
  letI : IsReduced (completion K (witnessPlace K) ⊗[K] A) := h (witnessPlace K)
  exact isReduced_of_tensorProduct_isReduced (K := K) (L := completion K (witnessPlace K))

/-- A commutative algebra over `F(t)` is reduced if all finite and infinite completed scalar
extensions are reduced. -/
theorem rationalFunction_isReduced_of_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A]
    (h : ∀ p : RationalFunctionPlace F,
      IsReduced (rationalFunctionCompletion F p ⊗[RatFunc F] A)) :
    IsReduced A := by
  letI : IsReduced (rationalFunctionCompletion F .infinite ⊗[RatFunc F] A) := h .infinite
  exact isReduced_of_tensorProduct_isReduced (K := RatFunc F)
    (L := rationalFunctionCompletion F .infinite)

/-- If a scalar extension at one number-field completion is reduced, then the global algebra is
reduced. -/
theorem numberField_isReduced_of_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A]
    (h : ∃ p : NumberFieldPlace K, IsReduced (completion K p ⊗[K] A)) :
    IsReduced A := by
  obtain ⟨p, hp⟩ := h
  letI : IsReduced (completion K p ⊗[K] A) := hp
  exact isReduced_of_tensorProduct_isReduced (K := K) (L := completion K p)

/-- If a scalar extension at one `F(t)`-completion is reduced, then the global algebra is
reduced. -/
theorem rationalFunction_isReduced_of_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A]
    (h : ∃ p : RationalFunctionPlace F,
      IsReduced (rationalFunctionCompletion F p ⊗[RatFunc F] A)) :
    IsReduced A := by
  obtain ⟨p, hp⟩ := h
  letI : IsReduced (rationalFunctionCompletion F p ⊗[RatFunc F] A) := hp
  exact isReduced_of_tensorProduct_isReduced (K := RatFunc F)
    (L := rationalFunctionCompletion F p)

end GaloisForLFunctions.HTGeometry.ABHN
