/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealPrimary

/-!
# Hasse detection of local rings

Faithfully flat scalar extension reflects the property of being a local ring. Thus, if a fixed
algebra becomes local after each completion, then it was already local.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If a commutative algebra becomes local after field scalar extension, then it was local. -/
theorem isLocalRing_of_tensorProduct_isLocalRing {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    [IsLocalRing (L ⊗[K] A)] : IsLocalRing A := by
  letI : Module.FaithfullyFlat A (A ⊗[K] L) := inferInstance
  letI : Module.FaithfullyFlat A (L ⊗[K] A) :=
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[K] L)
      (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  exact Module.FaithfullyFlat.isLocalRing A (L ⊗[K] A)

/-- If a commutative number-field algebra becomes local at every completed place, it is local. -/
theorem numberField_isLocalRing_of_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    (∀ p : NumberFieldPlace K, IsLocalRing (completion K p ⊗[K] A)) → IsLocalRing A := by
  intro h
  letI : IsLocalRing (completion K (witnessPlace K) ⊗[K] A) := h (witnessPlace K)
  exact isLocalRing_of_tensorProduct_isLocalRing
    (K := K) (L := completion K (witnessPlace K)) (A := A)

/-- If a commutative `F(t)`-algebra becomes local at every finite or infinite completed place,
it is local. -/
theorem rationalFunction_isLocalRing_of_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    (∀ p : RationalFunctionPlace F,
      IsLocalRing (rationalFunctionCompletion F p ⊗[RatFunc F] A)) → IsLocalRing A := by
  intro h
  letI : IsLocalRing (rationalFunctionCompletion F .infinite ⊗[RatFunc F] A) := h .infinite
  exact isLocalRing_of_tensorProduct_isLocalRing
    (K := RatFunc F) (L := rationalFunctionCompletion F .infinite) (A := A)

/-- If a scalar extension at one number-field completion is local, then the global algebra is
local. -/
theorem numberField_isLocalRing_of_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    (∃ p : NumberFieldPlace K, IsLocalRing (completion K p ⊗[K] A)) → IsLocalRing A := by
  rintro ⟨p, hp⟩
  letI : IsLocalRing (completion K p ⊗[K] A) := hp
  exact isLocalRing_of_tensorProduct_isLocalRing
    (K := K) (L := completion K p) (A := A)

/-- If a scalar extension at one `F(t)`-completion is local, then the global algebra is local. -/
theorem rationalFunction_isLocalRing_of_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    (∃ p : RationalFunctionPlace F,
      IsLocalRing (rationalFunctionCompletion F p ⊗[RatFunc F] A)) → IsLocalRing A := by
  rintro ⟨p, hp⟩
  letI : IsLocalRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) := hp
  exact isLocalRing_of_tensorProduct_isLocalRing
    (K := RatFunc F) (L := rationalFunctionCompletion F p) (A := A)

end GaloisForLFunctions.HTGeometry.ABHN
