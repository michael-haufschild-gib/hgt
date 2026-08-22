/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealFiniteness

/-!
# Hasse detection of radical ideals

Field scalar extension is faithfully flat.  Consequently, radicality of an extended fixed ideal
descends.  The converse is deliberately not asserted: an arbitrary field extension can turn a
radical ideal into a non-radical ideal through inseparability.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If the extension of an ideal to a field scalar extension is radical, then the original ideal
is radical. -/
theorem ideal_isRadical_of_tensorProduct_map_isRadical {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I : Ideal A)
    (h : (I.map (algebraMap A (L ⊗[K] A))).IsRadical) : I.IsRadical := by
  letI : Module.FaithfullyFlat A (A ⊗[K] L) := inferInstance
  letI : Module.FaithfullyFlat A (L ⊗[K] A) :=
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[K] L)
      (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  have hcomap : (I.map (algebraMap A (L ⊗[K] A))).comap
      (algebraMap A (L ⊗[K] A)) |>.IsRadical :=
    h.comap (algebraMap A (L ⊗[K] A))
  rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at hcomap

/-- If an ideal becomes radical at every completed place of a number field, it is radical. -/
theorem numberField_ideal_isRadical_of_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    (∀ p : NumberFieldPlace K,
      (I.map (algebraMap A (completion K p ⊗[K] A))).IsRadical) → I.IsRadical := by
  intro h
  exact ideal_isRadical_of_tensorProduct_map_isRadical
    (L := completion K (witnessPlace K)) I (h (witnessPlace K))

/-- If an ideal becomes radical at every finite or infinite completed place of `F(t)`, it is
radical. -/
theorem rationalFunction_ideal_isRadical_of_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    (∀ p : RationalFunctionPlace F,
      (I.map (algebraMap A
        (rationalFunctionCompletion F p ⊗[RatFunc F] A))).IsRadical) → I.IsRadical := by
  intro h
  exact ideal_isRadical_of_tensorProduct_map_isRadical
    (L := rationalFunctionCompletion F .infinite) I (h .infinite)

/-- If an ideal becomes radical at one number-field completion, then it is radical globally. -/
theorem numberField_ideal_isRadical_of_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    (∃ p : NumberFieldPlace K,
      (I.map (algebraMap A (completion K p ⊗[K] A))).IsRadical) → I.IsRadical := by
  rintro ⟨p, hp⟩
  exact ideal_isRadical_of_tensorProduct_map_isRadical (L := completion K p) I hp

/-- If an ideal becomes radical at one `F(t)`-completion, then it is radical globally. -/
theorem rationalFunction_ideal_isRadical_of_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    (∃ p : RationalFunctionPlace F,
      (I.map (algebraMap A
        (rationalFunctionCompletion F p ⊗[RatFunc F] A))).IsRadical) → I.IsRadical := by
  rintro ⟨p, hp⟩
  exact ideal_isRadical_of_tensorProduct_map_isRadical
    (L := rationalFunctionCompletion F p) I hp

end GaloisForLFunctions.HTGeometry.ABHN
