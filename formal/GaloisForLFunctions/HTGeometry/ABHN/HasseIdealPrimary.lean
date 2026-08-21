/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealPrime

/-!
# Hasse detection of primary ideals

Field scalar extension is faithfully flat.  A primary extended ideal contracts to a primary ideal,
and faithful flatness contracts the extension of a fixed ideal back to that ideal.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If the extension of an ideal to a field scalar extension is primary, then the original ideal
is primary. -/
theorem ideal_isPrimary_of_tensorProduct_map_isPrimary {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I : Ideal A)
    (h : (I.map (algebraMap A (L ⊗[K] A))).IsPrimary) : I.IsPrimary := by
  letI : Module.FaithfullyFlat A (A ⊗[K] L) := inferInstance
  letI : Module.FaithfullyFlat A (L ⊗[K] A) :=
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[K] L)
      (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  have hcomap : (I.map (algebraMap A (L ⊗[K] A))).comap
      (algebraMap A (L ⊗[K] A)) |>.IsPrimary :=
    h.comap (algebraMap A (L ⊗[K] A))
  rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at hcomap

/-- If an ideal becomes primary at every completed place of a number field, it is primary. -/
theorem numberField_ideal_isPrimary_of_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    (∀ p : NumberFieldPlace K,
      (I.map (algebraMap A (completion K p ⊗[K] A))).IsPrimary) → I.IsPrimary := by
  intro h
  exact ideal_isPrimary_of_tensorProduct_map_isPrimary
    (L := completion K (witnessPlace K)) I (h (witnessPlace K))

/-- If an ideal becomes primary at every finite or infinite completed place of `F(t)`, it is
primary. -/
theorem rationalFunction_ideal_isPrimary_of_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    (∀ p : RationalFunctionPlace F,
      (I.map (algebraMap A
        (rationalFunctionCompletion F p ⊗[RatFunc F] A))).IsPrimary) → I.IsPrimary := by
  intro h
  exact ideal_isPrimary_of_tensorProduct_map_isPrimary
    (L := rationalFunctionCompletion F .infinite) I (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
