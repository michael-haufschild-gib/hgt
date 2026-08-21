/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealRelations

/-!
# Hasse detection for coprime ideals

Faithfully flat field scalar extension reflects coprimality of ideals in a commutative algebra.
Consequently, Chinese-remainder decompositions specified by global ideals can be checked at every
completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Coprimality of ideals is reflected by tensoring a commutative algebra along a field extension.
-/
theorem ideal_isCoprime_iff_tensorProduct {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I J : Ideal A) :
    IsCoprime I J ↔ IsCoprime (I.map (algebraMap A (L ⊗[K] A)))
      (J.map (algebraMap A (L ⊗[K] A))) := by
  letI : Module.FaithfullyFlat A (A ⊗[K] L) := inferInstance
  letI : Module.FaithfullyFlat A (L ⊗[K] A) :=
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[K] L)
      (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  constructor
  · intro h
    rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
    rw [← Ideal.map_sup, h, Ideal.map_top]
  · intro h
    rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
    calc
      I ⊔ J = ((I ⊔ J).map (algebraMap A (L ⊗[K] A))).comap
          (algebraMap A (L ⊗[K] A)) :=
        (Ideal.comap_map_eq_self_of_faithfullyFlat (I ⊔ J)).symm
      _ = (I.map (algebraMap A (L ⊗[K] A)) ⊔ J.map (algebraMap A (L ⊗[K] A))).comap
          (algebraMap A (L ⊗[K] A)) := by rw [Ideal.map_sup]
      _ = (⊤ : Ideal (L ⊗[K] A)).comap (algebraMap A (L ⊗[K] A)) := by rw [h]
      _ = ⊤ := Ideal.comap_top

/-- Ideals in a commutative number-field algebra are coprime exactly when their extensions are
coprime at every completed place. -/
theorem numberField_ideal_isCoprime_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) :
    IsCoprime I J ↔ ∀ p : NumberFieldPlace K,
      IsCoprime (I.map (algebraMap A (completion K p ⊗[K] A)))
        (J.map (algebraMap A (completion K p ⊗[K] A))) := by
  constructor
  · intro h p
    exact (ideal_isCoprime_iff_tensorProduct (L := completion K p) I J).mp h
  · intro h
    exact (ideal_isCoprime_iff_tensorProduct (L := completion K (witnessPlace K)) I J).mpr
      (h (witnessPlace K))

/-- Ideals in a commutative `F(t)`-algebra are coprime exactly when their extensions are coprime
at every finite and infinite completed place. -/
theorem rationalFunction_ideal_isCoprime_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :
    IsCoprime I J ↔ ∀ p : RationalFunctionPlace F,
      IsCoprime (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)))
        (J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))) := by
  constructor
  · intro h p
    exact (ideal_isCoprime_iff_tensorProduct (L := rationalFunctionCompletion F p) I J).mp h
  · intro h
    exact (ideal_isCoprime_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite) I J).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
