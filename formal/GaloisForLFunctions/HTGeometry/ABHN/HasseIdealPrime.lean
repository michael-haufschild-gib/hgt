/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealRadical

/-!
# Hasse detection of prime ideals

Field scalar extension is faithfully flat.  A prime extended ideal contracts to a prime ideal, and
faithful flatness identifies that contraction with the original ideal.  This gives a local-to-global
test for primeness of a fixed ideal.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If the extension of an ideal to a field scalar extension is prime, then the original ideal is
prime. -/
theorem ideal_isPrime_of_tensorProduct_map_isPrime {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I : Ideal A)
    (h : (I.map (algebraMap A (L ⊗[K] A))).IsPrime) : I.IsPrime := by
  letI : Module.FaithfullyFlat A (A ⊗[K] L) := inferInstance
  letI : Module.FaithfullyFlat A (L ⊗[K] A) :=
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[K] L)
      (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  have hcomap : (I.map (algebraMap A (L ⊗[K] A))).comap
      (algebraMap A (L ⊗[K] A)) |>.IsPrime :=
    h.comap (algebraMap A (L ⊗[K] A))
  rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at hcomap

/-- If an ideal becomes prime at every completed place of a number field, it is prime. -/
theorem numberField_ideal_isPrime_of_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    (∀ p : NumberFieldPlace K,
      (I.map (algebraMap A (completion K p ⊗[K] A))).IsPrime) → I.IsPrime := by
  intro h
  exact ideal_isPrime_of_tensorProduct_map_isPrime
    (L := completion K (witnessPlace K)) I (h (witnessPlace K))

/-- If an ideal becomes prime at every finite or infinite completed place of `F(t)`, it is prime. -/
theorem rationalFunction_ideal_isPrime_of_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    (∀ p : RationalFunctionPlace F,
      (I.map (algebraMap A
        (rationalFunctionCompletion F p ⊗[RatFunc F] A))).IsPrime) → I.IsPrime := by
  intro h
  exact ideal_isPrime_of_tensorProduct_map_isPrime
    (L := rationalFunctionCompletion F .infinite) I (h .infinite)

/-- If an ideal becomes prime at one number-field completion, then it is prime globally. -/
theorem numberField_ideal_isPrime_of_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    (∃ p : NumberFieldPlace K,
      (I.map (algebraMap A (completion K p ⊗[K] A))).IsPrime) → I.IsPrime := by
  rintro ⟨p, hp⟩
  exact ideal_isPrime_of_tensorProduct_map_isPrime (L := completion K p) I hp

/-- If an ideal becomes prime at one `F(t)`-completion, then it is prime globally. -/
theorem rationalFunction_ideal_isPrime_of_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    (∃ p : RationalFunctionPlace F,
      (I.map (algebraMap A
        (rationalFunctionCompletion F p ⊗[RatFunc F] A))).IsPrime) → I.IsPrime := by
  rintro ⟨p, hp⟩
  exact ideal_isPrime_of_tensorProduct_map_isPrime
    (L := rationalFunctionCompletion F p) I hp

end GaloisForLFunctions.HTGeometry.ABHN
