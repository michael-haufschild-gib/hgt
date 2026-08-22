/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealPrimary

/-!
# Hasse detection of ideal relations

Faithful flatness identifies every ideal with the contraction of its scalar extension. Therefore,
equality and containment of fixed ideals can be checked after field scalar extension and at every
completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Containment of ideals is reflected by field scalar extension. -/
theorem ideal_map_le_iff_tensorProduct {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I J : Ideal A) :
    I.map (algebraMap A (L ⊗[K] A)) ≤ J.map (algebraMap A (L ⊗[K] A)) ↔ I ≤ J := by
  letI : Module.FaithfullyFlat A (A ⊗[K] L) := inferInstance
  letI : Module.FaithfullyFlat A (L ⊗[K] A) :=
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[K] L)
      (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  constructor
  · intro h
    have hI : (I.map (algebraMap A (L ⊗[K] A))).comap
        (algebraMap A (L ⊗[K] A)) = I :=
      Ideal.comap_map_eq_self_of_faithfullyFlat I
    have hJ : (J.map (algebraMap A (L ⊗[K] A))).comap
        (algebraMap A (L ⊗[K] A)) = J :=
      Ideal.comap_map_eq_self_of_faithfullyFlat J
    rw [← hI, ← hJ]
    exact Ideal.comap_mono h
  · exact Ideal.map_mono

/-- Equality of ideals is reflected by field scalar extension. -/
theorem ideal_map_eq_iff_tensorProduct {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I J : Ideal A) :
    I.map (algebraMap A (L ⊗[K] A)) = J.map (algebraMap A (L ⊗[K] A)) ↔ I = J := by
  constructor
  · intro h
    apply le_antisymm
    · exact (ideal_map_le_iff_tensorProduct I J).mp (le_of_eq h)
    · exact (ideal_map_le_iff_tensorProduct J I).mp (le_of_eq h.symm)
  · intro h
    rw [h]

/-- Ideal containment in a commutative number-field algebra is detected at every completed
place. -/
theorem numberField_ideal_map_le_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) :
    I ≤ J ↔ ∀ p : NumberFieldPlace K,
      I.map (algebraMap A (completion K p ⊗[K] A)) ≤
        J.map (algebraMap A (completion K p ⊗[K] A)) := by
  constructor
  · intro h p
    exact (ideal_map_le_iff_tensorProduct (L := completion K p) I J).mpr h
  · intro h
    exact (ideal_map_le_iff_tensorProduct (L := completion K (witnessPlace K)) I J).mp
      (h (witnessPlace K))

/-- Equality of ideals in a commutative number-field algebra is detected at every completed
place. -/
theorem numberField_ideal_map_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) :
    I = J ↔ ∀ p : NumberFieldPlace K,
      I.map (algebraMap A (completion K p ⊗[K] A)) =
        J.map (algebraMap A (completion K p ⊗[K] A)) := by
  constructor
  · intro h p
    exact (ideal_map_eq_iff_tensorProduct (L := completion K p) I J).mpr h
  · intro h
    exact (ideal_map_eq_iff_tensorProduct (L := completion K (witnessPlace K)) I J).mp
      (h (witnessPlace K))

/-- Ideal containment in a commutative `F(t)`-algebra is detected at every finite and infinite
completed place. -/
theorem rationalFunction_ideal_map_le_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :
    I ≤ J ↔ ∀ p : RationalFunctionPlace F,
      I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) ≤
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) := by
  constructor
  · intro h p
    exact (ideal_map_le_iff_tensorProduct (L := rationalFunctionCompletion F p) I J).mpr h
  · intro h
    exact (ideal_map_le_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite) I J).mp (h .infinite)

/-- Equality of ideals in a commutative `F(t)`-algebra is detected at every finite and infinite
completed place. -/
theorem rationalFunction_ideal_map_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :
    I = J ↔ ∀ p : RationalFunctionPlace F,
      I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) =
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) := by
  constructor
  · intro h p
    exact (ideal_map_eq_iff_tensorProduct (L := rationalFunctionCompletion F p) I J).mpr h
  · intro h
    exact (ideal_map_eq_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite) I J).mp (h .infinite)

/-- Ideal containment in a number-field algebra can be certified at one completion. -/
theorem numberField_ideal_map_le_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) :
    I ≤ J ↔ ∃ p : NumberFieldPlace K,
      I.map (algebraMap A (completion K p ⊗[K] A)) ≤
        J.map (algebraMap A (completion K p ⊗[K] A)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (ideal_map_le_iff_tensorProduct (L := completion K (witnessPlace K)) I J).mpr h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_map_le_iff_tensorProduct (L := completion K p) I J).mp hp

/-- Equality of ideals in a number-field algebra can be certified at one completion. -/
theorem numberField_ideal_map_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) :
    I = J ↔ ∃ p : NumberFieldPlace K,
      I.map (algebraMap A (completion K p ⊗[K] A)) =
        J.map (algebraMap A (completion K p ⊗[K] A)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (ideal_map_eq_iff_tensorProduct (L := completion K (witnessPlace K)) I J).mpr h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_map_eq_iff_tensorProduct (L := completion K p) I J).mp hp

/-- Ideal containment in an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_ideal_map_le_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :
    I ≤ J ↔ ∃ p : RationalFunctionPlace F,
      I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) ≤
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (ideal_map_le_iff_tensorProduct (L := rationalFunctionCompletion F .infinite) I J).mpr h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_map_le_iff_tensorProduct (L := rationalFunctionCompletion F p) I J).mp hp

/-- Equality of ideals in an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_ideal_map_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :
    I = J ↔ ∃ p : RationalFunctionPlace F,
      I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) =
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (ideal_map_eq_iff_tensorProduct (L := rationalFunctionCompletion F .infinite) I J).mpr h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_map_eq_iff_tensorProduct (L := rationalFunctionCompletion F p) I J).mp hp

end GaloisForLFunctions.HTGeometry.ABHN
