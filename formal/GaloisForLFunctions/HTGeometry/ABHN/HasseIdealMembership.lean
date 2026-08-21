import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealRelations

/-!
# Hasse detection of ideal membership

Faithful flatness identifies an ideal with the contraction of its scalar extension.  Hence a
fixed global element belongs to a fixed ideal exactly when its image belongs to the extended ideal
after every completion.  This is a local-global test for prescribed congruences, not descent of
independently chosen local ideals.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Membership in an ideal is reflected by field scalar extension. -/
theorem ideal_mem_map_iff_tensorProduct {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    (I : Ideal A) (a : A) :
    a ∈ I ↔ algebraMap A (L ⊗[K] A) a ∈ I.map (algebraMap A (L ⊗[K] A)) := by
  letI : Module.FaithfullyFlat A (A ⊗[K] L) := inferInstance
  letI : Module.FaithfullyFlat A (L ⊗[K] A) :=
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[K] L)
      (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  constructor
  · intro ha
    exact Ideal.mem_map_of_mem (algebraMap A (L ⊗[K] A)) ha
  · intro h
    have hcomap : (I.map (algebraMap A (L ⊗[K] A))).comap
        (algebraMap A (L ⊗[K] A)) = I :=
      Ideal.comap_map_eq_self_of_faithfullyFlat I
    rw [← hcomap]
    exact h

/-- A prescribed ideal congruence in a commutative number-field algebra is detected at every
completed place. -/
theorem numberField_ideal_mem_map_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A]
    (I : Ideal A) (a : A) :
    a ∈ I ↔ ∀ p : NumberFieldPlace K,
      algebraMap A (completion K p ⊗[K] A) a ∈
        I.map (algebraMap A (completion K p ⊗[K] A)) := by
  constructor
  · intro h p
    exact (ideal_mem_map_iff_tensorProduct (L := completion K p) I a).mp h
  · intro h
    exact (ideal_mem_map_iff_tensorProduct (L := completion K (witnessPlace K)) I a).mpr
      (h (witnessPlace K))

/-- A prescribed ideal congruence in a commutative `F(t)`-algebra is detected at every finite
and infinite completed place. -/
theorem rationalFunction_ideal_mem_map_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A]
    (I : Ideal A) (a : A) :
    a ∈ I ↔ ∀ p : RationalFunctionPlace F,
      algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A) a ∈
        I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) := by
  constructor
  · intro h p
    exact (ideal_mem_map_iff_tensorProduct
      (L := rationalFunctionCompletion F p) I a).mp h
  · intro h
    exact (ideal_mem_map_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite) I a).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
