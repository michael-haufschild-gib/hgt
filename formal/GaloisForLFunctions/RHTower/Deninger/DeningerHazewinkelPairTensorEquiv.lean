import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelUniversalMultiplicationDescent
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Hazewinkel pair quotient as an integer tensor product

This module identifies the two-block universal coordinate quotient used in corrected rational-Witt
multiplication with the tensor product over `ℤ` of the individual Hazewinkel stage quotients.
Both directions are given by explicit maps on polynomial generators and proved mutually inverse.

This removes an abstraction gap in the universal descent: reducedness of the pair quotient is
literally reducedness of Deninger's ring `R_n ⊗_ℤ R_m`, not an additional hidden premise.
-/

namespace RHTower
noncomputable section
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 200000

abbrev DeningerHazewinkelStageQuotient (n : ℕ) :=
  DeningerHazewinkelCoordinateRing ⧸ deningerHazewinkelIdeal n

abbrev DeningerHazewinkelStageTensor (n m : ℕ) :=
  (CommRingCat.coproductCocone
    (CommRingCat.of (DeningerHazewinkelStageQuotient n))
    (CommRingCat.of (DeningerHazewinkelStageQuotient m))).pt

def deningerHazewinkelStageTensorLeft (n m : ℕ) :
    DeningerHazewinkelStageQuotient n →+* DeningerHazewinkelStageTensor n m :=
  (CommRingCat.coproductCocone
    (CommRingCat.of (DeningerHazewinkelStageQuotient n))
    (CommRingCat.of (DeningerHazewinkelStageQuotient m))).inl.hom

def deningerHazewinkelStageTensorRight (n m : ℕ) :
    DeningerHazewinkelStageQuotient m →+* DeningerHazewinkelStageTensor n m :=
  (CommRingCat.coproductCocone
    (CommRingCat.of (DeningerHazewinkelStageQuotient n))
    (CommRingCat.of (DeningerHazewinkelStageQuotient m))).inr.hom

@[simp] theorem deningerHazewinkelStageTensorLeft_apply (n m : ℕ)
    (x : DeningerHazewinkelStageQuotient n) :
    deningerHazewinkelStageTensorLeft n m x =
      x ⊗ₜ[ℤ] (1 : DeningerHazewinkelStageQuotient m) := by
  rfl

@[simp] theorem deningerHazewinkelStageTensorRight_apply (n m : ℕ)
    (y : DeningerHazewinkelStageQuotient m) :
    deningerHazewinkelStageTensorRight n m y =
      (1 : DeningerHazewinkelStageQuotient n) ⊗ₜ[ℤ] y := by
  rfl

def deningerHazewinkelPairToTensor (n m : ℕ) :
    DeningerHazewinkelPairCoordinateRing →+*
      DeningerHazewinkelStageTensor n m :=
  MvPolynomial.eval₂Hom
      (Int.castRingHom (DeningerHazewinkelStageTensor n m)) fun x : Bool × ℕ =>
    if x.1 then
      (1 : DeningerHazewinkelStageQuotient n) ⊗ₜ[ℤ]
        (Ideal.Quotient.mk (deningerHazewinkelIdeal m) (MvPolynomial.X x.2))
    else
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n) (MvPolynomial.X x.2)) ⊗ₜ[ℤ]
        (1 : DeningerHazewinkelStageQuotient m)

theorem deningerHazewinkelPairToTensor_comp_left (n m : ℕ) :
    (deningerHazewinkelPairToTensor n m).comp deningerHazewinkelPairLeft =
      (deningerHazewinkelStageTensorLeft n m).comp
        (Ideal.Quotient.mk (deningerHazewinkelIdeal n)) := by
  apply DFunLike.ext _ _
  intro p
  induction p using MvPolynomial.induction_on with
  | C z => simp [deningerHazewinkelPairToTensor, deningerHazewinkelPairLeft]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, map_mul, hp]
      congr 1
      simp [RingHom.comp_apply, deningerHazewinkelPairLeft,
        deningerHazewinkelPairToTensor,
        deningerHazewinkelStageTensorLeft_apply]

theorem deningerHazewinkelPairToTensor_comp_right (n m : ℕ) :
    (deningerHazewinkelPairToTensor n m).comp deningerHazewinkelPairRight =
      (deningerHazewinkelStageTensorRight n m).comp
        (Ideal.Quotient.mk (deningerHazewinkelIdeal m)) := by
  apply DFunLike.ext _ _
  intro p
  induction p using MvPolynomial.induction_on with
  | C z => simp [deningerHazewinkelPairToTensor, deningerHazewinkelPairRight]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, map_mul, hp]
      congr 1
      simp [RingHom.comp_apply, deningerHazewinkelPairRight,
        deningerHazewinkelPairToTensor,
        deningerHazewinkelStageTensorRight_apply]

theorem deningerHazewinkelPairIdeal_le_ker_pairToTensor (n m : ℕ) :
    deningerHazewinkelPairIdeal n m ≤
      RingHom.ker (deningerHazewinkelPairToTensor n m) := by
  rw [deningerHazewinkelPairIdeal, sup_le_iff]
  constructor
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change deningerHazewinkelPairToTensor n m (deningerHazewinkelPairLeft p) = 0
    rw [← RingHom.comp_apply, deningerHazewinkelPairToTensor_comp_left]
    change deningerHazewinkelStageTensorLeft n m
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n) p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change deningerHazewinkelPairToTensor n m (deningerHazewinkelPairRight p) = 0
    rw [← RingHom.comp_apply, deningerHazewinkelPairToTensor_comp_right]
    change deningerHazewinkelStageTensorRight n m
      (Ideal.Quotient.mk (deningerHazewinkelIdeal m) p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

def deningerHazewinkelPairQuotientToTensor (n m : ℕ) :
    DeningerHazewinkelPairQuotient n m →+*
      DeningerHazewinkelStageTensor n m :=
  Ideal.Quotient.lift (deningerHazewinkelPairIdeal n m)
    (deningerHazewinkelPairToTensor n m)
    (deningerHazewinkelPairIdeal_le_ker_pairToTensor n m)

def deningerHazewinkelLeftStageToPairQuotient (n m : ℕ) :
    DeningerHazewinkelStageQuotient n →+*
      DeningerHazewinkelPairQuotient n m :=
  Ideal.Quotient.lift (deningerHazewinkelIdeal n)
    (deningerHazewinkelPairLeftQuotient n m)
    (deningerHazewinkelPairLeftQuotient_ker n m)

def deningerHazewinkelRightStageToPairQuotient (n m : ℕ) :
    DeningerHazewinkelStageQuotient m →+*
      DeningerHazewinkelPairQuotient n m :=
  Ideal.Quotient.lift (deningerHazewinkelIdeal m)
    (deningerHazewinkelPairRightQuotient n m)
    (deningerHazewinkelPairRightQuotient_ker n m)

def deningerHazewinkelTensorToPairQuotient (n m : ℕ) :
    DeningerHazewinkelStageTensor n m →+*
      DeningerHazewinkelPairQuotient n m :=
  ((CommRingCat.coproductCoconeIsColimit
      (CommRingCat.of (DeningerHazewinkelStageQuotient n))
      (CommRingCat.of (DeningerHazewinkelStageQuotient m))).desc
    (CategoryTheory.Limits.BinaryCofan.mk
      (CommRingCat.ofHom (deningerHazewinkelLeftStageToPairQuotient n m))
      (CommRingCat.ofHom (deningerHazewinkelRightStageToPairQuotient n m)))).hom

theorem deningerHazewinkelTensorToPairQuotient_comp_left (n m : ℕ) :
    (deningerHazewinkelTensorToPairQuotient n m).comp
        (deningerHazewinkelStageTensorLeft n m) =
      deningerHazewinkelLeftStageToPairQuotient n m := by
  exact congrArg CommRingCat.Hom.hom
    ((CommRingCat.coproductCoconeIsColimit
      (CommRingCat.of (DeningerHazewinkelStageQuotient n))
      (CommRingCat.of (DeningerHazewinkelStageQuotient m))).fac
      (CategoryTheory.Limits.BinaryCofan.mk
        (P := CommRingCat.of (DeningerHazewinkelPairQuotient n m))
        (CommRingCat.ofHom (deningerHazewinkelLeftStageToPairQuotient n m))
        (CommRingCat.ofHom (deningerHazewinkelRightStageToPairQuotient n m)))
      (CategoryTheory.Discrete.mk CategoryTheory.Limits.WalkingPair.left))

theorem deningerHazewinkelTensorToPairQuotient_comp_right (n m : ℕ) :
    (deningerHazewinkelTensorToPairQuotient n m).comp
        (deningerHazewinkelStageTensorRight n m) =
      deningerHazewinkelRightStageToPairQuotient n m := by
  exact congrArg CommRingCat.Hom.hom
    ((CommRingCat.coproductCoconeIsColimit
      (CommRingCat.of (DeningerHazewinkelStageQuotient n))
      (CommRingCat.of (DeningerHazewinkelStageQuotient m))).fac
      (CategoryTheory.Limits.BinaryCofan.mk
        (P := CommRingCat.of (DeningerHazewinkelPairQuotient n m))
        (CommRingCat.ofHom (deningerHazewinkelLeftStageToPairQuotient n m))
        (CommRingCat.ofHom (deningerHazewinkelRightStageToPairQuotient n m)))
      (CategoryTheory.Discrete.mk CategoryTheory.Limits.WalkingPair.right))

theorem deningerHazewinkelTensorToPairQuotient_tmul (n m : ℕ)
    (x : DeningerHazewinkelStageQuotient n)
    (y : DeningerHazewinkelStageQuotient m) :
    deningerHazewinkelTensorToPairQuotient n m (x ⊗ₜ[ℤ] y) =
      deningerHazewinkelLeftStageToPairQuotient n m x *
        deningerHazewinkelRightStageToPairQuotient n m y := by
  have ht : (x ⊗ₜ[ℤ] y : DeningerHazewinkelStageTensor n m) =
      deningerHazewinkelStageTensorLeft n m x *
        deningerHazewinkelStageTensorRight n m y := by
    rw [deningerHazewinkelStageTensorLeft_apply,
      deningerHazewinkelStageTensorRight_apply]
    change x ⊗ₜ[ℤ] y = Algebra.TensorProduct.mul
      (x ⊗ₜ[ℤ] (1 : DeningerHazewinkelStageQuotient m))
      ((1 : DeningerHazewinkelStageQuotient n) ⊗ₜ[ℤ] y)
    rw [Algebra.TensorProduct.mul_apply]
    simp
  rw [ht, map_mul, ← RingHom.comp_apply,
    deningerHazewinkelTensorToPairQuotient_comp_left,
    ← RingHom.comp_apply,
    deningerHazewinkelTensorToPairQuotient_comp_right]

theorem deningerHazewinkelPairQuotientToTensor_comp_leftStage (n m : ℕ) :
    (deningerHazewinkelPairQuotientToTensor n m).comp
        (deningerHazewinkelLeftStageToPairQuotient n m) =
      deningerHazewinkelStageTensorLeft n m := by
  apply DFunLike.ext _ _
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change deningerHazewinkelPairToTensor n m
      (deningerHazewinkelPairLeft p) =
    deningerHazewinkelStageTensorLeft n m
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n) p)
  rw [← RingHom.comp_apply, deningerHazewinkelPairToTensor_comp_left]
  rfl

theorem deningerHazewinkelPairQuotientToTensor_comp_rightStage (n m : ℕ) :
    (deningerHazewinkelPairQuotientToTensor n m).comp
        (deningerHazewinkelRightStageToPairQuotient n m) =
      deningerHazewinkelStageTensorRight n m := by
  apply DFunLike.ext _ _
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  change deningerHazewinkelPairToTensor n m
      (deningerHazewinkelPairRight p) =
    deningerHazewinkelStageTensorRight n m
      (Ideal.Quotient.mk (deningerHazewinkelIdeal m) p)
  rw [← RingHom.comp_apply, deningerHazewinkelPairToTensor_comp_right]
  rfl

@[simp] theorem deningerHazewinkelPairQuotientToTensor_mk_X_false
    (n m j : ℕ) :
    deningerHazewinkelPairQuotientToTensor n m
        (Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m)
          (MvPolynomial.X (false, j))) =
      deningerHazewinkelStageTensorLeft n m
        (Ideal.Quotient.mk (deningerHazewinkelIdeal n) (MvPolynomial.X j)) := by
  change deningerHazewinkelPairToTensor n m (MvPolynomial.X (false, j)) = _
  simp [deningerHazewinkelPairToTensor]

@[simp] theorem deningerHazewinkelPairQuotientToTensor_mk_X_true
    (n m j : ℕ) :
    deningerHazewinkelPairQuotientToTensor n m
        (Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m)
          (MvPolynomial.X (true, j))) =
      deningerHazewinkelStageTensorRight n m
        (Ideal.Quotient.mk (deningerHazewinkelIdeal m) (MvPolynomial.X j)) := by
  change deningerHazewinkelPairToTensor n m (MvPolynomial.X (true, j)) = _
  simp [deningerHazewinkelPairToTensor]

@[simp] theorem deningerHazewinkelLeftStageToPairQuotient_mk_X
    (n m j : ℕ) :
    deningerHazewinkelLeftStageToPairQuotient n m
        (Ideal.Quotient.mk (deningerHazewinkelIdeal n) (MvPolynomial.X j)) =
      Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m)
        (MvPolynomial.X (false, j)) := by
  simp [deningerHazewinkelLeftStageToPairQuotient,
    deningerHazewinkelPairLeftQuotient, deningerHazewinkelPairLeft]

@[simp] theorem deningerHazewinkelRightStageToPairQuotient_mk_X
    (n m j : ℕ) :
    deningerHazewinkelRightStageToPairQuotient n m
        (Ideal.Quotient.mk (deningerHazewinkelIdeal m) (MvPolynomial.X j)) =
      Ideal.Quotient.mk (deningerHazewinkelPairIdeal n m)
        (MvPolynomial.X (true, j)) := by
  simp [deningerHazewinkelRightStageToPairQuotient,
    deningerHazewinkelPairRightQuotient, deningerHazewinkelPairRight]

theorem deningerHazewinkelTensorPair_leftInverse (n m : ℕ) :
    Function.LeftInverse (deningerHazewinkelTensorToPairQuotient n m)
      (deningerHazewinkelPairQuotientToTensor n m) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [deningerHazewinkelPairQuotientToTensor,
        deningerHazewinkelPairToTensor,
        deningerHazewinkelTensorToPairQuotient]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p x hp =>
      rw [map_mul, map_mul, map_mul, hp]
      rcases x with ⟨b, j⟩
      cases b
      · rw [deningerHazewinkelPairQuotientToTensor_mk_X_false,
          ← RingHom.comp_apply,
          deningerHazewinkelTensorToPairQuotient_comp_left]
        rw [deningerHazewinkelLeftStageToPairQuotient_mk_X]
      · rw [deningerHazewinkelPairQuotientToTensor_mk_X_true,
          ← RingHom.comp_apply,
          deningerHazewinkelTensorToPairQuotient_comp_right]
        rw [deningerHazewinkelRightStageToPairQuotient_mk_X]

theorem deningerHazewinkelTensorPair_rightInverse (n m : ℕ) :
    Function.RightInverse (deningerHazewinkelTensorToPairQuotient n m)
      (deningerHazewinkelPairQuotientToTensor n m) := by
  intro t
  have hhom :
      (deningerHazewinkelPairQuotientToTensor n m).comp
          (deningerHazewinkelTensorToPairQuotient n m) =
        RingHom.id (DeningerHazewinkelStageTensor n m) := by
    apply CommRingCat.hom_ext_iff.mp
    apply CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext
      (CommRingCat.coproductCoconeIsColimit
        (CommRingCat.of (DeningerHazewinkelStageQuotient n))
        (CommRingCat.of (DeningerHazewinkelStageQuotient m)))
    · apply CommRingCat.hom_ext
      change ((deningerHazewinkelPairQuotientToTensor n m).comp
          (deningerHazewinkelTensorToPairQuotient n m)).comp
            (deningerHazewinkelStageTensorLeft n m) =
        (RingHom.id (DeningerHazewinkelStageTensor n m)).comp
          (deningerHazewinkelStageTensorLeft n m)
      rw [RingHom.comp_assoc,
        deningerHazewinkelTensorToPairQuotient_comp_left,
        deningerHazewinkelPairQuotientToTensor_comp_leftStage]
      rfl
    · apply CommRingCat.hom_ext
      change ((deningerHazewinkelPairQuotientToTensor n m).comp
          (deningerHazewinkelTensorToPairQuotient n m)).comp
            (deningerHazewinkelStageTensorRight n m) =
        (RingHom.id (DeningerHazewinkelStageTensor n m)).comp
          (deningerHazewinkelStageTensorRight n m)
      rw [RingHom.comp_assoc,
        deningerHazewinkelTensorToPairQuotient_comp_right,
        deningerHazewinkelPairQuotientToTensor_comp_rightStage]
      rfl
  exact RingHom.congr_fun hhom t

/-- The universal pair-coordinate quotient is canonically the coproduct, hence tensor product
over `ℤ`, of the two one-stage Hazewinkel quotients. -/
def deningerHazewinkelPairQuotientTensorEquiv (n m : ℕ) :
    DeningerHazewinkelPairQuotient n m ≃+*
      DeningerHazewinkelStageTensor n m :=
  RingEquiv.ofBijective (deningerHazewinkelPairQuotientToTensor n m)
    ⟨deningerHazewinkelTensorPair_leftInverse n m |>.injective,
      deningerHazewinkelTensorPair_rightInverse n m |>.surjective⟩

/-- Reducedness of the universal two-block quotient is exactly reducedness of the tensor product
of the two individual Hazewinkel quotients. -/
theorem deningerHazewinkelPairQuotient_isReduced_iff_stageTensor (n m : ℕ) :
    IsReduced (DeningerHazewinkelPairQuotient n m) ↔
      IsReduced (DeningerHazewinkelStageTensor n m) := by
  constructor
  · intro h
    letI := h
    exact isReduced_of_injective
      (deningerHazewinkelPairQuotientTensorEquiv n m).symm.toRingHom
      (deningerHazewinkelPairQuotientTensorEquiv n m).symm.injective
  · intro h
    letI := h
    exact isReduced_of_injective
      (deningerHazewinkelPairQuotientTensorEquiv n m).toRingHom
      (deningerHazewinkelPairQuotientTensorEquiv n m).injective

end
end RHTower
