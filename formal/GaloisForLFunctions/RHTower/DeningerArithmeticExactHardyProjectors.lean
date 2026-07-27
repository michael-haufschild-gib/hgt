import GaloisForLFunctions.HTGeometry.BRSTHodgeConstraint

/-!
# Exact Hardy projectors from an arithmetic chirality involution

Once the global arithmetic Calderón almost-involution has been
replaced by its exact self-adjoint polar sign `C`, its positive and
negative Hardy projectors are forced:

`Π₊ = (1 + C) / 2`, `Π₋ = (1 - C) / 2`.

This file proves their exact complementary, orthogonal-projector
identities.  It assumes only self-adjointness and `C² = 1`; it does
not assume a zeta-zero splitting or the Riemann hypothesis.
-/

namespace RHTower

noncomputable section

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

/-- Positive Hardy projector associated with a chirality operator. -/
def deningerHardyPlus (C : E →L[ℂ] E) : E →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (1 + C)

/-- Negative Hardy projector associated with a chirality operator. -/
def deningerHardyMinus (C : E →L[ℂ] E) : E →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (1 - C)

omit [CompleteSpace E] in
@[simp]
theorem deningerHardyPlus_apply (C : E →L[ℂ] E) (x : E) :
    deningerHardyPlus C x = (2 : ℂ)⁻¹ • (x + C x) := by
  rfl

omit [CompleteSpace E] in
@[simp]
theorem deningerHardyMinus_apply (C : E →L[ℂ] E) (x : E) :
    deningerHardyMinus C x = (2 : ℂ)⁻¹ • (x - C x) := by
  rfl

omit [CompleteSpace E] in
/-- Pointwise form of `C² = 1`. -/
theorem deningerChirality_apply_apply_eq_of_sq_eq_one
    (C : E →L[ℂ] E)
    (hC2 : C * C = 1)
    (x : E) :
    C (C x) = x := by
  have hx := DFunLike.congr_fun hC2 x
  simpa [ContinuousLinearMap.mul_def] using hx

omit [CompleteSpace E] in
/-- The positive Hardy operator is an exact projection. -/
theorem deningerHardyPlus_idempotent
    (C : E →L[ℂ] E)
    (hC2 : C * C = 1) :
    deningerHardyPlus C * deningerHardyPlus C =
      deningerHardyPlus C := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.mul_apply,
    deningerHardyPlus_apply, deningerHardyPlus_apply,
    map_smul, map_add,
    deningerChirality_apply_apply_eq_of_sq_eq_one C hC2 x]
  module

omit [CompleteSpace E] in
/-- The negative Hardy operator is an exact projection. -/
theorem deningerHardyMinus_idempotent
    (C : E →L[ℂ] E)
    (hC2 : C * C = 1) :
    deningerHardyMinus C * deningerHardyMinus C =
      deningerHardyMinus C := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.mul_apply,
    deningerHardyMinus_apply, deningerHardyMinus_apply,
    map_smul, map_sub,
    deningerChirality_apply_apply_eq_of_sq_eq_one C hC2 x]
  module

omit [CompleteSpace E] in
/-- The two Hardy projectors sum to the identity. -/
theorem deningerHardyPlus_add_minus
    (C : E →L[ℂ] E) :
    deningerHardyPlus C + deningerHardyMinus C = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.add_apply,
    deningerHardyPlus_apply, deningerHardyMinus_apply]
  change
    (2 : ℂ)⁻¹ • (x + C x) +
      (2 : ℂ)⁻¹ • (x - C x) = x
  module

omit [CompleteSpace E] in
/-- Positive followed by negative Hardy projection is zero. -/
theorem deningerHardyPlus_mul_minus
    (C : E →L[ℂ] E)
    (hC2 : C * C = 1) :
    deningerHardyPlus C * deningerHardyMinus C = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.mul_apply,
    deningerHardyPlus_apply, deningerHardyMinus_apply,
    map_smul, map_sub,
    deningerChirality_apply_apply_eq_of_sq_eq_one C hC2 x]
  change
    (2 : ℂ)⁻¹ •
      ((2 : ℂ)⁻¹ • (x - C x) +
        (2 : ℂ)⁻¹ • (C x - x)) = 0
  module

omit [CompleteSpace E] in
/-- Negative followed by positive Hardy projection is zero. -/
theorem deningerHardyMinus_mul_plus
    (C : E →L[ℂ] E)
    (hC2 : C * C = 1) :
    deningerHardyMinus C * deningerHardyPlus C = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.mul_apply,
    deningerHardyMinus_apply, deningerHardyPlus_apply,
    map_smul, map_add,
    deningerChirality_apply_apply_eq_of_sq_eq_one C hC2 x]
  change
    (2 : ℂ)⁻¹ •
      ((2 : ℂ)⁻¹ • (x + C x) -
        (2 : ℂ)⁻¹ • (C x + x)) = 0
  module

omit [CompleteSpace E] in
/-- Difference of the exact Hardy projectors recovers chirality. -/
theorem deningerHardyPlus_sub_minus
    (C : E →L[ℂ] E) :
    deningerHardyPlus C - deningerHardyMinus C = C := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.sub_apply,
    deningerHardyPlus_apply, deningerHardyMinus_apply]
  module

/-- Self-adjoint chirality gives a self-adjoint positive Hardy
projector. -/
theorem deningerHardyPlus_isSelfAdjoint
    (C : E →L[ℂ] E)
    (hC : IsSelfAdjoint C) :
    IsSelfAdjoint (deningerHardyPlus C) := by
  rw [IsSelfAdjoint, deningerHardyPlus, star_smul, star_add,
    star_one, hC.star_eq]
  norm_num

/-- Self-adjoint chirality gives a self-adjoint negative Hardy
projector. -/
theorem deningerHardyMinus_isSelfAdjoint
    (C : E →L[ℂ] E)
    (hC : IsSelfAdjoint C) :
    IsSelfAdjoint (deningerHardyMinus C) := by
  rw [IsSelfAdjoint, deningerHardyMinus, star_smul, star_sub,
    star_one, hC.star_eq]
  norm_num

end

end RHTower
