import GaloisForLFunctions.BiarithmeticGeometry.Affine.PolynomialCoefficients
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteColumns
import GaloisForLFunctions.HTGeometry.PolynomialShiftDifference

/-!
# Polynomial primitives of finite-dimensional affine coefficients

Integrating the rational Newton expansion gives a right unit-translation primitive with zero
values on dilations. Its coefficients factor through the dilation homomorphism; the right
translation coordinate has two column generators. The primitive therefore has finite column rank.
-/

open Polynomial Finset Module
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Every polynomial has a unit-shift primitive vanishing at zero. -/
theorem exists_normalized_shift_primitive (P : ℂ[X]) :
    ∃ Q : ℂ[X], Q.eval 0 = 0 ∧ Q.comp (X + C 1) - Q = P := by
  obtain ⟨Q, hQ⟩ := HTGeometry.exists_shiftDiff_eq (one_ne_zero : (1 : ℂ) ≠ 0) P
  refine ⟨Q - C (Q.eval 0), ?_, ?_⟩
  · rw [eval_sub, eval_C, sub_self]
  · simpa only [sub_comp, C_comp, sub_sub_sub_cancel_right] using hQ

def normalizedShiftPrimitive (P : ℂ[X]) : ℂ[X] :=
  (exists_normalized_shift_primitive P).choose

theorem normalizedShiftPrimitive_zero (P : ℂ[X]) :
    (normalizedShiftPrimitive P).eval 0 = 0 :=
  (exists_normalized_shift_primitive P).choose_spec.1

theorem normalizedShiftPrimitive_difference (P : ℂ[X]) (z : ℂ) :
    (normalizedShiftPrimitive P).eval (z + 1) -
      (normalizedShiftPrimitive P).eval z = P.eval z := by
  have h := congrArg (fun Q : ℂ[X] => Q.eval z)
    (exists_normalized_shift_primitive P).choose_spec.2
  simpa only [normalizedShiftPrimitive, eval_sub, eval_comp, eval_add, eval_X, eval_C] using h

/-- The homomorphism forgetting the translation component. -/
def affineDilationPart : AffineGroupQ →* AffineGroupQ where
  toFun g := dilation (Units.mk0 (affSlope g) (affSlope_ne_zero g))
  map_one' := by
    exact (congrArg dilation (Units.ext affSlope_one)).trans (map_one dilation)
  map_mul' g h := by
    rw [← map_mul]
    congr 1
    exact Units.ext (affSlope_mul g h)

/-- Translation coordinate in the factorization `g = D_a T_t`. -/
def rightTranslationCoordinate (g : AffineGroupQ) : ℚ := affShift g / affSlope g

theorem affineDilationPart_dilation (u : ℚˣ) :
    affineDilationPart (dilation u) = dilation u := by
  change dilation (Units.mk0 _ _) = dilation u
  congr 1
  exact Units.ext (affSlope_dilation u)

theorem affineDilationPart_translation (b : ℚ) :
    affineDilationPart (translation b) = 1 := by
  change dilation (Units.mk0 _ _) = 1
  rw [← map_one dilation]
  congr 1
  exact Units.ext (affSlope_translation b)

theorem rightTranslationCoordinate_dilation (u : ℚˣ) :
    rightTranslationCoordinate (dilation u) = 0 := by
  rw [rightTranslationCoordinate, affShift_dilation, zero_div]

theorem rightTranslationCoordinate_mul_translation (g : AffineGroupQ) (b : ℚ) :
    rightTranslationCoordinate (g * translation b) = rightTranslationCoordinate g + b := by
  simp only [rightTranslationCoordinate, affShift_mul, affSlope_mul,
    affShift_translation, affSlope_translation, mul_one]
  field_simp [affSlope_ne_zero g]
  ring

theorem eq_dilationPart_mul_translation (g : AffineGroupQ) :
    g = affineDilationPart g * translation (rightTranslationCoordinate g) := by
  apply affine_ext
  · simp only [affineDilationPart, MonoidHom.coe_mk, OneHom.coe_mk,
      affSlope_mul, affSlope_dilation, Units.val_mk0, affSlope_translation, mul_one]
  · simp only [affineDilationPart, MonoidHom.coe_mk, OneHom.coe_mk,
      affShift_mul, affSlope_dilation, Units.val_mk0, affShift_translation,
      affShift_dilation, add_zero, rightTranslationCoordinate]
    field_simp [affSlope_ne_zero g]

theorem rightTranslationCoordinate_inv_mul (x g : AffineGroupQ) :
    rightTranslationCoordinate (x⁻¹ * g) =
      rightTranslationCoordinate g - affShift x / affSlope g := by
  simp only [rightTranslationCoordinate, affShift_mul, affSlope_mul,
    affShift_inv, affSlope_inv]
  field_simp [affSlope_ne_zero x, affSlope_ne_zero g]
  ring

/-- Two column generators make the right translation coordinate finite rank. -/
theorem finite_columnSpan_rightTranslationCoordinate :
    Module.Finite ℂ (kernelColumnSpan (fun g => (rightTranslationCoordinate g : ℂ))) := by
  let F : Fin 2 → AffineGroupQ → ℂ := ![fun _ => 1, fun x => (affShift x : ℂ)]
  apply finite_columnSpan_of_features F
  intro g
  have he : kernelColumn (fun g => (rightTranslationCoordinate g : ℂ)) g =
      (rightTranslationCoordinate g : ℂ) • F 0 +
        (-(affSlope g : ℂ)⁻¹) • F 1 := by
    funext x
    change (rightTranslationCoordinate (x⁻¹ * g) : ℂ) =
      (rightTranslationCoordinate g : ℂ) * 1 + (-(affSlope g : ℂ)⁻¹) * (affShift x : ℂ)
    rw [rightTranslationCoordinate_inv_mul, Rat.cast_sub, Rat.cast_div]
    ring
  rw [he]
  exact (Submodule.span ℂ (Set.range F)).add_mem
    ((Submodule.span ℂ (Set.range F)).smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
    ((Submodule.span ℂ (Set.range F)).smul_mem _ (Submodule.subset_span ⟨1, rfl⟩))

section Coefficient
variable {V : Type*} [AddCommMonoid V] [Module ℂ V] [Module.Finite ℂ V]
local instance : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ

/-- Integrate a finite affine coefficient along right translation, with zero dilation values. -/
def affineCoefficientPrimitive (ρ : AffineGroupQ →* End ℂ V)
    (L : V →ₗ[ℂ] ℂ) (v : V) (g : AffineGroupQ) : ℂ :=
  ∑ j ∈ range (finrank ℂ V),
    L (ρ (affineDilationPart g) (((ρ (translation 1) - 1) ^ j) v)) *
      (normalizedShiftPrimitive (C ((j.factorial : ℂ)⁻¹) * descPochhammer ℂ j)).eval
        (rightTranslationCoordinate g : ℂ)

omit [Module.Finite ℂ V] in
theorem affineCoefficientPrimitive_dilation (ρ : AffineGroupQ →* End ℂ V)
    (L : V →ₗ[ℂ] ℂ) (v : V) (u : ℚˣ) :
    affineCoefficientPrimitive ρ L v (dilation u) = 0 := by
  simp only [affineCoefficientPrimitive, rightTranslationCoordinate_dilation,
    Rat.cast_zero, normalizedShiftPrimitive_zero, mul_zero, sum_const_zero]

theorem finite_columnSpan_affineCoefficientPrimitive (ρ : AffineGroupQ →* End ℂ V)
    (L : V →ₗ[ℂ] ℂ) (v : V) :
    Module.Finite ℂ (kernelColumnSpan (affineCoefficientPrimitive ρ L v)) := by
  apply finite_columnSpan_sum (range (finrank ℂ V))
  intro j _
  letI := finite_columnSpan_of_representation (ρ.comp affineDilationPart) L
    (((ρ (translation 1) - 1) ^ j) v)
  letI := finite_columnSpan_rightTranslationCoordinate
  letI := finite_columnSpan_polynomial (fun g => (rightTranslationCoordinate g : ℂ))
    (normalizedShiftPrimitive (C ((j.factorial : ℂ)⁻¹) * descPochhammer ℂ j))
  exact finite_columnSpan_mul
    (fun g => L (ρ (affineDilationPart g) (((ρ (translation 1) - 1) ^ j) v)))
    (fun g => (normalizedShiftPrimitive (C ((j.factorial : ℂ)⁻¹) * descPochhammer ℂ j)).eval
      (rightTranslationCoordinate g : ℂ))

/-- The unit right difference recovers the original coefficient. -/
theorem affineCoefficientPrimitive_difference (ρ : AffineGroupQ →* End ℂ V)
    (L : V →ₗ[ℂ] ℂ) (v : V) (g : AffineGroupQ) :
    affineCoefficientPrimitive ρ L v (g * translation 1) -
      affineCoefficientPrimitive ρ L v g = L (ρ g v) := by
  let A : End ℂ V →ₗ[ℂ] ℂ :=
    { toFun := fun U => L (ρ (affineDilationPart g) (U v))
      map_add' U W := by simp only [LinearMap.add_apply, map_add]
      map_smul' c U := by simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply] }
  have he := unipotent_rational_coefficient (finrank ℂ V)
    (fun b => ρ (translation b)) (by rw [translation_zero, map_one])
    (by intro a b; rw [translation_add, map_mul])
    (finite_rational_affine_end_translation_unipotent ρ) A (rightTranslationCoordinate g)
  have hcoefficient : A (ρ (translation (rightTranslationCoordinate g))) = L (ρ g v) := by
    change L (ρ (affineDilationPart g) (ρ (translation (rightTranslationCoordinate g)) v)) = _
    rw [← Module.End.mul_apply, ← map_mul, ← eq_dilationPart_mul_translation]
  rw [hcoefficient] at he
  rw [← he]
  simp only [affineCoefficientPrimitive, map_mul, affineDilationPart_translation, mul_one,
    rightTranslationCoordinate_mul_translation, Rat.cast_add, Rat.cast_one,
    unipotentPowerPolynomial, eval_finsetSum, eval_mul, eval_C, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [← mul_sub, normalizedShiftPrimitive_difference, eval_mul, eval_C]
  change _ = (L (ρ (affineDilationPart g) (((ρ (translation 1) - 1) ^ j) v)) /
    (j.factorial : ℂ)) * (descPochhammer ℂ j).eval (rightTranslationCoordinate g : ℂ)
  ring

end Coefficient

#print axioms exists_normalized_shift_primitive
#print axioms finite_columnSpan_rightTranslationCoordinate
#print axioms finite_columnSpan_affineCoefficientPrimitive
#print axioms affineCoefficientPrimitive_difference
end GaloisForLFunctions.BiarithmeticGeometry
