import GaloisForLFunctions.BiarithmeticGeometry.Affine.PositiveAffineIndex
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Affine actions on rational vector spaces

Positive rational scalars act by additive automorphisms. An injective rational linear
translation map induces an injective affine homomorphism.
-/

open GaloisForLFunctions.ArithmeticPositiveDuality
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- Positive rational scalars act by additive automorphisms. -/
def positiveRationalScalarAut (u : posUnits) : MulAut (Multiplicative V) where
  toFun x := Multiplicative.ofAdd (((u : ℚˣ) : ℚ) • x.toAdd)
  invFun x := Multiplicative.ofAdd ((((u⁻¹ : posUnits) : ℚˣ) : ℚ) • x.toAdd)
  left_inv x := by
    change Multiplicative.ofAdd ((((u : ℚˣ)⁻¹ : ℚˣ) : ℚ) •
      (((u : ℚˣ) : ℚ) • x.toAdd)) = x
    rw [Units.val_inv_eq_inv_val, ← mul_smul, inv_mul_cancel₀ (u : ℚˣ).ne_zero, one_smul]
    rfl
  right_inv x := by
    change Multiplicative.ofAdd (((u : ℚˣ) : ℚ) •
      (((((u : ℚˣ)⁻¹ : ℚˣ) : ℚ)) • x.toAdd)) = x
    rw [Units.val_inv_eq_inv_val, ← mul_smul, mul_inv_cancel₀ (u : ℚˣ).ne_zero, one_smul]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (((u : ℚˣ) : ℚ) • (x.toAdd + y.toAdd)) =
      Multiplicative.ofAdd (((u : ℚˣ) : ℚ) • x.toAdd + ((u : ℚˣ) : ℚ) • y.toAdd)
    rw [smul_add]

/-- The scalar action used in the positive rational affine semidirect product. -/
def positiveRationalScalarAction : posUnits →* MulAut (Multiplicative V) where
  toFun := positiveRationalScalarAut V
  map_one' := by
    ext x
    change Multiplicative.ofAdd ((1 : ℚ) • x.toAdd) = x
    rw [one_smul]
    rfl
  map_mul' u v := by
    ext x
    change Multiplicative.ofAdd ((((u : ℚˣ) : ℚ) * ((v : ℚˣ) : ℚ)) • x.toAdd) =
      Multiplicative.ofAdd (((u : ℚˣ) : ℚ) • (((v : ℚˣ) : ℚ) • x.toAdd))
    rw [mul_smul]

/-- The group of translations of a rational vector space and positive rational dilations. -/
abbrev PositiveRationalAffineGroup :=
  SemidirectProduct (Multiplicative V) posUnits (positiveRationalScalarAction V)

/-- A rational linear map of translation spaces induces the corresponding affine homomorphism. -/
def positiveRationalAffineMap (ι : ℚ →ₗ[ℚ] V) : posAffine →* PositiveRationalAffineGroup V where
  toFun g := ⟨Multiplicative.ofAdd (ι (affShift g)), posAffineSlope g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (ι (affShift 1)) = 1
      rw [affShift_one, map_zero]
      rfl
    · exact map_one posAffineSlope
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (ι (affShift ((g : AffineGroupQ) * h))) =
        Multiplicative.ofAdd (ι (affShift g) + affSlope g • ι (affShift h))
      rw [affShift_mul, map_add]
      have hm : ι (affSlope g * affShift h) = affSlope g • ι (affShift h) :=
        ι.map_smul (affSlope g) (affShift h)
      rw [hm, add_comm]
    · exact map_mul posAffineSlope g h

/-- An injective translation map induces an injective affine homomorphism. -/
theorem positiveRationalAffineMap_injective (ι : ℚ →ₗ[ℚ] V) (hι : Function.Injective ι) :
    Function.Injective (positiveRationalAffineMap V ι) := by
  intro g h he
  apply Subtype.ext
  apply affine_ext
  · exact congrArg (fun x : PositiveRationalAffineGroup V => ((x.right : ℚˣ) : ℚ)) he
  · exact hι (congrArg (fun x : PositiveRationalAffineGroup V => x.left.toAdd) he)

theorem positiveRationalAffineMap_translation (ι : ℚ →ₗ[ℚ] V) (b : ℚ) :
    positiveRationalAffineMap V ι (posAffineTranslation b) =
      SemidirectProduct.inl (Multiplicative.ofAdd (ι b)) := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (ι (affShift (translation b))) = _
    rw [affShift_translation]
    rfl
  · apply Subtype.ext
    apply Units.ext
    exact affSlope_translation b

theorem positiveRationalAffineMap_dilation (ι : ℚ →ₗ[ℚ] V) (u : posUnits) :
    positiveRationalAffineMap V ι (posAffineDilation u) = SemidirectProduct.inr u := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (ι (affShift (dilation u))) = 1
    rw [affShift_dilation, map_zero]
    rfl
  · apply Subtype.ext
    apply Units.ext
    exact affSlope_dilation u

#print axioms positiveRationalAffineMap
#print axioms positiveRationalAffineMap_injective
#print axioms positiveRationalAffineMap_translation
#print axioms positiveRationalAffineMap_dilation
end GaloisForLFunctions.BiarithmeticGeometry
