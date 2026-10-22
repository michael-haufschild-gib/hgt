import GaloisForLFunctions.HTGeometry.PositiveRationalSteinbergSquare
import GaloisForLFunctions.RHTower.Deninger.DeningerSteinbergKummerSuccessorNormalTransgression
import Mathlib.Data.Sign.Basic

/-!
# Exact positive Steinberg ideal in the actual rational-adelic group algebra

The positive complementary Steinberg relations generate exactly the square of the ideal
spanned by positive-rational augmentation generators. This upgrades the existing one-sided
augmentation-square inclusion to an exact ideal classification.

The carrier includes negative rationals. Its full augmentation square is strictly larger:
the rational sign character annihilates the positive relations but detects the square of
`[-1] - 1`. Thus the negative-scaling sector must not be silently removed.

These are unconditional statements about the existing source algebra. They do not assert
that the Kummer derivation descends or that the geometric Xi compatibility law holds.
-/

namespace RHTower
open GaloisForLFunctions.RHTower
noncomputable section

/-- Positive-rational augmentation ideal; the independent sign factor is retained. -/
def deningerPositiveAugmentationIdeal : Ideal RouteRMultiplierKOne.KummerGroupRing :=
  Ideal.span (Set.range (fun q : {q : ℚ // 0 < q} =>
    deningerSteinbergBasis (deningerScalingOfPositiveRational q.1 q.2) - 1))

private def steinbergQuotientCharacter :
    ℚˣ →* (RouteRMultiplierKOne.KummerGroupRing ⧸ deningerKummerSteinbergIdeal) where
  toFun q := Ideal.Quotient.mk _ (deningerSteinbergBasis ⟨q⟩)
  map_one' := by
    change Ideal.Quotient.mk _ (deningerSteinbergBasis 1) = 1
    simp
  map_mul' q r := by
    change Ideal.Quotient.mk _ (deningerSteinbergBasis (⟨q⟩ * ⟨r⟩)) = _
    simp

private theorem steinbergQuotientCharacter_relation
    (x y : ℚˣ) (hx : 0 < (x : ℚ)) (hy : 0 < (y : ℚ))
    (hxy : (x : ℚ) + (y : ℚ) = 1) :
    (steinbergQuotientCharacter x - 1) * (steinbergQuotientCharacter y - 1) = 0 := by
  let p : DeningerPositiveSteinbergPair := ⟨x, y, hx, hy, hxy⟩
  have hm : deningerPositiveSteinbergCell p ∈ deningerKummerSteinbergIdeal :=
    Ideal.subset_span (Set.mem_range_self p)
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  simpa [deningerPositiveSteinbergCell, p, deningerScalingOfPositiveRational,
    steinbergQuotientCharacter] using h

/-- All products of positive-rational augmentation generators are honest Steinberg relations. -/
theorem deningerPositiveAugmentation_product_mem_steinbergIdeal
    (q r : ℚ) (hq : 0 < q) (hr : 0 < r) :
    (deningerSteinbergBasis (deningerScalingOfPositiveRational q hq) - 1) *
      (deningerSteinbergBasis (deningerScalingOfPositiveRational r hr) - 1) ∈
        deningerKummerSteinbergIdeal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h2 : IsUnit (2 : RouteRMultiplierKOne.KummerGroupRing ⧸ deningerKummerSteinbergIdeal) := by
    have h := (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map
      (algebraMap ℂ (RouteRMultiplierKOne.KummerGroupRing ⧸ deningerKummerSteinbergIdeal))
    simpa only [map_ofNat] using h
  have h := GaloisForLFunctions.HTGeometry.PositiveRationalSteinberg.positive_products_zero steinbergQuotientCharacter h2
    steinbergQuotientCharacter_relation (Units.mk0 q hq.ne') (Units.mk0 r hr.ne') hq hr
  simpa [deningerScalingOfPositiveRational, steinbergQuotientCharacter] using h

/-- Exact source relation ideal: its quotient retains the full positive first-order layer. -/
theorem deningerKummerSteinbergIdeal_eq_positiveAugmentationIdeal_sq :
    deningerKummerSteinbergIdeal = deningerPositiveAugmentationIdeal ^ 2 := by
  apply le_antisymm
  · rw [deningerKummerSteinbergIdeal, Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    rw [pow_two]
    exact Ideal.mul_mem_mul
      (Ideal.subset_span (Set.mem_range_self (⟨p.x, p.x_pos⟩ : {q : ℚ // 0 < q})))
      (Ideal.subset_span (Set.mem_range_self (⟨p.y, p.y_pos⟩ : {q : ℚ // 0 < q})))
  · rw [pow_two, deningerPositiveAugmentationIdeal, Ideal.span_mul_span, Ideal.span_le]
    rintro _ ⟨a, ⟨q, rfl⟩, b, ⟨r, rfl⟩, rfl⟩
    exact deningerPositiveAugmentation_product_mem_steinbergIdeal q.1 r.1 q.2 r.2

end
end RHTower

namespace RHTower
open GaloisForLFunctions.RHTower
noncomputable section

private def deningerRationalSignCharacter : CCMRationalAdelicScaling →* ℂ where
  toFun k := SignType.castHom (signHom (k.val : ℚ))
  map_one' := by simp
  map_mul' k l := by simp [sign_mul]

/-- The rational sign character reads the independent negative-scaling sector. -/
def deningerKummerSignAugmentation : RouteRMultiplierKOne.KummerGroupRing →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ CCMRationalAdelicScaling deningerRationalSignCharacter

@[simp] theorem deningerKummerSignAugmentation_positive
    (q : ℚ) (hq : 0 < q) :
    deningerKummerSignAugmentation
      (deningerSteinbergBasis (deningerScalingOfPositiveRational q hq)) = 1 := by
  simp [deningerKummerSignAugmentation, deningerSteinbergBasis,
    deningerRationalSignCharacter, deningerScalingOfPositiveRational,
    signHom, sign_pos hq]

theorem deningerKummerSteinbergIdeal_le_signKernel :
    deningerKummerSteinbergIdeal ≤ RingHom.ker deningerKummerSignAugmentation.toRingHom := by
  rw [deningerKummerSteinbergIdeal, Ideal.span_le]
  rintro _ ⟨p, rfl⟩
  change deningerKummerSignAugmentation (deningerPositiveSteinbergCell p) = 0
  simp [deningerPositiveSteinbergCell]

/-- Positive Steinberg relations do not kill the negative-scaling augmentation square. -/
theorem deningerNegativeScaling_square_not_mem_steinbergIdeal :
    (deningerSteinbergBasis ⟨(-1 : ℚˣ)⟩ - 1) ^ 2 ∉ deningerKummerSteinbergIdeal := by
  intro hm
  have h := deningerKummerSteinbergIdeal_le_signKernel hm
  change deningerKummerSignAugmentation
    ((deningerSteinbergBasis ⟨(-1 : ℚˣ)⟩ - 1) ^ 2) = 0 at h
  norm_num [deningerKummerSignAugmentation, deningerSteinbergBasis,
    deningerRationalSignCharacter, signHom] at h

/-- The full augmentation square is strictly larger because it also contains the sign factor. -/
theorem deningerKummerSteinbergIdeal_lt_augmentationIdeal_sq :
    deningerKummerSteinbergIdeal < deningerKummerAugmentationIdeal ^ 2 := by
  refine lt_of_le_of_ne deningerKummerSteinbergIdeal_le_augmentationIdeal_sq ?_
  intro he
  apply deningerNegativeScaling_square_not_mem_steinbergIdeal
  rw [he]
  have hm := deningerSteinbergBasis_sub_one_mem_augmentationIdeal ⟨(-1 : ℚˣ)⟩
  have hh : (deningerSteinbergBasis ⟨(-1 : ℚˣ)⟩ - 1) *
      (deningerSteinbergBasis ⟨(-1 : ℚˣ)⟩ - 1) ∈
        deningerKummerAugmentationIdeal * deningerKummerAugmentationIdeal :=
    Ideal.mul_mem_mul hm hm
  simpa only [pow_two] using hh

end
end RHTower


