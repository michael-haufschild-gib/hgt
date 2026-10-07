import GaloisForLFunctions.RHTower.DeningerPositiveSteinbergSquare
import GaloisForLFunctions.RHTower.CyclicBarAlgHomMorphism
import GaloisForLFunctions.RHTower.SquareZeroUnitCyclicBoundary

/-!
# Exact Hochschild–cyclic comparison for the positive Steinberg source

The canonical tensor-power image of the existing multiplier K1 normal cycle survives in
Hochschild degree one with its original augmentation–Kummer value. Its image in ordinary
cyclic degree one vanishes, by an explicit square-zero boundary calculation.

This uses the actual positive Steinberg ideal in the full rational-scaling group algebra;
the negative-rational sign sector is retained. No RH or Xi compatibility premise is used.
Relative and negative cyclic Chern characters are not asserted to vanish.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower
namespace PositiveSteinbergCyclic
abbrev Source := RouteRMultiplierKOne.KummerGroupRing
abbrev Quotient := Source ⧸ deningerKummerSteinbergIdeal

/-- Canonical algebra quotient by the actual positive Steinberg relations. -/
def quotientMap : Source →ₐ[ℂ] Quotient := Ideal.Quotient.mkₐ ℂ deningerKummerSteinbergIdeal

/-- Source augmentation descends through the relation ideal. -/
def augmentation : Quotient →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ deningerKummerSteinbergIdeal deningerKummerAugmentation
    (fun _ h => (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0))
      (deningerKummerSteinbergIdeal_le_augmentationIdeal_sq h))

/-- The augmentation–Kummer derivative descends as a linear tangent functional. -/
def regulator : Quotient →ₗ[ℂ] ℂ :=
  (deningerKummerSteinbergIdeal.restrictScalars ℂ).liftQ deningerKummerRegulator
    (fun _ h => deningerKummerRegulator_eq_zero_of_mem_steinbergIdeal h)

@[simp] theorem augmentation_quotientMap (a : Source) :
    augmentation (quotientMap a) = deningerKummerAugmentation a := rfl
@[simp] theorem regulator_quotientMap (a : Source) :
    regulator (quotientMap a) = deningerKummerRegulator a := rfl

@[simp] theorem regulator_one : regulator 1 = 0 := by
  change regulator (quotientMap 1) = 0
  rw [regulator_quotientMap, deningerKummerRegulator_one]

theorem regulator_mul (a b : Quotient) :
    regulator (a*b) = augmentation a * regulator b + regulator a * augmentation b := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  exact deningerKummerRegulator_mul a b

/-- Actual selector normal direction in the Steinberg quotient. -/
def normalTangent (m : DeningerSteinbergDepth) : Quotient :=
  quotientMap (deningerSteinbergNormalEscape m)

@[simp] theorem augmentation_normalTangent (m : DeningerSteinbergDepth) :
    augmentation (normalTangent m) = 0 := by
  simp [normalTangent, deningerSteinbergNormalEscape_eq]

@[simp] theorem regulator_normalTangent (m : DeningerSteinbergDepth) :
    regulator (normalTangent m) = (m : ℂ) * (Real.log (3/2 : ℝ) : ℂ) := by
  exact deningerKummerRegulator_normalEscape m

theorem regulator_normalTangent_ne_zero (m : DeningerSteinbergDepth) :
    regulator (normalTangent m) ≠ 0 :=
  deningerKummerRegulator_normalEscape_ne_zero m

theorem normalTangent_square (m : DeningerSteinbergDepth) :
    normalTangent m * normalTangent m = 0 := by
  change quotientMap (deningerSteinbergNormalEscape m) *
    quotientMap (deningerSteinbergNormalEscape m) = 0
  rw [← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [deningerSteinbergNormalEscape_eq]
  exact deningerPositiveAugmentation_product_mem_steinbergIdeal
    ((3/2 : ℚ) ^ (m : ℕ)) ((3/2 : ℚ) ^ (m : ℕ))
    (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)

private theorem quotient_basis_ratio (m : DeningerSteinbergDepth) :
    quotientMap (deningerSteinbergBasis (deningerSteinbergRatioScaling m)) =
      1 + normalTangent m := by
  simp [normalTangent, deningerSteinbergNormalEscape_eq]

private theorem quotient_basis_ratio_inv (m : DeningerSteinbergDepth) :
    quotientMap (deningerSteinbergBasis (deningerSteinbergRatioScaling m)⁻¹) =
      1 - normalTangent m := by
  have hu : quotientMap (deningerSteinbergBasis (deningerSteinbergRatioScaling m)⁻¹) *
      (1 + normalTangent m) = 1 := by
    rw [← quotient_basis_ratio, ← map_mul, ← deningerSteinbergBasis_mul]
    simp
  have hv : (1 + normalTangent m) * (1 - normalTangent m) = 1 := by
    have h := normalTangent_square m
    calc _ = 1 - normalTangent m * normalTangent m := by ring
         _ = 1 := by rw [h, sub_zero]
  calc
    _ = quotientMap (deningerSteinbergBasis (deningerSteinbergRatioScaling m)⁻¹) *
        ((1 + normalTangent m) * (1 - normalTangent m)) := by rw [hv, mul_one]
    _ = 1 - normalTangent m := by rw [← mul_assoc, hu, one_mul]

/-- Canonical tensor-power image of the existing multiplier K1 source cycle. -/
def normalCycle (m : DeningerSteinbergDepth) : CyclicBarTensor ℂ Quotient 1 :=
  cyclicBarAlgHomDegree (quotientMap.comp RouteRMultiplierKOne.multiplierToKummerGroupRing) 1
    (deningerSteinbergNormalKOneCycle m)

/-- Identifies the actual source image, not merely a separately chosen unit cycle. -/
theorem normalCycle_eq (m : DeningerSteinbergDepth) :
    normalCycle m = SquareZeroCyclic.pair (1-normalTangent m) (1+normalTangent m) := by
  rw [normalCycle, deningerSteinbergNormalKOneCycle, cyclicBarAlgHomDegree_tprod]
  apply congrArg (PiTensorProduct.tprod ℂ)
  ext i; fin_cases i
  · change quotientMap (RouteRMultiplierKOne.multiplierToKummerGroupRing
      (↑((RouteRMultiplierKOne.dilUnit (deningerSteinbergRatioScaling m))⁻¹) :
        RouteRMultiplierKOne.Mult)) = 1 - normalTangent m
    rw [RouteRMultiplierKOne.multiplierToKummerGroupRing_dilUnit_inv]
    exact quotient_basis_ratio_inv m
  · change quotientMap (RouteRMultiplierKOne.multiplierToKummerGroupRing
      ((RouteRMultiplierKOne.dilUnit (deningerSteinbergRatioScaling m) :
        RouteRMultiplierKOne.Multˣ) : RouteRMultiplierKOne.Mult)) = 1 + normalTangent m
    rw [RouteRMultiplierKOne.multiplierToKummerGroupRing_dilUnit]
    exact quotient_basis_ratio m

theorem normalCycle_is_cycle (m : DeningerSteinbergDepth) :
    cyclicBarFace (R := ℂ) (0 : Fin 2) (normalCycle m) =
      cyclicBarFace (R := ℂ) (1 : Fin 2) (normalCycle m) := by
  rw [normalCycle_eq]
  exact SquareZeroCyclic.pair_is_cycle _ _ (mul_comm _ _)

/-- The quotient retains the exact source normal period in Hochschild degree one. -/
theorem normalCycle_regulator (m : DeningerSteinbergDepth) :
    SquareZeroCyclic.augmentationDetector augmentation regulator (normalCycle m) =
      (m : ℂ) * (Real.log (3/2 : ℝ) : ℂ) := by
  rw [normalCycle_eq, SquareZeroCyclic.augmentationDetector_unit
    augmentation regulator regulator_one _ (augmentation_normalTangent m), regulator_normalTangent]

/-- Positive survivor: the actual image remains a nonzero Hochschild-one class. -/
theorem normalCycle_not_mem_boundaryTwo_range (m : DeningerSteinbergDepth) :
    normalCycle m ∉ LinearMap.range SquareZeroCyclic.boundaryTwo := by
  rw [normalCycle_eq]
  exact SquareZeroCyclic.unit_not_mem_boundaryTwo_range augmentation regulator
    regulator_mul regulator_one _ (augmentation_normalTangent m)
    (regulator_normalTangent_ne_zero m)

/-- Ordinary cyclic descent kills this same source class. -/
theorem normalCycle_mem_cyclicRelations (m : DeningerSteinbergDepth) :
    normalCycle m ∈ SquareZeroCyclic.cyclicRelations := by
  rw [normalCycle_eq]
  exact SquareZeroCyclic.unit_mem_cyclicRelations _ (normalTangent_square m)

/-- No functional annihilating the ordinary cyclic relations can preserve the original period. -/
theorem no_cyclic_normal_regulator (m : DeningerSteinbergDepth)
    (L : CyclicBarTensor ℂ Quotient 1 →ₗ[ℂ] ℂ)
    (hL : SquareZeroCyclic.cyclicRelations ≤ LinearMap.ker L) :
    L (normalCycle m) ≠ (m : ℂ) * (Real.log (3/2 : ℝ) : ℂ) := by
  have hz : L (normalCycle m) = 0 := hL (normalCycle_mem_cyclicRelations m)
  intro heq
  apply regulator_normalTangent_ne_zero m
  rw [regulator_normalTangent, ← heq, hz]
end PositiveSteinbergCyclic
end RHTower
