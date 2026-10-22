import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixOrientationAsymmetry
import GaloisForLFunctions.RHTower.RouteRPreDivisorRationalAdelicMultiplierKOneHomology
import GaloisForLFunctions.RHTower.TateKummerWoldGammaIntervalCharacter

/-!
# Deninger Steinberg--Kummer successor normal transgression

This module constructs the depth-dependent complementary rational pair
`xₘ = 3^m/(2^m+3^m)`, `yₘ = 2^m/(2^m+3^m)` in the actual rational-adelic group algebra.  A
cubic polynomial in the existing Kummer derivation extracts the full successor edge
`[(3/2)^m] - 1` from its honest Steinberg cell.

The Kummer regulator proves that this selector lowers augmentation order and cannot descend to
ordinary Steinberg/Milnor incidence.  The same edge is the strict boundary of a canonical Tate
interval primitive.  A multiplicative half-density representation of the whole group algebra
sends it to the concrete complete-source `2 → 3` Möbius successor minus identity; its cofinal
source image converges to the nonzero theta defect while the operator norms diverge.

All algebraic and Tate statements hold at every positive depth.  Complete physical-source
statements use the honest analytic depth type `m ≥ 3`, exactly where the existing Möbius tails
are unconditionally summable.  No Xi zero, RH predicate, critical-line hypothesis, quotient
annihilation, or new axiom is used.
-/

open Complex
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

abbrev DeningerSteinbergDepth := MobiusPositiveIndex

def deningerSteinbergDenominator (m : DeningerSteinbergDepth) : ℚ :=
  2 ^ (m : ℕ) + 3 ^ (m : ℕ)

def deningerSteinbergX (m : DeningerSteinbergDepth) : ℚ :=
  3 ^ (m : ℕ) / deningerSteinbergDenominator m

def deningerSteinbergY (m : DeningerSteinbergDepth) : ℚ :=
  2 ^ (m : ℕ) / deningerSteinbergDenominator m

theorem deningerSteinbergDenominator_pos (m : DeningerSteinbergDepth) :
    0 < deningerSteinbergDenominator m := by
  unfold deningerSteinbergDenominator
  positivity

theorem deningerSteinbergX_pos (m : DeningerSteinbergDepth) :
    0 < deningerSteinbergX m := by
  exact div_pos (by positivity) (deningerSteinbergDenominator_pos m)

theorem deningerSteinbergY_pos (m : DeningerSteinbergDepth) :
    0 < deningerSteinbergY m := by
  exact div_pos (by positivity) (deningerSteinbergDenominator_pos m)

theorem deningerSteinbergX_add_Y (m : DeningerSteinbergDepth) :
    deningerSteinbergX m + deningerSteinbergY m = 1 := by
  rw [deningerSteinbergX, deningerSteinbergY]
  field_simp [deningerSteinbergDenominator_pos m |>.ne']
  unfold deningerSteinbergDenominator
  ring

theorem deningerSteinbergY_lt_X (m : DeningerSteinbergDepth) :
    deningerSteinbergY m < deningerSteinbergX m := by
  rw [deningerSteinbergX, deningerSteinbergY]
  apply div_lt_div_of_pos_right _ (deningerSteinbergDenominator_pos m)
  exact_mod_cast Nat.pow_lt_pow_left (by omega : 2 < 3) (by omega : (m : ℕ) ≠ 0)

theorem deningerSteinbergX_lt_one (m : DeningerSteinbergDepth) :
    deningerSteinbergX m < 1 := by
  nlinarith [deningerSteinbergY_pos m, deningerSteinbergX_add_Y m]

theorem deningerSteinbergY_lt_one (m : DeningerSteinbergDepth) :
    deningerSteinbergY m < 1 := by
  nlinarith [deningerSteinbergX_pos m, deningerSteinbergX_add_Y m]

theorem deningerSteinbergX_div_Y (m : DeningerSteinbergDepth) :
    deningerSteinbergX m / deningerSteinbergY m = (3 / 2 : ℚ) ^ (m : ℕ) := by
  rw [deningerSteinbergX, deningerSteinbergY]
  field_simp [deningerSteinbergDenominator_pos m |>.ne']
  rw [div_pow]
  field_simp

def deningerScalingOfPositiveRational (q : ℚ) (hq : 0 < q) :
    CCMRationalAdelicScaling :=
  ⟨Units.mk0 q hq.ne'⟩

@[simp] theorem deningerScalingOfPositiveRational_val
    (q : ℚ) (hq : 0 < q) :
    ((deningerScalingOfPositiveRational q hq).val : ℚ) = q := rfl

theorem deningerScalingOfPositiveRational_mul
    (q r : ℚ) (hq : 0 < q) (hr : 0 < r) :
    deningerScalingOfPositiveRational (q * r) (mul_pos hq hr) =
      deningerScalingOfPositiveRational q hq * deningerScalingOfPositiveRational r hr := by
  apply ccmRationalAdelicScalingEquiv.injective
  apply Units.ext
  rfl

def deningerSteinbergXScaling (m : DeningerSteinbergDepth) :
    CCMRationalAdelicScaling :=
  deningerScalingOfPositiveRational (deningerSteinbergX m) (deningerSteinbergX_pos m)

def deningerSteinbergYScaling (m : DeningerSteinbergDepth) :
    CCMRationalAdelicScaling :=
  deningerScalingOfPositiveRational (deningerSteinbergY m) (deningerSteinbergY_pos m)

def deningerSteinbergBasis (k : CCMRationalAdelicScaling) :
    RouteRMultiplierKOne.KummerGroupRing :=
  MonoidAlgebra.of ℂ CCMRationalAdelicScaling k

@[simp] theorem deningerSteinbergBasis_mul
    (k l : CCMRationalAdelicScaling) :
    deningerSteinbergBasis (k * l) = deningerSteinbergBasis k * deningerSteinbergBasis l := by
  exact map_mul (MonoidAlgebra.of ℂ CCMRationalAdelicScaling) k l

@[simp] theorem deningerSteinbergBasis_one :
    deningerSteinbergBasis 1 = 1 := by
  exact map_one (MonoidAlgebra.of ℂ CCMRationalAdelicScaling)

@[simp] theorem deningerSteinbergBasis_pow
    (k : CCMRationalAdelicScaling) (n : ℕ) :
    deningerSteinbergBasis (k ^ n) = deningerSteinbergBasis k ^ n := by
  exact map_pow (MonoidAlgebra.of ℂ CCMRationalAdelicScaling) k n

def deningerSteinbergCell (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  (deningerSteinbergBasis (deningerSteinbergXScaling m) - 1) *
    (deningerSteinbergBasis (deningerSteinbergYScaling m) - 1)

def deningerSteinbergA (m : DeningerSteinbergDepth) : ℂ :=
  (Real.log (deningerSteinbergX m : ℝ) : ℂ)

def deningerSteinbergB (m : DeningerSteinbergDepth) : ℂ :=
  (Real.log (deningerSteinbergY m : ℝ) : ℂ)

def deningerSteinbergL (m : DeningerSteinbergDepth) : ℂ :=
  deningerSteinbergA m + deningerSteinbergB m

def deningerSteinbergSelectorDenominator (m : DeningerSteinbergDepth) : ℂ :=
  deningerSteinbergA m * deningerSteinbergB m *
    (deningerSteinbergA m - deningerSteinbergB m)

def deningerSteinbergSelectorScalar
    (m : DeningerSteinbergDepth) (t : ℂ) : ℂ :=
  t * (t - deningerSteinbergL m) * (2 * t - deningerSteinbergL m) /
    deningerSteinbergSelectorDenominator m

theorem deningerSteinbergA_ne_zero (m : DeningerSteinbergDepth) :
    deningerSteinbergA m ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast deningerSteinbergX_pos m)
      (by exact_mod_cast ne_of_lt (deningerSteinbergX_lt_one m)))

theorem deningerSteinbergB_ne_zero (m : DeningerSteinbergDepth) :
    deningerSteinbergB m ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast deningerSteinbergY_pos m)
      (by exact_mod_cast ne_of_lt (deningerSteinbergY_lt_one m)))

theorem deningerSteinbergA_sub_B_ne_zero (m : DeningerSteinbergDepth) :
    deningerSteinbergA m - deningerSteinbergB m ≠ 0 := by
  apply sub_ne_zero.mpr
  have hlt : Real.log (deningerSteinbergY m : ℝ) <
      Real.log (deningerSteinbergX m : ℝ) :=
    Real.strictMonoOn_log
      (by show (0 : ℝ) < (deningerSteinbergY m : ℝ)
          exact_mod_cast deningerSteinbergY_pos m)
      (by show (0 : ℝ) < (deningerSteinbergX m : ℝ)
          exact_mod_cast deningerSteinbergX_pos m)
      (by exact_mod_cast deningerSteinbergY_lt_X m)
  intro h
  apply hlt.ne
  exact Complex.ofReal_injective (by simpa [deningerSteinbergA,
    deningerSteinbergB] using h.symm)

theorem deningerSteinbergSelectorDenominator_ne_zero
    (m : DeningerSteinbergDepth) :
    deningerSteinbergSelectorDenominator m ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (deningerSteinbergA_ne_zero m)
    (deningerSteinbergB_ne_zero m)) (deningerSteinbergA_sub_B_ne_zero m)

theorem deningerSteinbergSelectorScalar_zero (m : DeningerSteinbergDepth) :
    deningerSteinbergSelectorScalar m 0 = 0 := by
  simp [deningerSteinbergSelectorScalar]

theorem deningerSteinbergSelectorScalar_L (m : DeningerSteinbergDepth) :
    deningerSteinbergSelectorScalar m (deningerSteinbergL m) = 0 := by
  simp [deningerSteinbergSelectorScalar]

theorem deningerSteinbergSelectorScalar_A (m : DeningerSteinbergDepth) :
    deningerSteinbergSelectorScalar m (deningerSteinbergA m) = -1 := by
  rw [deningerSteinbergSelectorScalar, deningerSteinbergL]
  field_simp [deningerSteinbergSelectorDenominator_ne_zero m]
  unfold deningerSteinbergSelectorDenominator
  ring

theorem deningerSteinbergSelectorScalar_B (m : DeningerSteinbergDepth) :
    deningerSteinbergSelectorScalar m (deningerSteinbergB m) = 1 := by
  rw [deningerSteinbergSelectorScalar, deningerSteinbergL]
  field_simp [deningerSteinbergSelectorDenominator_ne_zero m]
  unfold deningerSteinbergSelectorDenominator
  ring

theorem deningerSteinbergSelectorScalar_cubic
    (m : DeningerSteinbergDepth) (t : ℂ) :
    deningerSteinbergSelectorScalar m t =
      (deningerSteinbergSelectorDenominator m)⁻¹ *
        (2 * t ^ 3 - (3 * deningerSteinbergL m) * t ^ 2 +
          (deningerSteinbergL m) ^ 2 * t) := by
  rw [deningerSteinbergSelectorScalar]
  field_simp [deningerSteinbergSelectorDenominator_ne_zero m]
  ring

theorem deningerKummerLogWeight_positiveRational
    (q : ℚ) (hq : 0 < q) :
    ccmRationalAdelicKummerLogWeight
        (deningerScalingOfPositiveRational q hq) =
      (Real.log (q : ℝ) : ℂ) := by
  rw [ccmRationalAdelicKummerLogWeight]
  simp only [deningerScalingOfPositiveRational_val]
  rw [abs_of_pos]
  exact_mod_cast hq

@[simp] theorem deningerSteinbergKummerWeight_X
    (m : DeningerSteinbergDepth) :
    ccmRationalAdelicKummerLogWeight (deningerSteinbergXScaling m) =
      deningerSteinbergA m := by
  exact deningerKummerLogWeight_positiveRational _ _

@[simp] theorem deningerSteinbergKummerWeight_Y
    (m : DeningerSteinbergDepth) :
    ccmRationalAdelicKummerLogWeight (deningerSteinbergYScaling m) =
      deningerSteinbergB m := by
  exact deningerKummerLogWeight_positiveRational _ _

def deningerSteinbergSelectorCoefficientMap
    (m : DeningerSteinbergDepth) :
    (CCMRationalAdelicScaling →₀ ℂ) →ₗ[ℂ]
      (CCMRationalAdelicScaling →₀ ℂ) :=
  Finsupp.lsum ℂ fun k =>
    deningerSteinbergSelectorScalar m
      (ccmRationalAdelicKummerLogWeight k) • Finsupp.lsingle k

/-- Cubic normal selector, defined spectrally on the actual rational-adelic group algebra. -/
def deningerSteinbergSelector (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing →ₗ[ℂ]
      RouteRMultiplierKOne.KummerGroupRing :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap.comp
    (deningerSteinbergSelectorCoefficientMap m |>.comp
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)

@[simp] theorem deningerSteinbergSelector_single
    (m : DeningerSteinbergDepth) (k : CCMRationalAdelicScaling) (c : ℂ) :
    deningerSteinbergSelector m (MonoidAlgebra.single k c) =
      MonoidAlgebra.single k
        (deningerSteinbergSelectorScalar m
          (ccmRationalAdelicKummerLogWeight k) * c) := by
  apply (MonoidAlgebra.coeffLinearEquiv ℂ).injective
  simp [deningerSteinbergSelector, deningerSteinbergSelectorCoefficientMap,
    smul_eq_mul]

@[simp] theorem deningerSteinbergSelector_basis
    (m : DeningerSteinbergDepth) (k : CCMRationalAdelicScaling) :
    deningerSteinbergSelector m (deningerSteinbergBasis k) =
      deningerSteinbergSelectorScalar m
          (ccmRationalAdelicKummerLogWeight k) •
        deningerSteinbergBasis k := by
  simp [deningerSteinbergBasis, MonoidAlgebra.of_apply, smul_eq_mul]

/-- Selector is exactly the normalized cubic polynomial in the existing Kummer derivation. -/
theorem deningerSteinbergSelector_eq_cubic
    (m : DeningerSteinbergDepth)
    (F : RouteRMultiplierKOne.KummerGroupRing) :
    deningerSteinbergSelector m F =
      (deningerSteinbergSelectorDenominator m)⁻¹ •
        (2 • RouteRMultiplierKOne.kummerGroupRingDerivation
              (RouteRMultiplierKOne.kummerGroupRingDerivation
                (RouteRMultiplierKOne.kummerGroupRingDerivation F)) -
          (3 * deningerSteinbergL m) •
            RouteRMultiplierKOne.kummerGroupRingDerivation
              (RouteRMultiplierKOne.kummerGroupRingDerivation F) +
          (deningerSteinbergL m) ^ 2 •
            RouteRMultiplierKOne.kummerGroupRingDerivation F) := by
  induction F using MonoidAlgebra.induction_on with
  | hM k =>
      change deningerSteinbergSelector m (deningerSteinbergBasis k) = _
      let w := ccmRationalAdelicKummerLogWeight k
      have hN1 : RouteRMultiplierKOne.kummerGroupRingDerivation
          (deningerSteinbergBasis k) = w • deningerSteinbergBasis k := by
        exact RouteRMultiplierKOne.kummerGroupRingDerivation_of k
      have hN2 : RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.kummerGroupRingDerivation
            (deningerSteinbergBasis k)) = w ^ 2 • deningerSteinbergBasis k := by
        rw [hN1, map_smul, hN1]
        module
      have hN3 : RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.kummerGroupRingDerivation
            (RouteRMultiplierKOne.kummerGroupRingDerivation
              (deningerSteinbergBasis k))) =
            w ^ 3 • deningerSteinbergBasis k := by
        rw [hN2, map_smul, hN1]
        module
      rw [deningerSteinbergSelector_basis]
      change deningerSteinbergSelectorScalar m w • deningerSteinbergBasis k =
        (deningerSteinbergSelectorDenominator m)⁻¹ •
          (2 • RouteRMultiplierKOne.kummerGroupRingDerivation
                (RouteRMultiplierKOne.kummerGroupRingDerivation
                  (RouteRMultiplierKOne.kummerGroupRingDerivation
                    (deningerSteinbergBasis k))) -
            (3 * deningerSteinbergL m) •
              RouteRMultiplierKOne.kummerGroupRingDerivation
                (RouteRMultiplierKOne.kummerGroupRingDerivation
                  (deningerSteinbergBasis k)) +
            deningerSteinbergL m ^ 2 •
              RouteRMultiplierKOne.kummerGroupRingDerivation
                (deningerSteinbergBasis k))
      rw [hN3, hN2, hN1]
      rw [deningerSteinbergSelectorScalar_cubic]
      module
  | hadd F H hF hH =>
      simp only [map_add, hF, hH]
      module
  | hsmul c F hF =>
      simp only [map_smul, hF]
      module

theorem deningerSteinbergCell_expand (m : DeningerSteinbergDepth) :
    deningerSteinbergCell m =
      deningerSteinbergBasis
          (deningerSteinbergXScaling m * deningerSteinbergYScaling m) -
        deningerSteinbergBasis (deningerSteinbergXScaling m) -
        deningerSteinbergBasis (deningerSteinbergYScaling m) + 1 := by
  rw [deningerSteinbergCell]
  rw [deningerSteinbergBasis_mul]
  ring

/-- Cubic selector sends the honest depth-dependent Steinberg cell to its oriented edge. -/
theorem deningerSteinbergSelector_cell (m : DeningerSteinbergDepth) :
    deningerSteinbergSelector m (deningerSteinbergCell m) =
      deningerSteinbergBasis (deningerSteinbergXScaling m) -
        deningerSteinbergBasis (deningerSteinbergYScaling m) := by
  rw [deningerSteinbergCell_expand]
  simp only [map_add, map_sub, deningerSteinbergSelector_basis,
    ccmRationalAdelicKummerLogWeight_mul,
    deningerSteinbergKummerWeight_X, deningerSteinbergKummerWeight_Y,
    deningerSteinbergSelectorScalar_A,
    deningerSteinbergSelectorScalar_B]
  have hone : ccmRationalAdelicKummerLogWeight
      (1 : CCMRationalAdelicScaling) = 0 := by
    simp [ccmRationalAdelicKummerLogWeight]
  rw [show (1 : RouteRMultiplierKOne.KummerGroupRing) =
      deningerSteinbergBasis 1 by rw [deningerSteinbergBasis_one]]
  rw [deningerSteinbergSelector_basis, hone,
    deningerSteinbergSelectorScalar_zero]
  rw [show deningerSteinbergSelectorScalar m
      (deningerSteinbergA m + deningerSteinbergB m) = 0 by
    simpa [deningerSteinbergL] using deningerSteinbergSelectorScalar_L m]
  module

def deningerSteinbergRatioScaling (m : DeningerSteinbergDepth) :
    CCMRationalAdelicScaling :=
  deningerScalingOfPositiveRational ((3 / 2 : ℚ) ^ (m : ℕ)) (by positivity)

theorem deningerSteinbergY_inv_mul_X_scaling (m : DeningerSteinbergDepth) :
    (deningerSteinbergYScaling m)⁻¹ * deningerSteinbergXScaling m =
      deningerSteinbergRatioScaling m := by
  apply ccmRationalAdelicScalingEquiv.injective
  apply Units.ext
  change (deningerSteinbergY m)⁻¹ * deningerSteinbergX m =
    (3 / 2 : ℚ) ^ (m : ℕ)
  rw [inv_mul_eq_div, deningerSteinbergX_div_Y]

def deningerSteinbergNormalEscape (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  deningerSteinbergBasis (deningerSteinbergYScaling m)⁻¹ *
    deningerSteinbergSelector m (deningerSteinbergCell m)

/-- Exact full-grade normal extraction on the actual rational-adelic group algebra. -/
theorem deningerSteinbergNormalEscape_eq (m : DeningerSteinbergDepth) :
    deningerSteinbergNormalEscape m =
      deningerSteinbergBasis (deningerSteinbergRatioScaling m) - 1 := by
  rw [deningerSteinbergNormalEscape, deningerSteinbergSelector_cell, mul_sub]
  rw [← deningerSteinbergBasis_mul, ← deningerSteinbergBasis_mul]
  rw [inv_mul_cancel (deningerSteinbergYScaling m)]
  rw [deningerSteinbergBasis_one]
  rw [deningerSteinbergY_inv_mul_X_scaling]

def deningerKummerAugmentationMonoidHom :
    CCMRationalAdelicScaling →* ℂ where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp

/-- Canonical augmentation of the actual rational-adelic group algebra. -/
def deningerKummerAugmentation :
    RouteRMultiplierKOne.KummerGroupRing →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ CCMRationalAdelicScaling
    deningerKummerAugmentationMonoidHom

@[simp] theorem deningerKummerAugmentation_basis
    (k : CCMRationalAdelicScaling) :
    deningerKummerAugmentation (deningerSteinbergBasis k) = 1 := by
  simp [deningerKummerAugmentation, deningerSteinbergBasis,
    deningerKummerAugmentationMonoidHom]

def deningerKummerAugmentationIdeal :
    Ideal RouteRMultiplierKOne.KummerGroupRing :=
  RingHom.ker deningerKummerAugmentation.toRingHom

theorem deningerSteinbergBasis_sub_one_mem_augmentationIdeal
    (k : CCMRationalAdelicScaling) :
    deningerSteinbergBasis k - 1 ∈ deningerKummerAugmentationIdeal := by
  change deningerKummerAugmentation (deningerSteinbergBasis k - 1) = 0
  simp

/-- Positive complementary rational pair indexing an honest Steinberg generator. -/
structure DeningerPositiveSteinbergPair where
  x : ℚ
  y : ℚ
  x_pos : 0 < x
  y_pos : 0 < y
  complementary : x + y = 1

def deningerPositiveSteinbergCell (p : DeningerPositiveSteinbergPair) :
    RouteRMultiplierKOne.KummerGroupRing :=
  (deningerSteinbergBasis (deningerScalingOfPositiveRational p.x p.x_pos) - 1) *
    (deningerSteinbergBasis (deningerScalingOfPositiveRational p.y p.y_pos) - 1)

/-- Honest Steinberg ideal inside the actual rational-adelic group algebra. -/
def deningerKummerSteinbergIdeal :
    Ideal RouteRMultiplierKOne.KummerGroupRing :=
  Ideal.span (Set.range deningerPositiveSteinbergCell)

def deningerSteinbergDepthPair (m : DeningerSteinbergDepth) :
    DeningerPositiveSteinbergPair where
  x := deningerSteinbergX m
  y := deningerSteinbergY m
  x_pos := deningerSteinbergX_pos m
  y_pos := deningerSteinbergY_pos m
  complementary := deningerSteinbergX_add_Y m

theorem deningerSteinbergCell_depthPair (m : DeningerSteinbergDepth) :
    deningerPositiveSteinbergCell (deningerSteinbergDepthPair m) =
      deningerSteinbergCell m := rfl

theorem deningerSteinbergCell_mem_steinbergIdeal
    (m : DeningerSteinbergDepth) :
    deningerSteinbergCell m ∈ deningerKummerSteinbergIdeal := by
  rw [← deningerSteinbergCell_depthPair m]
  exact Ideal.subset_span (Set.mem_range_self (deningerSteinbergDepthPair m))

theorem deningerPositiveSteinbergCell_mem_augmentationIdeal_sq
    (p : DeningerPositiveSteinbergPair) :
    deningerPositiveSteinbergCell p ∈ deningerKummerAugmentationIdeal ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul
    (deningerSteinbergBasis_sub_one_mem_augmentationIdeal _)
    (deningerSteinbergBasis_sub_one_mem_augmentationIdeal _)

theorem deningerKummerSteinbergIdeal_le_augmentationIdeal_sq :
    deningerKummerSteinbergIdeal ≤ deningerKummerAugmentationIdeal ^ 2 := by
  rw [deningerKummerSteinbergIdeal, Ideal.span_le]
  rintro _ ⟨p, rfl⟩
  exact deningerPositiveSteinbergCell_mem_augmentationIdeal_sq p

/-- Logarithmic Kummer regulator: augmentation after the exact Kummer derivation. -/
def deningerKummerRegulator :
    RouteRMultiplierKOne.KummerGroupRing →ₗ[ℂ] ℂ :=
  deningerKummerAugmentation.toLinearMap.comp
    RouteRMultiplierKOne.kummerGroupRingDerivation

@[simp] theorem deningerKummerRegulator_basis
    (k : CCMRationalAdelicScaling) :
    deningerKummerRegulator (deningerSteinbergBasis k) =
      ccmRationalAdelicKummerLogWeight k := by
  change deningerKummerAugmentation
      (RouteRMultiplierKOne.kummerGroupRingDerivation
        (deningerSteinbergBasis k)) = _
  have hN : RouteRMultiplierKOne.kummerGroupRingDerivation
      (deningerSteinbergBasis k) =
        ccmRationalAdelicKummerLogWeight k • deningerSteinbergBasis k :=
    RouteRMultiplierKOne.kummerGroupRingDerivation_of k
  rw [hN, map_smul, deningerKummerAugmentation_basis]
  simp

@[simp] theorem deningerKummerRegulator_one :
    deningerKummerRegulator 1 = 0 := by
  have h := deningerKummerRegulator_basis (1 : CCMRationalAdelicScaling)
  simpa [deningerSteinbergBasis_one,
    ccmRationalAdelicKummerLogWeight] using h

theorem deningerKummerRegulator_mul
    (F H : RouteRMultiplierKOne.KummerGroupRing) :
    deningerKummerRegulator (F * H) =
      deningerKummerAugmentation F * deningerKummerRegulator H +
        deningerKummerRegulator F * deningerKummerAugmentation H := by
  change deningerKummerAugmentation
      (RouteRMultiplierKOne.kummerGroupRingDerivation (F * H)) =
    deningerKummerAugmentation F * deningerKummerAugmentation
        (RouteRMultiplierKOne.kummerGroupRingDerivation H) +
      deningerKummerAugmentation
          (RouteRMultiplierKOne.kummerGroupRingDerivation F) *
        deningerKummerAugmentation H
  rw [RouteRMultiplierKOne.kummerGroupRingDerivation_mul, map_add,
    map_mul, map_mul]
  ring

theorem deningerKummerRegulator_eq_zero_of_mem_augmentationIdeal_sq
    {F : RouteRMultiplierKOne.KummerGroupRing}
    (hF : F ∈ deningerKummerAugmentationIdeal ^ 2) :
    deningerKummerRegulator F = 0 := by
  rw [pow_two] at hF
  refine Submodule.mul_induction_on hF ?_ ?_
  · intro F hFI H hHI
    rw [deningerKummerRegulator_mul]
    change deningerKummerAugmentation F = 0 at hFI
    change deningerKummerAugmentation H = 0 at hHI
    simp [hFI, hHI]
  · intro F H hF hH
    simp [map_add, hF, hH]

theorem deningerKummerRegulator_eq_zero_of_mem_steinbergIdeal
    {F : RouteRMultiplierKOne.KummerGroupRing}
    (hF : F ∈ deningerKummerSteinbergIdeal) :
    deningerKummerRegulator F = 0 :=
  deningerKummerRegulator_eq_zero_of_mem_augmentationIdeal_sq
    (deningerKummerSteinbergIdeal_le_augmentationIdeal_sq hF)

theorem deningerSteinbergRatioScaling_weight
    (m : DeningerSteinbergDepth) :
    ccmRationalAdelicKummerLogWeight (deningerSteinbergRatioScaling m) =
      (m : ℂ) * (Real.log (3 / 2 : ℝ) : ℂ) := by
  rw [deningerSteinbergRatioScaling,
    deningerKummerLogWeight_positiveRational]
  push_cast
  rw [Real.log_pow]
  push_cast
  rfl

/-- Kummer regulator detects the full depth of the normal escape. -/
theorem deningerKummerRegulator_normalEscape
    (m : DeningerSteinbergDepth) :
    deningerKummerRegulator (deningerSteinbergNormalEscape m) =
      (m : ℂ) * (Real.log (3 / 2 : ℝ) : ℂ) := by
  rw [deningerSteinbergNormalEscape_eq, map_sub,
    deningerKummerRegulator_basis, deningerSteinbergRatioScaling_weight]
  simp

theorem deningerKummerRegulator_normalEscape_ne_zero
    (m : DeningerSteinbergDepth) :
    deningerKummerRegulator (deningerSteinbergNormalEscape m) ≠ 0 := by
  rw [deningerKummerRegulator_normalEscape]
  exact mul_ne_zero (by exact_mod_cast (show (m : ℕ) ≠ 0 by omega))
    (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne')

/-- Selector lowers augmentation order: its extracted edge is not in the square. -/
theorem deningerSteinbergNormalEscape_not_mem_augmentationIdeal_sq
    (m : DeningerSteinbergDepth) :
    deningerSteinbergNormalEscape m ∉ deningerKummerAugmentationIdeal ^ 2 := by
  intro h
  exact deningerKummerRegulator_normalEscape_ne_zero m
    (deningerKummerRegulator_eq_zero_of_mem_augmentationIdeal_sq h)

/-- In particular, the normal escape is not an ordinary Steinberg/Milnor boundary. -/
theorem deningerSteinbergNormalEscape_not_mem_steinbergIdeal
    (m : DeningerSteinbergDepth) :
    deningerSteinbergNormalEscape m ∉ deningerKummerSteinbergIdeal := by
  intro h
  exact deningerKummerRegulator_normalEscape_ne_zero m
    (deningerKummerRegulator_eq_zero_of_mem_steinbergIdeal h)

def deningerSteinbergBaseScaling : CCMRationalAdelicScaling :=
  deningerScalingOfPositiveRational (3 / 2) (by norm_num)

theorem deningerSteinbergBaseScaling_pow (m : DeningerSteinbergDepth) :
    deningerSteinbergBaseScaling ^ (m : ℕ) = deningerSteinbergRatioScaling m := by
  apply ccmRationalAdelicScalingEquiv.injective
  apply Units.ext
  rfl

/-- Canonical counteroriented Tate interval primitive of the Steinberg normal escape. -/
def deningerSteinbergTatePrimitive (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  deningerSteinbergBasis (deningerSteinbergRatioScaling m) *
    GaloisForLFunctions.HTGeometry.tateIntervalCharacter
      (deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹) (m : ℕ)

theorem deningerSteinbergTateTop_cancel (m : DeningerSteinbergDepth) :
    deningerSteinbergBasis (deningerSteinbergRatioScaling m) *
        deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹ ^ (m : ℕ) = 1 := by
  rw [← deningerSteinbergBasis_pow, ← deningerSteinbergBasis_mul,
    ← deningerSteinbergBaseScaling_pow]
  simp

/-- Strict Steinberg-normal/Tate boundary square on the actual group algebra. -/
theorem deningerSteinbergTateBoundary (m : DeningerSteinbergDepth) :
    (1 - deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹) *
        deningerSteinbergTatePrimitive m =
      deningerSteinbergNormalEscape m := by
  rw [deningerSteinbergTatePrimitive, deningerSteinbergNormalEscape_eq]
  calc
    (1 - deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹) *
          (deningerSteinbergBasis (deningerSteinbergRatioScaling m) *
            GaloisForLFunctions.HTGeometry.tateIntervalCharacter
              (deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹) (m : ℕ)) =
        deningerSteinbergBasis (deningerSteinbergRatioScaling m) *
          ((1 - deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹) *
            GaloisForLFunctions.HTGeometry.tateIntervalCharacter
              (deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹) (m : ℕ)) := by
          ring
    _ = deningerSteinbergBasis (deningerSteinbergRatioScaling m) *
          (1 - deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹ ^ (m : ℕ)) := by
          rw [GaloisForLFunctions.HTGeometry.one_sub_mul_tateIntervalCharacter]
    _ = deningerSteinbergBasis (deningerSteinbergRatioScaling m) - 1 := by
          rw [mul_sub, mul_one, deningerSteinbergTateTop_cancel]

/-- Full strict algebraic source square: selector extraction equals Tate boundary. -/
theorem deningerSteinbergSelector_eq_tateBoundary (m : DeningerSteinbergDepth) :
    deningerSteinbergBasis (deningerSteinbergYScaling m)⁻¹ *
        deningerSteinbergSelector m (deningerSteinbergCell m) =
      (1 - deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹) *
        deningerSteinbergTatePrimitive m := by
  exact (deningerSteinbergTateBoundary m).symm

def deningerKummerCharacterMonoidHom (δ : ℂ) :
    CCMRationalAdelicScaling →* ℂ where
  toFun k :=
    (((|(((k.val : CCMRationalUnit) : ℚ) : ℝ)| : ℝ) : ℂ) ^ δ)
  map_one' := by simp
  map_mul' k l := by
    rw [ccmRationalAdelicScaling_mul_val]
    push_cast
    rw [abs_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _)]

/-- Multiplicative positive-real character on the actual rational-adelic group algebra. -/
def deningerKummerCharacter (δ : ℂ) :
    RouteRMultiplierKOne.KummerGroupRing →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ CCMRationalAdelicScaling
    (deningerKummerCharacterMonoidHom δ)

@[simp] theorem deningerKummerCharacter_basis
    (δ : ℂ) (k : CCMRationalAdelicScaling) :
    deningerKummerCharacter δ (deningerSteinbergBasis k) =
      (((|(((k.val : CCMRationalUnit) : ℚ) : ℝ)| : ℝ) : ℂ) ^ δ) := by
  simp [deningerKummerCharacter, deningerSteinbergBasis,
    deningerKummerCharacterMonoidHom]

theorem deningerKummerCharacter_baseScaling (δ : ℂ) :
    deningerKummerCharacter δ
        (deningerSteinbergBasis deningerSteinbergBaseScaling) =
      ((3 / 2 : ℂ) ^ δ) := by
  rw [deningerKummerCharacter_basis]
  norm_num [deningerSteinbergBaseScaling,
    deningerScalingOfPositiveRational]

/-- Character of the conormal escape is the full-depth reflection anomaly. -/
theorem deningerKummerCharacter_normalEscape
    (m : DeningerSteinbergDepth) (δ : ℂ) :
    deningerKummerCharacter δ (deningerSteinbergNormalEscape m) =
      (3 / 2 : ℂ) ^ ((m : ℂ) * δ) - 1 := by
  rw [deningerSteinbergNormalEscape_eq, map_sub, map_one]
  rw [← deningerSteinbergBaseScaling_pow m,
    deningerSteinbergBasis_pow, map_pow,
    deningerKummerCharacter_baseScaling]
  rw [← Complex.cpow_nat_mul]

/-- Exact factorization of the reflected successor normalizer through the conormal character. -/
theorem deningerSteinbergReflectionFactorization
    (m : DeningerSteinbergDepth) (s : ℂ) :
    (3 / 2 : ℂ) ^ ((m : ℂ) * s) -
        (3 / 2 : ℂ) ^ ((m : ℂ) * (1 - starRingEnd ℂ s)) =
      (3 / 2 : ℂ) ^ ((m : ℂ) * (1 - starRingEnd ℂ s)) *
        deningerKummerCharacter
          (s - (1 - starRingEnd ℂ s)) (deningerSteinbergNormalEscape m) := by
  rw [deningerKummerCharacter_normalEscape]
  have hbase : (3 / 2 : ℂ) ≠ 0 := by norm_num
  rw [mul_sub]
  rw [show (m : ℂ) * s =
      (m : ℂ) * (1 - starRingEnd ℂ s) +
        (m : ℂ) * (s - (1 - starRingEnd ℂ s)) by ring]
  rw [Complex.cpow_add _ _ hbase]
  have href : (3 / 2 : ℂ) ^ ((m : ℂ) * (1 - starRingEnd ℂ s)) =
      (3 / 2 : ℂ) ^ ((m : ℂ) * 1 - (m : ℂ) * starRingEnd ℂ s) := by
    congr 1
    ring
  rw [href]
  ring

def deningerScalingAbsoluteValue (k : CCMRationalAdelicScaling) : ℝ :=
  |(((k.val : CCMRationalUnit) : ℚ) : ℝ)|

theorem deningerScalingAbsoluteValue_pos (k : CCMRationalAdelicScaling) :
    0 < deningerScalingAbsoluteValue k := by
  rw [deningerScalingAbsoluteValue, abs_pos]
  exact_mod_cast Units.ne_zero k.val

@[simp] theorem deningerScalingAbsoluteValue_one :
    deningerScalingAbsoluteValue 1 = 1 := by
  simp [deningerScalingAbsoluteValue]

theorem deningerScalingAbsoluteValue_mul
    (k l : CCMRationalAdelicScaling) :
    deningerScalingAbsoluteValue (k * l) =
      deningerScalingAbsoluteValue k * deningerScalingAbsoluteValue l := by
  rw [deningerScalingAbsoluteValue, deningerScalingAbsoluteValue,
    deningerScalingAbsoluteValue, ccmRationalAdelicScaling_mul_val]
  push_cast
  exact abs_mul _ _

/-- Canonical half-density translation attached to a rational-adelic scaling. -/
def deningerHalfDensityScalingCLM (k : CCMRationalAdelicScaling) :
    MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  ((((deningerScalingAbsoluteValue k) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) •
    (MellinL2.additiveTranslationUnitary
      ((Real.log (deningerScalingAbsoluteValue k)) *
        MellinL2.spectralNormalization)).toLinearIsometry.toContinuousLinearMap

@[simp] theorem deningerHalfDensityScalingCLM_apply
    (k : CCMRationalAdelicScaling) (f : MobiusThetaSourceL2) :
    deningerHalfDensityScalingCLM k f =
      ((((deningerScalingAbsoluteValue k) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) •
        MellinL2.additiveTranslationUnitary
          ((Real.log (deningerScalingAbsoluteValue k)) *
            MellinL2.spectralNormalization) f := rfl

theorem deningerHalfDensityScalingCLM_one :
    deningerHalfDensityScalingCLM 1 =
      ContinuousLinearMap.id ℂ MobiusThetaSourceL2 := by
  ext f
  simp [deningerHalfDensityScalingCLM_apply,
    additiveTranslationUnitary_zero_apply]

theorem deningerHalfDensityScalingCLM_mul
    (k l : CCMRationalAdelicScaling) :
    deningerHalfDensityScalingCLM (k * l) =
      deningerHalfDensityScalingCLM k * deningerHalfDensityScalingCLM l := by
  ext f
  rw [mul_apply_eq_comp]
  simp only [deningerHalfDensityScalingCLM_apply, map_smul, smul_smul]
  rw [additiveTranslationUnitary_add_apply]
  rw [deningerScalingAbsoluteValue_mul,
    Real.mul_rpow (le_of_lt (deningerScalingAbsoluteValue_pos k))
      (le_of_lt (deningerScalingAbsoluteValue_pos l)),
    Real.log_mul (ne_of_gt (deningerScalingAbsoluteValue_pos k))
      (ne_of_gt (deningerScalingAbsoluteValue_pos l))]
  have hamp :
      (((deningerScalingAbsoluteValue k ^ ((1 : ℝ) / 2) *
          deningerScalingAbsoluteValue l ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) =
        ((deningerScalingAbsoluteValue l ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
          ((deningerScalingAbsoluteValue k ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  have htime :
      (Real.log (deningerScalingAbsoluteValue k) +
          Real.log (deningerScalingAbsoluteValue l)) *
          MellinL2.spectralNormalization =
        Real.log (deningerScalingAbsoluteValue k) *
            MellinL2.spectralNormalization +
          Real.log (deningerScalingAbsoluteValue l) *
            MellinL2.spectralNormalization := by ring
  rw [hamp, htime]

def deningerHalfDensityScalingMonoidHom :
    CCMRationalAdelicScaling →*
      (MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2) where
  toFun := deningerHalfDensityScalingCLM
  map_one' := deningerHalfDensityScalingCLM_one
  map_mul' := deningerHalfDensityScalingCLM_mul

/-- Multiplicative half-density representation of the full rational-adelic group algebra. -/
def deningerHalfDensityRepresentation :
    RouteRMultiplierKOne.KummerGroupRing →ₐ[ℂ]
      (MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2) :=
  MonoidAlgebra.lift ℂ
    (MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2)
    CCMRationalAdelicScaling deningerHalfDensityScalingMonoidHom

@[simp] theorem deningerHalfDensityRepresentation_basis
    (k : CCMRationalAdelicScaling) :
    deningerHalfDensityRepresentation (deningerSteinbergBasis k) =
      deningerHalfDensityScalingCLM k := by
  simp [deningerHalfDensityRepresentation, deningerSteinbergBasis,
    deningerHalfDensityScalingMonoidHom]

def deningerSteinbergPhysicalEscapeCLM (m : ℕ) :
    MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  mobiusThetaSuccessorBlowupCLM ⟨2, by omega⟩ m -
    ContinuousLinearMap.id ℂ MobiusThetaSourceL2

theorem deningerScalingAbsoluteValue_ratio
    (m : DeningerSteinbergDepth) :
    deningerScalingAbsoluteValue (deningerSteinbergRatioScaling m) =
      ((3 : ℝ) / 2) ^ (m : ℕ) := by
  rw [deningerScalingAbsoluteValue, deningerSteinbergRatioScaling]
  simp only [deningerScalingOfPositiveRational_val]
  push_cast
  rw [abs_of_pos]
  positivity

theorem deningerHalfDensityScalingCLM_ratio
    (m : DeningerSteinbergDepth) :
    deningerHalfDensityScalingCLM (deningerSteinbergRatioScaling m) =
      mobiusThetaSuccessorBlowupCLM ⟨2, by omega⟩ m := by
  ext f
  simp only [deningerHalfDensityScalingCLM_apply,
    mobiusThetaSuccessorBlowupCLM_apply]
  rw [deningerScalingAbsoluteValue_ratio, mobiusThetaSuccessorBlowup,
    mobiusSuccessor_two]
  have hamp : ((((3 : ℝ) / 2) ^ (m : ℕ)) ^ ((1 : ℝ) / 2)) =
      ((3 : ℝ) / 2) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    congr 1
    ring
  have htime : Real.log (((3 : ℝ) / 2) ^ (m : ℕ)) *
        MellinL2.spectralNormalization =
      ((m : ℝ) * Real.log ((3 : ℝ) / 2)) *
        MellinL2.spectralNormalization := by
    rw [Real.log_pow]
  rw [hamp, htime]
  norm_num

/-- Half-density representation sends the algebraic escape to the concrete successor minus id. -/
theorem deningerHalfDensityRepresentation_normalEscape
    (m : DeningerSteinbergDepth) :
    deningerHalfDensityRepresentation (deningerSteinbergNormalEscape m) =
      deningerSteinbergPhysicalEscapeCLM m := by
  rw [deningerSteinbergNormalEscape_eq, map_sub, map_one,
    deningerHalfDensityRepresentation_basis,
    deningerHalfDensityScalingCLM_ratio]
  rfl

/-- Half-density image of the strict Tate square is the physical Euler boundary. -/
theorem deningerHalfDensityRepresentation_tateBoundary
    (m : DeningerSteinbergDepth) :
    (ContinuousLinearMap.id ℂ MobiusThetaSourceL2 -
        deningerHalfDensityRepresentation
          (deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹)) *
      deningerHalfDensityRepresentation (deningerSteinbergTatePrimitive m) =
        deningerSteinbergPhysicalEscapeCLM m := by
  change (1 - deningerHalfDensityRepresentation
          (deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹)) *
      deningerHalfDensityRepresentation (deningerSteinbergTatePrimitive m) =
        deningerSteinbergPhysicalEscapeCLM m
  have h := congrArg deningerHalfDensityRepresentation
    (deningerSteinbergTateBoundary m)
  simpa only [map_mul, map_sub, map_one,
    deningerHalfDensityRepresentation_normalEscape] using h

@[simp] theorem deningerSteinbergPhysicalEscapeCLM_apply
    (m : ℕ) (f : MobiusThetaSourceL2) :
    deningerSteinbergPhysicalEscapeCLM m f =
      mobiusThetaTwoThreeSuccessorBlowup m f - f := by
  rfl

def deningerSteinbergCompleteSource (m : MobiusHonestDepth) :
    MobiusThetaSourceL2 :=
  mobiusThetaPrimeNormalResidual 2 m + xiThetaSourceL2

/-- Exact action of the extracted edge on the complete physical Möbius source. -/
theorem deningerSteinbergPhysicalEscape_completeSource
    (m : MobiusHonestDepth) :
    deningerSteinbergPhysicalEscapeCLM m
        (deningerSteinbergCompleteSource m) =
      mobiusThetaPrimeNormalResidual 3 m - deningerSteinbergCompleteSource m := by
  rw [deningerSteinbergPhysicalEscapeCLM_apply,
    deningerSteinbergCompleteSource,
    mobiusTheta_two_three_successor_transport]

/-- Strict Tate/half-density source boundary on the complete physical Möbius tail. -/
theorem deningerSteinbergTateBoundary_completeSource
    (m : MobiusHonestDepth) :
    ((ContinuousLinearMap.id ℂ MobiusThetaSourceL2 -
          deningerHalfDensityRepresentation
            (deningerSteinbergBasis deningerSteinbergBaseScaling⁻¹)) *
        deningerHalfDensityRepresentation
          (deningerSteinbergTatePrimitive ⟨m, by omega⟩))
        (deningerSteinbergCompleteSource m) =
      mobiusThetaPrimeNormalResidual 3 m - deningerSteinbergCompleteSource m := by
  rw [deningerHalfDensityRepresentation_tateBoundary]
  exact deningerSteinbergPhysicalEscape_completeSource m

/-- Genuine multiplier K1 direction carried by the Steinberg normal escape. -/
def deningerSteinbergNormalKOneCycle
    (m : DeningerSteinbergDepth) : RouteRMultiplierKOne.MC1 :=
  let u := RouteRMultiplierKOne.dilUnit (deningerSteinbergRatioScaling m)
  PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
    Fin.cases (↑u⁻¹ : RouteRMultiplierKOne.Mult)
      (fun _ => (u : RouteRMultiplierKOne.Mult)) i)

theorem deningerSteinbergNormalKOneCycle_boundary
    (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.mBoundaryOne
      (deningerSteinbergNormalKOneCycle m) = 0 := by
  rw [deningerSteinbergNormalKOneCycle,
    RouteRMultiplierKOne.mBoundaryOne_tprod]
  simp

/-- Genuine Kummer cyclic cocycle reads the full normal depth. -/
theorem deningerSteinbergNormalKOneCycle_kummerValue
    (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle
        (deningerSteinbergNormalKOneCycle m) =
      (m : ℂ) * (Real.log (3 / 2 : ℝ) : ℂ) := by
  rw [deningerSteinbergNormalKOneCycle,
    RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle_tprod]
  change RouteRMultiplierKOne.kummerGroupRingTrace
      (RouteRMultiplierKOne.multiplierToKummerGroupRing
          (↑((RouteRMultiplierKOne.dilUnit
            (deningerSteinbergRatioScaling m))⁻¹) : RouteRMultiplierKOne.Mult) *
        RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.multiplierToKummerGroupRing
            ((RouteRMultiplierKOne.dilUnit
              (deningerSteinbergRatioScaling m) : RouteRMultiplierKOne.Multˣ) :
                RouteRMultiplierKOne.Mult))) = _
  rw [RouteRMultiplierKOne.multiplierToKummerGroupRing_dilUnit_inv,
    RouteRMultiplierKOne.multiplierToKummerGroupRing_dilUnit,
    RouteRMultiplierKOne.kummerGroupRingPair_inv_of,
    deningerSteinbergRatioScaling_weight]

/-- The K1 direction cannot be a degree-two Hochschild boundary. -/
theorem deningerSteinbergNormalKOneCycle_not_mem_boundaryTwo_range
    (m : DeningerSteinbergDepth) :
    deningerSteinbergNormalKOneCycle m ∉
      LinearMap.range RouteRMultiplierKOne.multiplierHochschildBoundaryTwo := by
  rintro ⟨z, hz⟩
  have hzero : RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle
      (RouteRMultiplierKOne.multiplierHochschildBoundaryTwo z) = 0 := by
    have hcomp := congrArg
      (fun L : RouteRMultiplierKOne.MultiplierDegreeTwoCyclicSource →ₗ[ℂ] ℂ => L z)
      RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle_comp_boundaryTwo
    simpa using hcomp
  rw [hz, deningerSteinbergNormalKOneCycle_kummerValue] at hzero
  apply deningerKummerRegulator_normalEscape_ne_zero m
  rw [deningerKummerRegulator_normalEscape]
  exact hzero

def deningerSteinbergPhysicalCofinalTarget (n : ℕ) : MobiusThetaSourceL2 :=
  deningerSteinbergPhysicalEscapeCLM (n + 3)
    (mobiusThetaTwoThreeCofinalSource n)

theorem deningerSteinbergPhysicalCofinalTarget_eq (n : ℕ) :
    deningerSteinbergPhysicalCofinalTarget n =
      mobiusThetaTwoThreeCofinalTarget n - mobiusThetaTwoThreeCofinalSource n := by
  rfl

/-- The extracted physical boundary converges to the nonzero theta defect. -/
theorem tendsto_deningerSteinbergPhysicalCofinalTarget :
    Filter.Tendsto deningerSteinbergPhysicalCofinalTarget Filter.atTop
      (nhds (-xiThetaSourceL2)) := by
  have h := tendsto_mobiusThetaTwoThreeCofinalTarget.sub
    tendsto_mobiusThetaTwoThreeCofinalSource_zero
  have h' : Filter.Tendsto
      (fun n => mobiusThetaTwoThreeCofinalTarget n -
        mobiusThetaTwoThreeCofinalSource n) Filter.atTop
      (nhds (-xiThetaSourceL2)) := by simpa using h
  exact h'.congr' (Filter.Eventually.of_forall fun n =>
    (deningerSteinbergPhysicalCofinalTarget_eq n).symm)

/-- Reverse-triangle lower bound for the physical normal escape. -/
theorem norm_deningerSteinbergPhysicalEscapeCLM_lower
    (m : ℕ) :
    ((3 : ℝ) / 2) ^ ((m : ℝ) / 2) - 1 ≤
      ‖deningerSteinbergPhysicalEscapeCLM m‖ := by
  have h := norm_sub_norm_le
    (mobiusThetaSuccessorBlowupCLM ⟨2, by omega⟩ m)
    (ContinuousLinearMap.id ℂ MobiusThetaSourceL2)
  rw [norm_mobiusThetaSuccessorBlowupCLM,
    mobiusSuccessor_two, ContinuousLinearMap.norm_id] at h
  exact h

/-- Physical images of the conormal escapes are exponentially singular. -/
theorem tendsto_norm_deningerSteinbergPhysicalEscapeCLM_atTop :
    Filter.Tendsto
      (fun n : ℕ => ‖deningerSteinbergPhysicalEscapeCLM (n + 3)‖)
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  have hT := tendsto_norm_mobiusThetaSuccessorBlowupCLM_atTop
    (⟨2, by omega⟩ : MobiusPositiveIndex)
  rw [Filter.tendsto_atTop] at hT
  filter_upwards [hT (b + 1)] with n hn
  have hlower := norm_deningerSteinbergPhysicalEscapeCLM_lower (n + 3)
  rw [norm_mobiusThetaSuccessorBlowupCLM, mobiusSuccessor_two] at hn
  linarith

end

end RHTower
