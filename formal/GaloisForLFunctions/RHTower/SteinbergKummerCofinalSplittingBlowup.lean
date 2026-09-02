import GaloisForLFunctions.RHTower.DeningerSteinbergKummerSuccessorNormalTransgression

/-!
# Steinberg--Kummer cofinal splitting blowup

Exact second-jet augmentation certificate in the actual rational-adelic Kummer group ring. Any
three-jet Bezout splitting of the Steinberg cell has a second coefficient whose coefficient
`ell¹` norm is bounded below by the reciprocal logarithmic product.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

def deningerKummerCoefficientL1
    (F : RouteRMultiplierKOne.KummerGroupRing) : ℝ :=
  let c := MonoidAlgebra.coeffLinearEquiv ℂ F
  ∑ k ∈ c.support, ‖c k‖

theorem norm_deningerKummerAugmentation_le_coefficientL1
    (F : RouteRMultiplierKOne.KummerGroupRing) :
    ‖deningerKummerAugmentation F‖ ≤ deningerKummerCoefficientL1 F := by
  rw [deningerKummerAugmentation]
  let c := MonoidAlgebra.coeffLinearEquiv ℂ F
  rw [MonoidAlgebra.lift_apply]
  simp only [deningerKummerAugmentationMonoidHom, MonoidHom.coe_mk,
    OneHom.coe_mk, smul_eq_mul, mul_one]
  change ‖c.sum fun _ z => z‖ ≤ _
  rw [deningerKummerCoefficientL1]
  exact norm_sum_le _ _

private theorem deningerKummerAugmentation_secondDerivation_basis
    (k : GaloisForLFunctions.RHTower.CCMRationalAdelicScaling) :
    deningerKummerAugmentation
        (RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.kummerGroupRingDerivation
            (deningerSteinbergBasis k))) =
      ccmRationalAdelicKummerLogWeight k ^ 2 := by
  have hD : RouteRMultiplierKOne.kummerGroupRingDerivation
      (deningerSteinbergBasis k) =
        ccmRationalAdelicKummerLogWeight k • deningerSteinbergBasis k :=
    RouteRMultiplierKOne.kummerGroupRingDerivation_of k
  rw [hD, map_smul, hD, map_smul, map_smul,
    deningerKummerAugmentation_basis]
  simp [smul_eq_mul, pow_two]

theorem deningerKummerAugmentation_secondDerivation_cell
    (m : DeningerSteinbergDepth) :
    deningerKummerAugmentation
        (RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.kummerGroupRingDerivation
            (deningerSteinbergCell m))) =
      2 * deningerSteinbergA m * deningerSteinbergB m := by
  rw [deningerSteinbergCell_expand]
  simp only [map_add, map_sub, deningerKummerAugmentation_secondDerivation_basis,
    ccmRationalAdelicKummerLogWeight_mul, deningerSteinbergKummerWeight_X,
    deningerSteinbergKummerWeight_Y]
  have hone : ccmRationalAdelicKummerLogWeight
      (1 : GaloisForLFunctions.RHTower.CCMRationalAdelicScaling) = 0 := by
    simp [ccmRationalAdelicKummerLogWeight]
  rw [show (1 : RouteRMultiplierKOne.KummerGroupRing) =
      deningerSteinbergBasis 1 by rw [deningerSteinbergBasis_one],
    deningerKummerAugmentation_secondDerivation_basis, hone]
  ring

/-- SKSB-1: exact reciprocal lower bound for the second coefficient in every three-jet splitting. -/
theorem deningerSteinbergSecondJet_coefficientL1_lower_bound
    (m : DeningerSteinbergDepth)
    (u₀ u₁ u₂ : RouteRMultiplierKOne.KummerGroupRing)
    (hcomb :
      u₀ * deningerSteinbergCell m +
        u₁ * RouteRMultiplierKOne.kummerGroupRingDerivation
          (deningerSteinbergCell m) +
        u₂ * RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.kummerGroupRingDerivation
            (deningerSteinbergCell m)) = 1) :
    (2 * ‖deningerSteinbergA m * deningerSteinbergB m‖)⁻¹ ≤
      deningerKummerCoefficientL1 u₂ := by
  have hcell : deningerKummerAugmentation (deningerSteinbergCell m) = 0 := by
    simp [deningerSteinbergCell]
  have hfirst : deningerKummerAugmentation
      (RouteRMultiplierKOne.kummerGroupRingDerivation
        (deningerSteinbergCell m)) = 0 := by
    change deningerKummerRegulator (deningerSteinbergCell m) = 0
    exact deningerKummerRegulator_eq_zero_of_mem_steinbergIdeal
      (deningerSteinbergCell_mem_steinbergIdeal m)
  have hsecond := deningerKummerAugmentation_secondDerivation_cell m
  have haug := congrArg deningerKummerAugmentation hcomb
  simp only [map_add, map_mul, map_one, hcell, hfirst, hsecond,
    mul_zero, add_zero] at haug
  have haug' : deningerKummerAugmentation u₂ *
      (2 * deningerSteinbergA m * deningerSteinbergB m) = 1 := by
    simpa using haug
  have hAB : deningerSteinbergA m * deningerSteinbergB m ≠ 0 :=
    mul_ne_zero (deningerSteinbergA_ne_zero m) (deningerSteinbergB_ne_zero m)
  have hy : 2 * ‖deningerSteinbergA m * deningerSteinbergB m‖ ≠ 0 := by
    positivity
  have hnorm := congrArg norm haug'
  have hfactor : ‖2 * deningerSteinbergA m * deningerSteinbergB m‖ =
      2 * ‖deningerSteinbergA m * deningerSteinbergB m‖ := by
    rw [norm_mul, norm_mul]
    norm_num
    ring
  rw [norm_mul, norm_one, hfactor] at hnorm
  have hinv : (2 * ‖deningerSteinbergA m * deningerSteinbergB m‖)⁻¹ =
      ‖deningerKummerAugmentation u₂‖ := by
    apply (mul_right_cancel₀ hy)
    rw [inv_mul_cancel₀ hy, hnorm]
  rw [hinv]
  exact norm_deningerKummerAugmentation_le_coefficientL1 u₂

end

end RHTower
