import GaloisForLFunctions.RHTower.ThetaRealGroundPolarization

/-!
# Polarization with precisely the active prime-power translations

Ordered supports give an exact continuous cross term and a separate, explicit
prime correlation correction. The correction vanishes when support differences
avoid logarithms of prime powers. Logarithms with zero von Mangoldt weight impose
no restriction. This extends the earlier complete-integer-log exclusion theorem.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

private theorem ordered_diagonal_product_zero (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (x : ℝ) : phi x * psi x = 0 := by
  by_cases hp : phi x = 0
  · rw [hp, zero_mul]
  by_cases hq : psi x = 0
  · rw [hq, mul_zero]
  have := hsep x hq x hp
  linarith

private theorem ordered_reverse_product_zero (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (x t : ℝ) (ht : 0 ≤ t) : phi (x + t) * psi x = 0 := by
  by_cases hp : phi (x + t) = 0
  · rw [hp, zero_mul]
  by_cases hq : psi x = 0
  · rw [hq, mul_zero]
  have := hsep x hq (x + t) hp
  linarith

/-- Exact polarization without any arithmetic exclusion: the prime correction is retained. -/
theorem thetaRealArithmeticQuadratic_ordered_prime_correction
    (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y) :
    thetaRealArithmeticQuadratic (phi + psi) - thetaRealArithmeticQuadratic (phi - psi) =
      4 * thetaGammaPolarGroundCrossPairing phi psi -
        2 * (thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
          thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi - psi)).toBoundedContinuousFunction) := by
  have hsq (x : ℝ) : ‖thetaComplexify (phi + psi) x‖ ^ 2 =
      ‖thetaComplexify (phi - psi) x‖ ^ 2 := by
    simp only [thetaComplexify_apply, add_apply, sub_apply,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [ordered_diagonal_product_zero phi psi hsep x]
  have hnorm : thetaGroundNormSq (thetaComplexify (phi + psi)) =
      thetaGroundNormSq (thetaComplexify (phi - psi)) := by
    unfold thetaGroundNormSq thetaGroundNormDensity
    simp_rw [hsq]
  have hpoint (p : ℝ × ℝ) (hp : 0 < p.1) :
      thetaGammaPolarQuadraticDensity thetaCuspTiltSource (thetaComplexify (phi + psi)) p -
        thetaGammaPolarQuadraticDensity thetaCuspTiltSource (thetaComplexify (phi - psi)) p =
      4 * (thetaGammaPolarScalingKernel p.1 * thetaCuspFullSource p.2 *
        thetaCuspFullSource (p.2 + p.1) * phi p.2 * psi (p.2 + p.1)) := by
    have hr := ordered_reverse_product_zero phi psi hsep p.2 p.1 hp.le
    unfold thetaGammaPolarQuadraticDensity
    rw [hsq, hsq]
    simp only [thetaCuspTiltSource_k, thetaComplexify_apply, add_apply, sub_apply,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    linear_combination 4 * thetaGammaPolarScalingKernel p.1 * thetaCuspFullSource p.2 *
      thetaCuspFullSource (p.2 + p.1) * hr
  have hc : (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource
        (thetaComplexify (phi + psi)) p ∂thetaContinuousLinkMeasure) -
      (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource
        (thetaComplexify (phi - psi)) p ∂thetaContinuousLinkMeasure) =
      4 * thetaGammaPolarGroundCrossPairing phi psi := by
    rw [← thetaOrderedGroundCross_eq_pairing phi psi hsep,
      ← integral_sub (integrable_thetaGammaPolarQuadraticDensity _)
        (integrable_thetaGammaPolarQuadraticDensity _), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [thetaContinuousLinkMeasure_ae_pos] with p hp
    exact hpoint p hp
  unfold thetaRealArithmeticQuadratic thetaFullArithmeticQuadratic
  rw [hnorm]
  linarith only [hc]

theorem thetaPrimeScalingCross_sum_eq_sub_of_primePowerFree
    (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (hfree : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, IsPrimePow n → x - y ≠ Real.log n) :
    thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction =
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction := by
  unfold thetaPrimeScalingCross
  apply integral_congr_ae
  filter_upwards with p
  by_cases hw : ArithmeticFunction.vonMangoldt p.1 = 0
  · simp only [thetaPrimeScalingCrossDensity, thetaPrimeLinkDensity_eq_real, hw,
      zero_div, zero_mul, Complex.ofReal_zero, Complex.zero_re, mul_zero]
  have hlog : 0 ≤ Real.log p.1 := by
    by_cases hn : p.1 = 0
    · simp [hn]
    exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have h₁ := ordered_reverse_product_zero phi psi hsep p.2 (Real.log p.1) hlog
  have h₂ : phi p.2 * psi (p.2 + Real.log p.1) = 0 := by
    by_cases hp : phi p.2 = 0
    · rw [hp, zero_mul]
    by_cases hq : psi (p.2 + Real.log p.1) = 0
    · rw [hq, mul_zero]
    exact False.elim (hfree _ hq _ hp p.1
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hw) (by ring))
  simp only [thetaPrimeScalingCrossDensity, SchwartzMap.toBoundedContinuousFunction_apply,
    thetaComplexify_apply, add_apply, sub_apply,
    Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  congr 1
  nlinarith only [h₁, h₂]

/-- Prime-power avoidance suffices for the exact full quadratic identity. Composite
integers with zero von Mangoldt weight may lie inside the difference interval. -/
theorem thetaRealArithmeticQuadratic_primePowerFree_polarization
    (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (hfree : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, IsPrimePow n → x - y ≠ Real.log n) :
    thetaRealArithmeticQuadratic (phi + psi) - thetaRealArithmeticQuadratic (phi - psi) =
      4 * thetaGammaPolarGroundCrossPairing phi psi := by
  rw [thetaRealArithmeticQuadratic_ordered_prime_correction phi psi hsep,
    thetaPrimeScalingCross_sum_eq_sub_of_primePowerFree phi psi hsep hfree,
    sub_self, mul_zero, sub_zero]

end RHTower.ThetaSourceWard
