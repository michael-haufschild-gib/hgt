import GaloisForLFunctions.RHTower.CCM.CCMPrimeGapCrossBound
import GaloisForLFunctions.RHTower.ThetaIntegerLogGapPolarization
import GaloisForLFunctions.RHTower.ThetaPrimeSensitivePolarization

/-!
# Full arithmetic interference at the square-root prime-gap scale

The actual continuous cross pairing is bounded using consecutive prime gaps.
The complete Weil quadratic satisfies the corresponding bound plus its exact
prime correction. If all active prime-power translations are absent, the
correction vanishes. No estimate for the asymptotic size of prime gaps is used.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem abs_thetaGammaPolarGroundCrossPairing_primeLogCell_le
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    (N : ℕ) {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hp : Function.support phi ⊆ Metric.ball c₁ r)
    (hq : Function.support psi ⊆ Metric.ball c₂ r)
    (hleft : xiMassNthPrimeLogHeight N ≤ c₂ - c₁ - 2 * r)
    (hright : c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (N + 1)) :
    |thetaGammaPolarGroundCrossPairing phi psi| ≤
      (xiHeatCassiniOrderedPrimeGap N / (2 * Real.sqrt (nthPrimeSubtype N : ℝ))) *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  have hgap := (screwSignThreshold_lt_primeLogHeight N).le.trans hleft
  obtain ⟨A, hA, hbound⟩ := (hpc.union hqc).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hps : tsupport phi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inl hx))
  have hqs : tsupport psi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inr hx))
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    linarith [hx'.1, hy'.2, screwSignThreshold_pos]
  rw [thetaGammaPolarGroundCrossPairing_eq_ccm_screw a phi psi hpc hqc hps hqs hsep,
    thetaGroundNormSq_compactReal_eq_physical a phi hpc hps,
    thetaGroundNormSq_compactReal_eq_physical a psi hqc hqs]
  exact abs_screwRegularForm_ccm_primeLogCell_le _ _ N hr
    (by rwa [support_ccmThetaSourceOfCompactRealProfile])
    (by rwa [support_ccmThetaSourceOfCompactRealProfile]) hleft hright

/-- Full interference bound retaining every active arithmetic translation. -/
theorem abs_thetaRealArithmeticQuadratic_primeLogCell_difference_le
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    (N : ℕ) {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hp : Function.support phi ⊆ Metric.ball c₁ r)
    (hq : Function.support psi ⊆ Metric.ball c₂ r)
    (hleft : xiMassNthPrimeLogHeight N ≤ c₂ - c₁ - 2 * r)
    (hright : c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (N + 1)) :
    |thetaRealArithmeticQuadratic (phi + psi) - thetaRealArithmeticQuadratic (phi - psi)| ≤
      (2 * xiHeatCassiniOrderedPrimeGap N / Real.sqrt (nthPrimeSubtype N : ℝ)) *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) +
      2 * |thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
        thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi - psi)).toBoundedContinuousFunction| := by
  have hgap := (screwSignThreshold_lt_primeLogHeight N).le.trans hleft
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    linarith [hx'.1, hy'.2, screwSignThreshold_pos]
  rw [thetaRealArithmeticQuadratic_ordered_prime_correction phi psi hsep]
  have h := abs_thetaGammaPolarGroundCrossPairing_primeLogCell_le
    phi psi hpc hqc N hr hp hq hleft hright
  have h4 := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 4 by positivity)
  have hc : 4 * (xiHeatCassiniOrderedPrimeGap N /
        (2 * Real.sqrt (nthPrimeSubtype N : ℝ))) =
      2 * xiHeatCassiniOrderedPrimeGap N / Real.sqrt (nthPrimeSubtype N : ℝ) := by
    field_simp
    ring
  rw [← mul_assoc, hc] at h4
  calc
    _ ≤ |4 * thetaGammaPolarGroundCrossPairing phi psi| +
        |2 * (thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
        thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (thetaComplexify (phi - psi)).toBoundedContinuousFunction)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (4 * thetaGammaPolarGroundCrossPairing phi psi) 0
          (2 * (thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
            (thetaComplexify (phi + psi)).toBoundedContinuousFunction -
            thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
            (thetaComplexify (phi - psi)).toBoundedContinuousFunction))
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 4 by positivity),
        abs_of_pos (show (0 : ℝ) < 2 by positivity)]
      linarith only [h4]

theorem abs_thetaRealArithmeticQuadratic_primePowerFree_primeLogCell_le
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    (N : ℕ) {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hp : Function.support phi ⊆ Metric.ball c₁ r)
    (hq : Function.support psi ⊆ Metric.ball c₂ r)
    (hleft : xiMassNthPrimeLogHeight N ≤ c₂ - c₁ - 2 * r)
    (hright : c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (N + 1))
    (hfree : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, IsPrimePow n → x - y ≠ Real.log n) :
    |thetaRealArithmeticQuadratic (phi + psi) - thetaRealArithmeticQuadratic (phi - psi)| ≤
      (2 * xiHeatCassiniOrderedPrimeGap N / Real.sqrt (nthPrimeSubtype N : ℝ)) *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  have hgap := (screwSignThreshold_lt_primeLogHeight N).le.trans hleft
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    linarith [hx'.1, hy'.2, screwSignThreshold_pos]
  have h := abs_thetaRealArithmeticQuadratic_primeLogCell_difference_le
    phi psi hpc hqc N hr hp hq hleft hright
  rwa [thetaPrimeScalingCross_sum_eq_sub_of_primePowerFree phi psi hsep hfree,
    sub_self, abs_zero, mul_zero, add_zero] at h

end RHTower
