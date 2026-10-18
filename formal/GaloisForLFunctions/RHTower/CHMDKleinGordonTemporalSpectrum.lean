import GaloisForLFunctions.RHTower.CHMDTemporalCosineExtraction
import GaloisForLFunctions.RHTower.CHMDMobiusFoldedTransportOfKleinGordonPrimeWave

/-!
# The continuous temporal spectrum of the Klein–Gordon kernel

Every positive frequency has a null fibre under `r ↦ sqrt(r²+2)`.
Consequently the prime kernel and its spatial derivatives have zero
temporal cosine coefficient at every positive frequency. This is a
statement about each kernel, before the arithmetic sum over scales.
-/

open MeasureTheory Filter Set Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone GaloisForLFunctions.HTGeometry

attribute [local fun_prop] continuous_sechSqHalf

noncomputable section

private theorem kgFrequency_fibre_null (lam : ℝ) :
    ∀ᵐ r : ℝ, Real.sqrt (r ^ 2 + 2) ≠ lam := by
  filter_upwards [volume.ae_ne (Real.sqrt (lam ^ 2 - 2)),
    volume.ae_ne (-Real.sqrt (lam ^ 2 - 2))] with r hp hn
  intro h
  have hs : r ^ 2 + 2 = lam ^ 2 := by
    rw [← h, Real.sq_sqrt (by positivity)]
  have hr : Real.sqrt (lam ^ 2 - 2) = |r| := by
    rw [show lam ^ 2 - 2 = r ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  by_cases hsign : 0 ≤ r
  · exact hp (by simp only [hr, abs_of_nonneg hsign])
  · exact hn (by simp only [hr, abs_of_neg (lt_of_not_ge hsign), neg_neg])

/-- Integrable spectral amplitudes produce no temporal point mass. -/
theorem kgSpectralIntegral_temporalCoefficient_zero
    {a : ℝ → ℝ} (ha : Measurable a) (hi : Integrable a)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage
      (fun y => ∫ r : ℝ, a r * Real.cos (Real.sqrt (r ^ 2 + 2) * y)) lam)
      atTop (𝓝 0) :=
  temporalCosineAverage_spectralIntegral_tendsto_zero ha hi
    (by fun_prop) (fun r => Real.sqrt_pos.mpr (by positivity)) hlam
    (kgFrequency_fibre_null lam)

theorem measurable_chmdPrimeKernel_joint :
    Measurable (fun p : ℝ × ℝ => chmdPrimeKernel p.1 p.2) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      Real.cos (p.1.1 * Real.sqrt (p.2 ^ 2 + 2)) * sechSqHalf p.2 *
        Real.cos (p.2 * p.1.2)) := by
    exact (by fun_prop : Continuous _).measurable
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_kernelDeriv_joint :
    Measurable (fun p : ℝ × ℝ => kernelDeriv p.1 p.2) := by
  simp_rw [kernelDeriv_eq_kernelDerivFourier]
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      kgSymbolWeight p.1.1 p.2 * (p.2 * Real.sin (p.2 * p.1.2))) := by
    unfold kgSymbolWeight
    exact (by fun_prop : Continuous _).measurable
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_kernelDeriv2_joint :
    Measurable (fun p : ℝ × ℝ => kernelDeriv2 p.1 p.2) := by
  simp_rw [kernelDeriv2_eq_kernelDeriv2Fourier]
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      kgSymbolWeight p.1.1 p.2 * (p.2 ^ 2 * Real.cos (p.2 * p.1.2))) := by
    unfold kgSymbolWeight
    exact (by fun_prop : Continuous _).measurable
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_conjugatedLaplacian_joint :
    Measurable (fun p : ℝ × ℝ => conjugatedLaplacian p.1 p.2) := by
  unfold conjugatedLaplacian
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ => Real.exp (-(p.2 / 2)))).mul
    ((measurable_kernelDeriv2_joint.sub measurable_kernelDeriv_joint).add
      (measurable_chmdPrimeKernel_joint.div_const 4))

/-- Each spatial sample of the prime kernel has zero temporal cosine coefficient. -/
theorem chmdPrimeKernel_temporalCoefficient_zero (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage (fun y => chmdPrimeKernel y s) lam) atTop (𝓝 0) := by
  let a : ℝ → ℝ := fun r => sechSqHalf r * Real.cos (r * s)
  have hi : Integrable a := by
    refine integrable_sechSqHalf.mono' (by fun_prop) (Eventually.of_forall fun r => ?_)
    simp only [a, Real.norm_eq_abs, abs_mul, abs_of_pos (sechSqHalf_pos r)]
    exact mul_le_of_le_one_right (sechSqHalf_pos r).le (Real.abs_cos_le_one _)
  have h := (kgSpectralIntegral_temporalCoefficient_zero (by fun_prop : Measurable a)
    hi hlam).const_mul (1 / π)
  have heq : (fun y => chmdPrimeKernel y s) =
      fun y => (1 / π) * ∫ r : ℝ, a r * Real.cos (Real.sqrt (r ^ 2 + 2) * y) := by
    funext y
    rw [chmdPrimeKernel_eq_kgSymbolWeight]
    congr 1
    apply integral_congr_ae
    filter_upwards with r
    simp only [a, kgSymbolWeight, mul_comm, mul_left_comm]
  rw [heq]
  simpa only [mul_zero, ← temporalCosineAverage_const_mul] using h

theorem kernelDeriv_temporalCoefficient_zero (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage (fun y => kernelDeriv y s) lam) atTop (𝓝 0) := by
  let a : ℝ → ℝ := fun r => sechSqHalf r * (r * Real.sin (r * s))
  have hi : Integrable a := by
    refine integrable_abs_mul_sechSqHalf.mono' (by fun_prop)
      (Eventually.of_forall fun r => ?_)
    simp only [a, Real.norm_eq_abs, abs_mul, abs_of_pos (sechSqHalf_pos r)]
    calc sechSqHalf r * (|r| * |Real.sin (r * s)|)
        ≤ sechSqHalf r * (|r| * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg r))
            (sechSqHalf_pos r).le
      _ = |r| * sechSqHalf r := by ring
  have h := (kgSpectralIntegral_temporalCoefficient_zero (by fun_prop : Measurable a)
    hi hlam).const_mul (-(1 / π))
  have heq : (fun y => kernelDeriv y s) =
      fun y => -(1 / π) * ∫ r : ℝ, a r * Real.cos (Real.sqrt (r ^ 2 + 2) * y) := by
    funext y
    rw [kernelDeriv_eq_kernelDerivFourier, kernelDerivFourier]
    congr 1
    apply integral_congr_ae
    filter_upwards with r
    simp only [a, kgSymbolWeight, mul_comm, mul_left_comm, mul_assoc]
  rw [heq]
  simpa only [mul_zero, ← temporalCosineAverage_const_mul] using h

theorem kernelDeriv2_temporalCoefficient_zero (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage (fun y => kernelDeriv2 y s) lam) atTop (𝓝 0) := by
  let a : ℝ → ℝ := fun r => sechSqHalf r * (r ^ 2 * Real.cos (r * s))
  have hi : Integrable a := by
    refine integrable_sq_mul_sechSqHalf.mono' (by fun_prop)
      (Eventually.of_forall fun r => ?_)
    simp only [a, Real.norm_eq_abs, abs_mul, abs_of_pos (sechSqHalf_pos r),
      abs_of_nonneg (sq_nonneg r)]
    calc sechSqHalf r * (r ^ 2 * |Real.cos (r * s)|)
        ≤ sechSqHalf r * (r ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg r))
            (sechSqHalf_pos r).le
      _ = r ^ 2 * sechSqHalf r := by ring
  have h := (kgSpectralIntegral_temporalCoefficient_zero (by fun_prop : Measurable a)
    hi hlam).const_mul (-(1 / π))
  have heq : (fun y => kernelDeriv2 y s) =
      fun y => -(1 / π) * ∫ r : ℝ, a r * Real.cos (Real.sqrt (r ^ 2 + 2) * y) := by
    funext y
    rw [kernelDeriv2_eq_kernelDeriv2Fourier, kernelDeriv2Fourier]
    congr 1
    apply integral_congr_ae
    filter_upwards with r
    simp only [a, kgSymbolWeight, mul_comm, mul_left_comm, mul_assoc]
  rw [heq]
  simpa only [mul_zero, ← temporalCosineAverage_const_mul] using h

end

end RHTower.CHMDChebyshevTransport
