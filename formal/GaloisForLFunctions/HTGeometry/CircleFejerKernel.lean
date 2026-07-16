import GaloisForLFunctions.HTGeometry.HardyTaylorCoefficient
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite Fejer kernels on the circle

This module packages the finite nonnegative Fejer kernel in the angular parametrization used by
the polynomial Hardy factorization.  It proves its normalization and the exact Fubini identity
against every integrable function on a finite circle measure.
-/

open MeasureTheory Complex Filter Topology Set Polynomial PowerSeries Finset
open scoped Real ENNReal NNReal Nat

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The normalized finite Fejer kernel, with the first variable in angular coordinates. -/
noncomputable def circleFejerKernel (N : ℕ) (theta : ℝ) (w : Circle) : ℝ :=
  ((N + 1 : ℝ)⁻¹) *
    ‖∑ j ∈ Finset.range (N + 1),
      (((starRingEnd ℂ) (w : ℂ)) ^ j) * (circleMap 0 1 theta) ^ j‖ ^ 2

theorem circleFejerKernel_nonneg (N : ℕ) (theta : ℝ) (w : Circle) :
    0 ≤ circleFejerKernel N theta w := by
  unfold circleFejerKernel
  positivity

theorem circleFejerKernel_le (N : ℕ) (theta : ℝ) (w : Circle) :
    circleFejerKernel N theta w ≤ N + 1 := by
  unfold circleFejerKernel
  have hsum : ‖∑ j ∈ Finset.range (N + 1),
      ((starRingEnd ℂ) (w : ℂ)) ^ j * circleMap 0 1 theta ^ j‖ ≤ (N + 1 : ℝ) := by
    calc
      ‖∑ j ∈ Finset.range (N + 1),
          ((starRingEnd ℂ) (w : ℂ)) ^ j * circleMap 0 1 theta ^ j‖
          ≤ ∑ j ∈ Finset.range (N + 1),
              ‖((starRingEnd ℂ) (w : ℂ)) ^ j * circleMap 0 1 theta ^ j‖ :=
        norm_sum_le _ _
      _ = ∑ _j ∈ Finset.range (N + 1), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [norm_circleMap_zero]
      _ = N + 1 := by simp
  have hM : (0 : ℝ) < N + 1 := by positivity
  calc
    (N + 1 : ℝ)⁻¹ *
        ‖∑ j ∈ Finset.range (N + 1),
          ((starRingEnd ℂ) (w : ℂ)) ^ j * circleMap 0 1 theta ^ j‖ ^ 2
        ≤ (N + 1 : ℝ)⁻¹ * (N + 1 : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsum 2)
        (inv_nonneg.mpr hM.le)
    _ = (N + 1 : ℝ) := by
      field_simp [ne_of_gt hM]

/-- The normalized angular integral of the Fejer kernel is one. -/
theorem circleAverage_circleFejerKernel (N : ℕ) (w : Circle) :
    (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..(2 * Real.pi),
      circleFejerKernel N theta w = 1 := by
  unfold circleFejerKernel
  rw [intervalIntegral.integral_const_mul]
  have hparse := circleAverage_normSq_poly (1 : ℝ) (N + 1)
    (fun j => ((starRingEnd ℂ) (w : ℂ)) ^ j)
  calc
    (2 * Real.pi)⁻¹ * ((N + 1 : ℝ)⁻¹ *
        ∫ theta in (0 : ℝ)..(2 * Real.pi),
          ‖∑ j ∈ Finset.range (N + 1),
            ((starRingEnd ℂ) (w : ℂ)) ^ j * circleMap 0 1 theta ^ j‖ ^ 2) =
        (N + 1 : ℝ)⁻¹ * ((2 * Real.pi)⁻¹ *
          ∫ theta in (0 : ℝ)..(2 * Real.pi),
            ‖∑ j ∈ Finset.range (N + 1),
              ((starRingEnd ℂ) (w : ℂ)) ^ j * circleMap 0 1 theta ^ j‖ ^ 2) := by ring
    _ = (N + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1),
        ‖((starRingEnd ℂ) (w : ℂ)) ^ j‖ ^ 2 * (1 : ℝ) ^ (2 * j) := by rw [hparse]
    _ = 1 := by
      have hw : ‖(starRingEnd ℂ) (w : ℂ)‖ = 1 := by simp
      simp only [norm_pow, hw, one_pow, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      exact inv_mul_cancel₀ (ne_of_gt (by positivity : (0 : ℝ) < N + 1))

theorem continuous_circleFejerKernel_uncurry (N : ℕ) :
    Continuous (Function.uncurry (fun theta w => circleFejerKernel N theta w)) := by
  unfold circleFejerKernel
  fun_prop

/-- The Fejer kernel times an integrable circle function is integrable on the angular product. -/
theorem integrable_circleFejerKernel_mul_prod
    (N : ℕ) (mu : Measure Circle) [IsFiniteMeasure mu]
    {f : Circle → ℝ} (hf : Integrable f mu) :
    Integrable (Function.uncurry (fun theta w => circleFejerKernel N theta w * f w))
      ((volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).prod mu) := by
  let muTheta : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  have hbase : Integrable (fun p : ℝ × Circle => (N + 1 : ℝ) * ‖f p.2‖)
      (muTheta.prod mu) := by
    simpa only [Function.comp_apply] using (hf.norm.comp_snd muTheta).const_mul (N + 1 : ℝ)
  refine Integrable.mono' hbase ?_ ?_
  · exact (continuous_circleFejerKernel_uncurry N).aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd
  · filter_upwards with p
    change |circleFejerKernel N p.1 p.2 * f p.2| ≤ (N + 1 : ℝ) * ‖f p.2‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (circleFejerKernel_nonneg N p.1 p.2)]
    exact mul_le_mul_of_nonneg_right (circleFejerKernel_le N p.1 p.2) (abs_nonneg _)

/-- Fejer averaging preserves the integral of every integrable real circle function. -/
theorem circleFejerKernel_integral_identity
    (N : ℕ) (mu : Measure Circle) [IsFiniteMeasure mu]
    {f : Circle → ℝ} (hf : Integrable f mu) :
    (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..(2 * Real.pi),
      ∫ w, circleFejerKernel N theta w * f w ∂mu = ∫ w, f w ∂mu := by
  let muTheta : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hint := integrable_circleFejerKernel_mul_prod N mu hf
  change Integrable _ (muTheta.prod mu) at hint
  rw [intervalIntegral.integral_of_le hpi]
  change (2 * Real.pi)⁻¹ * ∫ theta, (∫ w,
    circleFejerKernel N theta w * f w ∂mu) ∂muTheta = _
  rw [integral_integral_swap hint]
  have hinner : ∀ w : Circle,
      (∫ theta, circleFejerKernel N theta w * f w ∂muTheta) =
        (2 * Real.pi) * f w := by
    intro w
    rw [integral_mul_const]
    have havg := circleAverage_circleFejerKernel N w
    have hKint : (∫ theta, circleFejerKernel N theta w ∂muTheta) = 2 * Real.pi := by
      rw [← intervalIntegral.integral_of_le hpi]
      have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      calc
        (∫ theta in (0 : ℝ)..(2 * Real.pi), circleFejerKernel N theta w) =
            (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
              ∫ theta in (0 : ℝ)..(2 * Real.pi), circleFejerKernel N theta w) := by
              field_simp
        _ = 2 * Real.pi := by rw [havg, mul_one]
    rw [hKint]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_const_mul]
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

end

end GaloisForLFunctions.HTGeometry
