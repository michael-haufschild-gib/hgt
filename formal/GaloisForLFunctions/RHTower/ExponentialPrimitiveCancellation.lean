import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exponential cancellation survives taking a primitive

A locally integrable source that is little-o of the exponential has a
primitive with the same cancellation. The proof retains the finite initial
interval and controls the tail by an exact exponential integral.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

theorem tendsto_exp_neg_mul_primitive_zero (f : ℝ → ℝ)
    (hi : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hf : Tendsto (fun t => Real.exp (-t) * f t) atTop (nhds 0)) :
    Tendsto (fun t => Real.exp (-t) * ∫ s in (0 : ℝ)..t, f s) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp hf) (epsilon / 2) (half_pos hepsilon)
  have hhead : Tendsto (fun t => Real.exp (-t) * |∫ s in (0 : ℝ)..T, f s|)
      atTop (nhds 0) := by
    simpa only [zero_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const
      |∫ s in (0 : ℝ)..T, f s|
  obtain ⟨A, hA⟩ := (Metric.tendsto_atTop.mp hhead) (epsilon / 2) (half_pos hepsilon)
  refine ⟨max A T, ?_⟩
  intro t ht
  have hAt : A ≤ t := (le_max_left _ _).trans ht
  have hTt : T ≤ t := (le_max_right _ _).trans ht
  have hheadlt : Real.exp (-t) * |∫ s in (0 : ℝ)..T, f s| < epsilon / 2 := by
    have h := hA t hAt
    simpa only [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs] using h
  have hpoint (s : ℝ) (hs : T ≤ s) : |f s| ≤ (epsilon / 2) * Real.exp s := by
    have h := hT s hs
    simp only [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)] at h
    have hm := mul_le_mul_of_nonneg_left h.le (Real.exp_pos s).le
    have hc : Real.exp s * Real.exp (-s) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [← mul_assoc, hc, one_mul] at hm
    simpa only [mul_comm] using hm
  have htail : |∫ s in T..t, f s| ≤ (epsilon / 2) * (Real.exp t - Real.exp T) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (f := f) hTt
      (show ∀ᵐ s : ℝ ∂volume, s ∈ Ioc T t → ‖f s‖ ≤ (epsilon / 2) * Real.exp s from by
        filter_upwards [] with s hs
        simpa only [Real.norm_eq_abs] using hpoint s hs.1.le)
      ((Real.continuous_exp.const_mul (epsilon / 2)).intervalIntegrable T t)
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_exp] using h
  have hsum : |∫ s in (0 : ℝ)..t, f s| ≤
      |∫ s in (0 : ℝ)..T, f s| + (epsilon / 2) * (Real.exp t - Real.exp T) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 T) (hi T t)]
    exact (abs_add_le _ _).trans (add_le_add le_rfl htail)
  have hscaled := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (-t)).le
  have hcancel : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
  have htailpos : 0 ≤ Real.exp (-t) * ((epsilon / 2) * Real.exp T) := by positivity
  have hnormalize : Real.exp (-t) * ((epsilon / 2) * (Real.exp t - Real.exp T)) =
      epsilon / 2 - Real.exp (-t) * ((epsilon / 2) * Real.exp T) := by
    calc
      _ = (epsilon / 2) * (Real.exp (-t) * Real.exp t) -
          Real.exp (-t) * ((epsilon / 2) * Real.exp T) := by ring
      _ = _ := by rw [hcancel, mul_one]
  rw [mul_add, hnormalize] at hscaled
  linarith only [hscaled, hheadlt, htailpos]

end RHTower
