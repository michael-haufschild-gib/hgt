import GaloisForLFunctions.RHTower.SmoothAFELogGaussianMoment
import GaloisForLFunctions.RHTower.SmoothAFECutoffGaussianTail
import Mathlib.MeasureTheory.Integral.DominatedConvergence


open MeasureTheory Filter Finset
noncomputable section
namespace RHTower

private theorem logGaussian_nonneg (y : ℝ) : 0 ≤ smoothAFELogGaussian y := by
  unfold smoothAFELogGaussian
  positivity

private theorem integrable_logGaussian : Integrable smoothAFELogGaussian := by
  simpa only [zero_mul, Real.exp_zero, mul_one] using
    integrable_smoothAFELogGaussian_mul_real_exp 0

private theorem cutoff_eq_logGaussian_tail {x : ℝ} (hx : 0 < x) :
    smoothAFECutoff x = ((∫ y in Set.Ici (Real.log x), smoothAFELogGaussian y : ℝ) : ℂ) := by
  rw [integral_Ici_eq_integral_Ioi]
  simpa only [Real.exp_log hx, smoothAFELogGaussian] using
    smoothAFECutoff_exp_eq_gaussian_tail (Real.log x)

private theorem logThreshold_iff {R : ℝ} (hR : 0 < R) (n : ℕ) (y : ℝ) :
    y ∈ Set.Ici (Real.log (((n + 1 : ℕ) : ℝ) / R)) ↔ n ∈ range ⌊R * Real.exp y⌋₊ := by
  rw [Set.mem_Ici, Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hR,
    mem_range, ← Nat.add_one_le_iff, Nat.le_floor_iff (by positivity)]
  rw [mul_comm]

/-- Exact Gaussian averaging of a summable cutoff-weighted series into its sharp prefixes. -/
theorem tsum_smoothAFECutoff_eq_logGaussian_prefix_integral
    (a : ℕ → ℂ) {R : ℝ} (hR : 0 < R)
    (hsum : Summable (fun n : ℕ => ‖a n‖ *
      (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)).re)) :
    (∑' n : ℕ, a n * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)) =
      ∫ y : ℝ, (smoothAFELogGaussian y : ℂ) * ∑ n ∈ range ⌊R * Real.exp y⌋₊, a n := by
  classical
  let F : ℕ → ℝ → ℂ := fun n =>
    (Set.Ici (Real.log (((n + 1 : ℕ) : ℝ) / R))).indicator
      (fun y => (smoothAFELogGaussian y : ℂ) * a n)
  have hint (n : ℕ) : Integrable (F n) :=
    (integrable_logGaussian.ofReal.mul_const (a n)).indicator measurableSet_Ici
  have hsingle (n : ℕ) : (∫ y : ℝ, F n y) =
      a n * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R) := by
    rw [show F n = (Set.Ici (Real.log (((n + 1 : ℕ) : ℝ) / R))).indicator
      (fun y => (smoothAFELogGaussian y : ℂ) * a n) from rfl,
      integral_indicator measurableSet_Ici, integral_mul_const,
      integral_complex_ofReal, ← cutoff_eq_logGaussian_tail (by positivity), mul_comm]
  have hnorm (n : ℕ) : (∫ y : ℝ, ‖F n y‖) =
      ‖a n‖ * (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)).re := by
    have hpoint : (fun y => ‖F n y‖) =
        (Set.Ici (Real.log (((n + 1 : ℕ) : ℝ) / R))).indicator
          (fun y => smoothAFELogGaussian y * ‖a n‖) := by
      funext y
      by_cases hy : y ∈ Set.Ici (Real.log (((n + 1 : ℕ) : ℝ) / R))
      · simp only [F, Set.indicator_of_mem hy, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (logGaussian_nonneg y)]
      · simp only [F, Set.indicator_of_notMem hy, norm_zero]
    rw [hpoint, integral_indicator measurableSet_Ici, integral_mul_const,
      cutoff_eq_logGaussian_tail (by positivity), Complex.ofReal_re, mul_comm]
  have hsumNorm : Summable (fun n : ℕ => ∫ y : ℝ, ‖F n y‖) := by
    simpa only [hnorm] using hsum
  have hpoint (y : ℝ) : (∑' n : ℕ, F n y) =
      (smoothAFELogGaussian y : ℂ) * ∑ n ∈ range ⌊R * Real.exp y⌋₊, a n := by
    rw [tsum_eq_sum (s := range ⌊R * Real.exp y⌋₊) (fun n hn => ?_), mul_sum]
    · apply sum_congr rfl
      intro n hn
      exact Set.indicator_of_mem ((logThreshold_iff hR n y).mpr hn) _
    · exact Set.indicator_of_notMem (fun hy => hn ((logThreshold_iff hR n y).mp hy)) _
  calc
    _ = ∑' n : ℕ, ∫ y : ℝ, F n y := by simp only [hsingle]
    _ = ∫ y : ℝ, ∑' n : ℕ, F n y := integral_tsum_of_summable_integral_norm hint hsumNorm
    _ = _ := integral_congr_ae (Eventually.of_forall hpoint)

end RHTower
