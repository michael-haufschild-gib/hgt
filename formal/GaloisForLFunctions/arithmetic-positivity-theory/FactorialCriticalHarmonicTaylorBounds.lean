import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelMass
import GaloisForLFunctions.RHTower.MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Native critical harmonic bounds

Subtract the finite Taylor-bounded head from the exact half-line kernel mass.
This gives global polynomial bounds and quantitative estimates for the four
small harmonics used in the complete critical prime sign problem.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology


noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private theorem unit_pattern (u : ℝ) :
    factorialCriticalPatternDensity {0} (fun _ => 1) u = 1 := by
  simp [factorialCriticalPatternDensity]

private theorem kernel_weight_integrable :
    IntegrableOn factorialCriticalPrimeKernelWeight (Ioi (0 : ℝ)) := by
  simpa only [unit_pattern, mul_one] using
    integrableOn_factorialCriticalPrimeKernelWeight_pattern {0} (fun _ => 1)

private theorem kernel_weight_mass :
    (∫ u in Ioi (0 : ℝ), factorialCriticalPrimeKernelWeight u) = Real.pi^2 / 12 := by
  simpa only [unit_pattern, mul_one, Finset.sum_singleton, one_pow] using
    factorialCriticalPrimeKernelWeight_pattern_mass {0} (fun _ => 1)

/-- The native harmonic mass is the exact total weight minus its finite head. -/
theorem factorialCriticalHarmonicDefect_eq_head (m : ℕ) :
    factorialCriticalHarmonicDefect m = (m : ℝ) *
      (Real.pi^2 / 12 - ∫ u in (0 : ℝ)..(m : ℝ), factorialCriticalPrimeKernelWeight u) := by
  by_cases hm : m = 0
  · simp [hm, factorialCriticalHarmonicDefect]
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm
  have htail := factorialCriticalPatternHarmonicMass_eq_common_tail {0} (fun _ => 1) hm0
  simp only [factorialCriticalPatternHarmonicMass_singleton, one_pow, one_mul,
    unit_pattern, mul_one] at htail
  have hhead := intervalIntegral.integral_Ioi_sub_Ioi kernel_weight_integrable
    (Nat.cast_nonneg (α := ℝ) m)
  rw [kernel_weight_mass] at hhead
  rw [htail]
  congr 1
  linarith

private theorem kernel_weight_upper {u : ℝ} (hu : 0 < u) :
    factorialCriticalPrimeKernelWeight u ≤
      (Real.pi / 6)^2 / 2 - (Real.pi / 6)^4 * u^2 / 24 +
        (Real.pi / 6)^6 * u^4 / 720 := by
  have h := RHTower.one_sub_cos_le_sq_div_two_sub_pow_four_add_pow_six (Real.pi / 6 * u)
  rw [factorialCriticalPrimeKernelWeight, Real.rpow_neg hu.le, Real.rpow_two,
    show 2 * Real.pi * u / 12 = Real.pi / 6 * u by ring]
  have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (sq_nonneg u))
  convert h' using 1 <;> first | rfl | field_simp [hu.ne']

private theorem kernel_weight_lower {u : ℝ} (hu : 0 < u) :
    (Real.pi / 6)^2 / 2 - (Real.pi / 6)^4 * u^2 / 24 +
      (Real.pi / 6)^6 * u^4 / 720 - (Real.pi / 6)^8 * u^6 / 40320 ≤
        factorialCriticalPrimeKernelWeight u := by
  have h := RHTower.sq_div_two_sub_pow_four_add_pow_six_sub_pow_eight_le_one_sub_cos
    (Real.pi / 6 * u)
  rw [factorialCriticalPrimeKernelWeight, Real.rpow_neg hu.le, Real.rpow_two,
    show 2 * Real.pi * u / 12 = Real.pi / 6 * u by ring]
  have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (sq_nonneg u))
  convert h' using 1 <;> first | rfl | field_simp [hu.ne']

private theorem kernel_weight_intervalIntegrable (M : ℝ) (hM : 0 ≤ M) :
    IntervalIntegrable factorialCriticalPrimeKernelWeight volume 0 M := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hM).mpr
    (kernel_weight_integrable.mono_set Ioc_subset_Ioi_self)

private theorem upper_head_integral (M : ℝ) :
    (∫ u in (0 : ℝ)..M, (Real.pi / 6)^2 / 2 - (Real.pi / 6)^4 * u^2 / 24 +
      (Real.pi / 6)^6 * u^4 / 720) =
    (Real.pi / 6)^2 * M / 2 - (Real.pi / 6)^4 * M^3 / 72 +
      (Real.pi / 6)^6 * M^5 / 3600 := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem lower_head_integral (M : ℝ) :
    (∫ u in (0 : ℝ)..M, (Real.pi / 6)^2 / 2 - (Real.pi / 6)^4 * u^2 / 24 +
      (Real.pi / 6)^6 * u^4 / 720 - (Real.pi / 6)^8 * u^6 / 40320) =
    (Real.pi / 6)^2 * M / 2 - (Real.pi / 6)^4 * M^3 / 72 +
      (Real.pi / 6)^6 * M^5 / 3600 - (Real.pi / 6)^8 * M^7 / 282240 := by
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), upper_head_integral]
  simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    integral_pow]
  norm_num
  ring

/-- Global lower Taylor bound for the complete native harmonic mass. -/
theorem factorialCriticalHarmonicDefect_lower_taylor (m : ℕ) :
    Real.pi^2 * m / 12 - (Real.pi * m / 6)^2 / 2 +
      (Real.pi * m / 6)^4 / 72 - (Real.pi * m / 6)^6 / 3600 ≤
        factorialCriticalHarmonicDefect m := by
  have hM := Nat.cast_nonneg (α := ℝ) m
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hM
    (kernel_weight_intervalIntegrable m hM)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (fun u hu => kernel_weight_upper hu.1)
  rw [upper_head_integral] at h
  rw [factorialCriticalHarmonicDefect_eq_head]
  nlinarith only [mul_le_mul_of_nonneg_left h hM]

/-- Global upper Taylor bound for the complete native harmonic mass. -/
theorem factorialCriticalHarmonicDefect_upper_taylor (m : ℕ) :
    factorialCriticalHarmonicDefect m ≤
      Real.pi^2 * m / 12 - (Real.pi * m / 6)^2 / 2 +
        (Real.pi * m / 6)^4 / 72 - (Real.pi * m / 6)^6 / 3600 +
          (Real.pi * m / 6)^8 / 282240 := by
  have hM := Nat.cast_nonneg (α := ℝ) m
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hM
    (by apply Continuous.intervalIntegrable; fun_prop)
    (kernel_weight_intervalIntegrable m hM)
    (fun u hu => kernel_weight_lower hu.1)
  rw [lower_head_integral] at h
  rw [factorialCriticalHarmonicDefect_eq_head]
  nlinarith only [mul_le_mul_of_nonneg_left h hM]

private theorem pi_power_bounds (k : ℕ) :
    (157 / 50 : ℝ)^k ≤ Real.pi^k ∧ Real.pi^k ≤ (22 / 7 : ℝ)^k := by
  constructor
  · exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_d2]) k
  · exact pow_le_pow_left₀ Real.pi_pos.le (by linarith [Real.pi_lt_d4]) k

/-- The unique negative arithmetic harmonic retains a definite native mass. -/
theorem factorialCriticalHarmonicDefect_two_ge :
    (10 / 9 : ℝ) ≤ factorialCriticalHarmonicDefect 2 := by
  have h := factorialCriticalHarmonicDefect_lower_taylor 2
  norm_num at h
  nlinarith only [h, (pi_power_bounds 2).1, (pi_power_bounds 4).1,
    (pi_power_bounds 6).2]

/-- Small positive harmonics are bounded using the complete mass, not just its weight. -/
theorem factorialCriticalHarmonicDefect_three_le :
    factorialCriticalHarmonicDefect 3 ≤ (4 / 3 : ℝ) := by
  have h := factorialCriticalHarmonicDefect_upper_taylor 3
  norm_num at h
  nlinarith only [h, (pi_power_bounds 2).2, (pi_power_bounds 4).2,
    (pi_power_bounds 6).1, (pi_power_bounds 8).2]

theorem factorialCriticalHarmonicDefect_five_le :
    factorialCriticalHarmonicDefect 5 ≤ (4 / 3 : ℝ) := by
  have h := factorialCriticalHarmonicDefect_upper_taylor 5
  norm_num at h
  nlinarith only [h, (pi_power_bounds 2).2, (pi_power_bounds 4).2,
    (pi_power_bounds 6).1, (pi_power_bounds 8).2]

theorem factorialCriticalHarmonicDefect_six_le :
    factorialCriticalHarmonicDefect 6 ≤ (7 / 6 : ℝ) := by
  have h := factorialCriticalHarmonicDefect_upper_taylor 6
  norm_num at h
  nlinarith only [h, (pi_power_bounds 4).2, (pi_power_bounds 6).1,
    (pi_power_bounds 8).2]

end GaloisForLFunctions.ArithmeticPositivityTheory
