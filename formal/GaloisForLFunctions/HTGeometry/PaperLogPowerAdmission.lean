import GaloisForLFunctions.HTGeometry.PaperFourierLLogLAdmission
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Every finite logarithmic power is paid by L² admission

An explicit elementary majorant makes the finite-measure implication available
for arbitrary nonnegative real logarithmic exponents.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- Logarithmic powers have a global linear majorant on the norm half-line. -/
theorem exists_logPower_linear_bound (a : ℝ≥0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      Real.log (2 + t) ^ (a : ℝ) ≤ C * (2 + t) := by
  by_cases ha : (a : ℝ) = 0
  · refine ⟨1, one_pos, fun t ht => ?_⟩
    simp only [ha, Real.rpow_zero, one_mul]
    linarith
  · have ha0 : 0 < (a : ℝ) := lt_of_le_of_ne a.coe_nonneg (Ne.symm ha)
    refine ⟨(a : ℝ) ^ (a : ℝ), Real.rpow_pos_of_pos ha0 _, fun t ht => ?_⟩
    have ht0 : 0 < 2 + t := by linarith
    have hlog : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
    have h := Real.log_le_rpow_div ht0.le (one_div_pos.mpr ha0)
    have hpow := Real.rpow_le_rpow hlog h a.coe_nonneg
    calc
      Real.log (2 + t) ^ (a : ℝ) ≤
          ((2 + t) ^ (1 / (a : ℝ)) / (1 / (a : ℝ))) ^ (a : ℝ) := hpow
      _ = (a : ℝ) ^ (a : ℝ) * (2 + t) := by
        rw [div_eq_mul_inv, one_div, inv_inv,
          Real.mul_rpow (Real.rpow_nonneg ht0.le _) a.coe_nonneg,
          ← Real.rpow_mul ht0.le, inv_mul_cancel₀ ha, Real.rpow_one]
        ring

/-- An actual L² function pays every finite nonnegative logarithmic power. -/
theorem integrable_logPower_Lp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) (a : ℝ≥0) :
    Integrable (fun x => ‖f x‖ * Real.log (2 + ‖f x‖) ^ (a : ℝ)) μ := by
  obtain ⟨C, hC, hb⟩ := exists_logPower_linear_bound a
  have h1 := ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  have h2 := (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hm := (Lp.aestronglyMeasurable f).norm.aemeasurable
  refine ((h1.const_mul 2).add h2 |>.const_mul C).mono'
    (hm.mul ((aemeasurable_const.add hm).log.pow_const (a : ℝ))).aestronglyMeasurable ?_
  filter_upwards [] with x
  have hn := norm_nonneg (f x)
  have hl : 0 ≤ Real.log (2 + ‖f x‖) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (Real.rpow_nonneg hl _))]
  calc
    _ ≤ ‖f x‖ * (C * (2 + ‖f x‖)) := mul_le_mul_of_nonneg_left (hb _ hn) hn
    _ = C * (2 * ‖f x‖ + ‖f x‖ ^ 2) := by ring

end GaloisForLFunctions.HTGeometry
