import GaloisForLFunctions.HTGeometry.PaperRotationCommutatorIdealTrace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Quantitative norm of the paper rotation defect

The exact sinc factor retains the first-order size of a rotation commutator. This quantitative
information complements the paper's zero-or-infinite closed-ideal trace. All formulas include
zero angle; positive clock denominators are written as successors.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- Exact chord length, with its removable singularity already filled in. -/
theorem paperRotationPhase_norm_sinc (t : ℝ) :
    ‖paperRotationPhase t - 1‖ = |t| * |Real.sinc (t / 2)| := by
  change ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ = _
  rw [mul_comm (t : ℂ), Complex.norm_exp_I_mul_ofReal_sub_one]
  have hs : 2 * Real.sin (t / 2) = t * Real.sinc (t / 2) := by
    by_cases ht : t = 0
    · simp [ht]
    · rw [Real.sinc_of_ne_zero (div_ne_zero ht (by norm_num))]
      field_simp
  rw [hs, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]

/-- The angle bounds the actual operator phase defect at every scale. -/
theorem paperRotationPhase_norm_le (t : ℝ) :
    ‖paperRotationPhase t - 1‖ ≤ |t| := by
  rw [paperRotationPhase_norm_sinc]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (t / 2)) (abs_nonneg t)

/-- Multiplying by the positive clock denominator leaves exactly a sinc correction. -/
theorem paperRotationPhase_scaled_norm (t : ℝ) (q : ℕ) :
    ((q : ℝ) + 1) * ‖paperRotationPhase (t / ((q : ℝ) + 1)) - 1‖ =
      |t| * |Real.sinc (t / (2 * ((q : ℝ) + 1)))| := by
  have hq : 0 < (q : ℝ) + 1 := by positivity
  rw [paperRotationPhase_norm_sinc, abs_div, abs_of_pos hq,
    show t / ((q : ℝ) + 1) / 2 = t / (2 * ((q : ℝ) + 1)) by
      rw [div_div, mul_comm ((q : ℝ) + 1)]]
  field_simp

/-- Uniform sharp first-order bound, without any small-angle premise. -/
theorem paperRotationPhase_scaled_norm_le (t : ℝ) (q : ℕ) :
    ((q : ℝ) + 1) * ‖paperRotationPhase (t / ((q : ℝ) + 1)) - 1‖ ≤ |t| := by
  rw [paperRotationPhase_scaled_norm]
  simpa using mul_le_mul_of_nonneg_left
    (Real.abs_sinc_le_one (t / (2 * ((q : ℝ) + 1)))) (abs_nonneg t)

/-- The first-order coefficient of the shrinking phase defect is exactly angle magnitude. -/
theorem paperRotationPhase_scaled_norm_tendsto (t : ℝ) :
    Tendsto (fun q : ℕ =>
      ((q : ℝ) + 1) * ‖paperRotationPhase (t / ((q : ℝ) + 1)) - 1‖)
      atTop (𝓝 |t|) := by
  have hq : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun q : ℕ => t / (2 * ((q : ℝ) + 1))) atTop (𝓝 0) := by
    have h := Tendsto.div_atTop (tendsto_const_nhds (x := t / 2)) hq
    simpa only [div_div] using h
  have hs := ((Real.continuous_sinc.tendsto 0).comp ht).abs
  have h := (tendsto_const_nhds (x := |t|)).mul hs
  simpa only [Function.comp_def, Real.sinc_zero, abs_one, mul_one,
    paperRotationPhase_scaled_norm] using h

end

end GaloisForLFunctions.HTGeometry
