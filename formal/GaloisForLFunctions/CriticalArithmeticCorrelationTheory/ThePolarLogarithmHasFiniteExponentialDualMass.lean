import GaloisForLFunctions.HTGeometry.ReflectionIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The terminal logarithm has finite exponential dual mass

Two exponential substitutions reduce the boundary logarithm to the second
moment of the exponential density. Its ninth exponential weight is bounded
by the second exponential weight on the negative half-line.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

private theorem integral_log_sq_unit :
    (∫ x in Ioo (0 : ℝ) 1, Real.log x ^ 2) = 2 := by
  have him : (fun t : ℝ => Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)⟩
    · intro hx
      refine ⟨-Real.log x, neg_pos.mpr (Real.log_neg hx.1 hx.2), ?_⟩
      change Real.exp (- -Real.log x) = x
      rw [neg_neg, Real.exp_log hx.1]
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    simpa only [Pi.neg_apply, mul_neg, mul_one] using ((hasDerivAt_id' t).neg.exp)
  have hi : InjOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    fun x _ y _ h => neg_injective (Real.exp_injective h)
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (hd t).hasDerivWithinAt) hi (fun x => Real.log x ^ 2)
  rw [him] at he
  simp only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, Real.log_exp, neg_sq] at he
  rw [he]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1)
    (by norm_num) (by norm_num)
  norm_num [Real.Gamma_nat_eq_factorial] at hg
  simpa only [mul_comm] using hg

private theorem integral_second_exp_log_one_sub_exp_sq :
    (∫ y in Iio (0 : ℝ), Real.exp (2 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2) = 1 := by
  have him : (fun y : ℝ => 1 - Real.exp (2 * y)) '' Iio 0 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y < 0 at hy
      have he : Real.exp (2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      constructor <;> linarith only [he, Real.exp_pos (2 * y)]
    · intro hx
      refine ⟨Real.log (1 - x) / 2, ?_, ?_⟩
      · exact div_neg_of_neg_of_pos (Real.log_neg (by linarith only [hx.2])
          (by linarith only [hx.1])) (by norm_num)
      · change 1 - Real.exp (2 * (Real.log (1 - x) / 2)) = x
        rw [show 2 * (Real.log (1 - x) / 2) = Real.log (1 - x) by ring,
          Real.exp_log (by linarith only [hx.2])]
        ring
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => 1 - Real.exp (2 * y))
      (-(2 * Real.exp (2 * y))) y := by
    simpa only [mul_one, mul_comm, one_mul] using (((hasDerivAt_id' y).const_mul 2).exp.const_sub 1)
  have hi : InjOn (fun y : ℝ => 1 - Real.exp (2 * y)) (Iio 0) := by
    intro x _ y _ h
    have he : Real.exp (2 * x) = Real.exp (2 * y) := by linarith only [h]
    have he' := Real.exp_injective he
    linarith only [he']
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Iio
    (fun y _ => (hd y).hasDerivWithinAt) hi (fun x => Real.log x ^ 2)
  rw [him, integral_log_sq_unit] at he
  simp only [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos (Real.exp_pos _),
    smul_eq_mul, mul_assoc, integral_const_mul] at he
  linarith only [he]

/-- The squared dual weight of the terminal logarithm is integrable, with mass at most one. -/
theorem polar_logarithmic_dual_weight_integrable_and_le_one :
    IntegrableOn (fun y : ℝ => Real.exp (9 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2) (Iio 0) ∧
      (∫ y in Iio (0 : ℝ), Real.exp (9 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2) ≤ 1 := by
  have hi : IntegrableOn (fun y : ℝ =>
      Real.exp (2 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2) (Iio 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_second_exp_log_one_sub_exp_sq]
    norm_num
  have hpoint (y : ℝ) (hy : y < 0) :
      Real.exp (9 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2 ≤
        Real.exp (2 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2 :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hy])) (sq_nonneg _)
  have hmeas : AEStronglyMeasurable (fun y : ℝ =>
      Real.exp (9 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2) (volume.restrict (Iio 0)) := by
    fun_prop
  have hj : IntegrableOn (fun y : ℝ =>
      Real.exp (9 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2) (Iio 0) :=
    hi.mono' hmeas (by
      filter_upwards [self_mem_ae_restrict measurableSet_Iio] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint y hy)
  refine ⟨hj, ?_⟩
  calc
    _ ≤ ∫ y in Iio (0 : ℝ), Real.exp (2 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2 :=
      integral_mono_ae hj hi (by
        filter_upwards [self_mem_ae_restrict measurableSet_Iio] with y hy
        exact hpoint y hy)
    _ = 1 := integral_second_exp_log_one_sub_exp_sq

/-- The terminal logarithm contributes at most one to the squared exponential dual norm. -/
theorem integral_polar_logarithmic_dual_weight_le_one :
    (∫ y in Iio (0 : ℝ), Real.exp (9 * y) * Real.log (1 - Real.exp (2 * y)) ^ 2) ≤ 1 :=
  polar_logarithmic_dual_weight_integrable_and_le_one.2

#print axioms polar_logarithmic_dual_weight_integrable_and_le_one
#print axioms integral_polar_logarithmic_dual_weight_le_one
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
