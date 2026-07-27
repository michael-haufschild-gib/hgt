import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Polynomial growth against a high inverse power is integrable

`(2+|y|)^A (1+y²)^{-m}` is integrable on the line as soon as `2m > A+1`.

This is the shape produced by a Mellin transform with arbitrarily fast decay multiplied by a
polynomially bounded Dirichlet series: the decay order `m` is free, so the product can always be
made integrable.
-/

open MeasureTheory Real

namespace GaloisForLFunctions.HTGeometry

/-- **Integrability of polynomial growth against a high inverse power.** -/
theorem integrable_rpow_mul_inv_pow {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : A + 1 < 2 * (m : ℝ)) :
    Integrable fun y : ℝ => (2 + |y|) ^ A * ((1 + y ^ 2) ^ m)⁻¹ := by
  have hfin : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 2 * (m : ℝ) - A := by
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  have hbase : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 * (m : ℝ) - A))) :=
    integrable_one_add_norm hfin
  have hcont : Continuous fun y : ℝ => (2 + |y|) ^ A * ((1 + y ^ 2) ^ m)⁻¹ := by
    refine Continuous.mul ?_ ?_
    · exact (continuous_const.add continuous_abs).rpow_const fun _ => Or.inr hA
    · exact ((continuous_const.add (continuous_pow 2)).pow m).inv₀ fun y =>
        (by positivity : (0 : ℝ) < (1 + y ^ 2) ^ m).ne'
  refine Integrable.mono' (hbase.const_mul ((2 : ℝ) ^ A * 2 ^ m)) hcont.aestronglyMeasurable ?_
  filter_upwards with y
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 + |y|) ^ A * ((1 + y ^ 2) ^ m)⁻¹)]
  set u : ℝ := 1 + |y| with hu
  have hu1 : (1 : ℝ) ≤ u := by rw [hu]; linarith [abs_nonneg y]
  have hu0 : (0 : ℝ) < u := by linarith
  -- the growth factor
  have hA1 : (2 + |y|) ^ A ≤ 2 ^ A * u ^ A := by
    have hle : 2 + |y| ≤ 2 * u := by rw [hu]; linarith [abs_nonneg y]
    calc (2 + |y|) ^ A ≤ (2 * u) ^ A := Real.rpow_le_rpow (by positivity) hle hA
      _ = 2 ^ A * u ^ A := Real.mul_rpow (by norm_num) hu0.le
  -- the decay factor
  have hu2m : u ^ (2 * m) ≤ 2 ^ m * (1 + y ^ 2) ^ m := by
    have hsq : u ^ 2 ≤ 2 * (1 + y ^ 2) := by
      rw [hu]
      nlinarith [sq_nonneg (|y| - 1), sq_abs y]
    calc u ^ (2 * m) = (u ^ 2) ^ m := by rw [← pow_mul]
      _ ≤ (2 * (1 + y ^ 2)) ^ m := pow_le_pow_left₀ (by positivity) hsq m
      _ = 2 ^ m * (1 + y ^ 2) ^ m := by rw [mul_pow]
  have hXY : ((1 + y ^ 2) ^ m)⁻¹ ≤ 2 ^ m * (u ^ (2 * m))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div,
      div_le_iff₀ (by positivity)]
    linarith [hu2m]
  have hupow : u ^ (-(2 * (m : ℝ) - A)) = u ^ A * (u ^ (2 * m))⁻¹ := by
    rw [← Real.rpow_natCast u (2 * m), ← Real.rpow_neg hu0.le, ← Real.rpow_add hu0]
    congr 1
    push_cast
    ring
  rw [hupow]
  calc (2 + |y|) ^ A * ((1 + y ^ 2) ^ m)⁻¹ ≤ (2 ^ A * u ^ A) * (2 ^ m * (u ^ (2 * m))⁻¹) :=
        mul_le_mul hA1 hXY (by positivity) (by positivity)
    _ = 2 ^ A * 2 ^ m * (u ^ A * (u ^ (2 * m))⁻¹) := by ring

end GaloisForLFunctions.HTGeometry
