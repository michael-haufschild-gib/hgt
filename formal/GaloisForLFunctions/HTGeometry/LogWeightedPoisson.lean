import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals

/-!
# Logarithmic weights against a Poisson kernel

A logarithm grows more slowly than any power, so `log (2 + |x|)` is still integrable against the
Poisson kernel `(a² + x²)⁻¹`.  The comparison is made explicit by `log u ≤ 2√u` and the Japanese
bracket: the weighted kernel is dominated by a constant multiple of `(1 + |x|)^{-3/2}`.

This is what makes an archimedean rate of logarithmic growth pair with a rational half-density.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The logarithm is dominated by twice the square root. -/
theorem log_le_two_mul_sqrt {u : ℝ} (hu : 0 < u) : Real.log u ≤ 2 * Real.sqrt u := by
  have h1 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu)
  rw [Real.log_sqrt hu.le] at h1
  linarith [Real.sqrt_nonneg u]

/-- The Japanese bracket at exponent `3/2` is integrable on the line. -/
theorem integrable_one_add_abs_rpow_three_halves :
    Integrable fun x : ℝ => (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
  have h : Integrable fun x : ℝ => (1 + ‖x‖) ^ (-(3 / 2 : ℝ)) := by
    refine integrable_one_add_norm ?_
    simp
    norm_num
  exact h.congr (Filter.Eventually.of_forall fun x => by simp only [Real.norm_eq_abs])

/-- **A logarithmic weight is Poisson-integrable.** -/
theorem integrable_log_mul_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    Integrable fun x : ℝ => Real.log (2 + |x|) * (a ^ 2 + x ^ 2)⁻¹ := by
  have hm : (0 : ℝ) < min (a ^ 2) 1 := lt_min (by positivity) one_pos
  have hmle : min (a ^ 2) 1 ≤ a ^ 2 := min_le_left _ _
  have hmone : min (a ^ 2) 1 ≤ 1 := min_le_right _ _
  refine (integrable_one_add_abs_rpow_three_halves.const_mul
    (4 * Real.sqrt 2 / min (a ^ 2) 1)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul ?_ ?_
    · refine Continuous.log (continuous_const.add continuous_abs) fun x => ?_
      have h : (0 : ℝ) < 2 + |x| := by positivity
      exact ne_of_gt h
    · refine Continuous.inv₀ (by fun_prop) fun x => ?_
      have h : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
      exact ne_of_gt h
  filter_upwards with x
  have habs : (0 : ℝ) ≤ |x| := abs_nonneg x
  have ht : (0 : ℝ) < 1 + |x| := by linarith
  have hu : (0 : ℝ) < 2 + |x| := by linarith
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have hlog0 : 0 ≤ Real.log (2 + |x|) := Real.log_nonneg (by linarith)
  -- `log (2+|x|) ≤ 2√2 · √(1+|x|)`
  have hsq : Real.sqrt (2 + |x|) ≤ Real.sqrt 2 * Real.sqrt (1 + |x|) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlog : Real.log (2 + |x|) ≤ 2 * (Real.sqrt 2 * Real.sqrt (1 + |x|)) := by
    have := log_le_two_mul_sqrt hu
    nlinarith [Real.sqrt_nonneg (2 + |x|), Real.sqrt_nonneg (1 + |x|)]
  -- `(a²+x²)⁻¹ ≤ 2 / (m (1+|x|)²)`
  have hxsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hden : min (a ^ 2) 1 * (1 + |x|) ^ 2 ≤ 2 * (a ^ 2 + x ^ 2) := by
    have h2 : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
      rw [hxsq]
      nlinarith [sq_nonneg (1 - |x|)]
    nlinarith [sq_nonneg x, hm.le]
  have hinv : (a ^ 2 + x ^ 2)⁻¹ ≤ 2 / (min (a ^ 2) 1 * (1 + |x|) ^ 2) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hpos (by positivity)]
    linarith
  -- combine
  have hrpow : Real.sqrt (1 + |x|) / (1 + |x|) ^ 2 = (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + |x|) 2, div_eq_mul_inv,
      ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.log (2 + |x|) * (a ^ 2 + x ^ 2)⁻¹
      ≤ (2 * (Real.sqrt 2 * Real.sqrt (1 + |x|)))
          * (2 / (min (a ^ 2) 1 * (1 + |x|) ^ 2)) := by
        refine mul_le_mul hlog hinv (le_of_lt (inv_pos.mpr hpos)) (by positivity)
    _ = (4 * Real.sqrt 2 / min (a ^ 2) 1) * (Real.sqrt (1 + |x|) / (1 + |x|) ^ 2) := by
        field_simp
        ring
    _ = (4 * Real.sqrt 2 / min (a ^ 2) 1) * (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
        rw [hrpow]

end GaloisForLFunctions.HTGeometry
