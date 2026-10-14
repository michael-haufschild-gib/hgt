import GaloisForLFunctions.RHTower.WeilLagArchCurvatureSign
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Exact leading coefficient of the native archimedean curvature

The complete trivial-zero term disappears at cubic scale. The logarithmic
curvature retains coefficient one sixth, so the signed correction has limit
minus one sixth. No arithmetic cancellation estimate is used.
-/

namespace RHTower.IntegerLagCurvature
noncomputable section
open Filter
open scoped Topology

private theorem shifted_ratio_tendsto (a b : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + a) / (n + b)) atTop (𝓝 1) := by
  simpa only [one_mul, div_one, add_comm] using
    tendsto_add_mul_div_add_mul_atTop_nhds a b 1 (d := (1 : ℝ)) one_ne_zero

theorem trivialCurvature_cubic_tendsto_zero :
    Tendsto (fun n : ℕ => (n + 3 : ℝ) ^ 3 * trivialCurvature n) atTop (𝓝 0) := by
  have hb (n : ℕ) :
      (n + 3 : ℝ) ^ 3 * trivialCurvature n ≤
        (((n : ℝ) + 3) / (n + 2)) ^ 2 * (1 / (n + 1)) := by
    calc
      _ ≤ (n + 3 : ℝ) ^ 3 *
          (1 / ((n + 2 : ℝ) ^ 2 * ((n + 2 : ℝ) ^ 2 - 1))) :=
        mul_le_mul_of_nonneg_left (trivialCurvature_quartic_bound n) (by positivity)
      _ = _ := by
        rw [show ((n : ℝ) + 2) ^ 2 - 1 = (n + 1) * (n + 3) by ring]
        have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
        have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
        have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
        field_simp
  apply squeeze_zero (fun n => mul_nonneg (by positivity) (trivialCurvature_bounds n).1) hb
  simpa only [one_pow, mul_zero] using
    ((shifted_ratio_tendsto 3 2).pow 2).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem logCurvature_centered_cubic_tendsto :
    Tendsto (fun n : ℕ => (n + 3 : ℝ) ^ 3 *
      (logCurvature n - 1 / (n + 3 : ℝ))) atTop (𝓝 (1 / 6)) := by
  have hl : Tendsto (fun n : ℕ => (1 / 6 : ℝ) * ((n + 3 : ℝ) / (n + 4)))
      atTop (𝓝 (1 / 6)) := by
    simpa only [mul_one] using (shifted_ratio_tendsto 3 4).const_mul (1 / 6)
  have hu : Tendsto (fun n : ℕ => (1 / 6 : ℝ) * ((n + 3 : ℝ) / (n + 2)))
      atTop (𝓝 (1 / 6)) := by
    simpa only [mul_one] using (shifted_ratio_tendsto 3 2).const_mul (1 / 6)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro n
    calc
      _ = (n + 3 : ℝ) ^ 3 * (1 / (6 * (n + 3 : ℝ) ^ 2 * (n + 4))) := by
        have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
        have h4 : (n : ℝ) + 4 ≠ 0 := by positivity
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (logCurvature_centered_cubic_bounds n).1 (by positivity)
  · intro n
    calc
      _ ≤ (n + 3 : ℝ) ^ 3 * (1 / (6 * (n + 3 : ℝ) ^ 2 * (n + 2))) :=
        mul_le_mul_of_nonneg_left (logCurvature_centered_cubic_bounds n).2 (by positivity)
      _ = _ := by
        have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
        have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
        field_simp

theorem archCurvatureCorrection_cubic_tendsto :
    Tendsto (fun n : ℕ => (n + 3 : ℝ) ^ 3 * archCurvatureCorrection n)
      atTop (𝓝 (-(1 / 6))) := by
  simpa only [archCurvatureCorrection_eq, mul_sub, zero_sub] using
    trivialCurvature_cubic_tendsto_zero.sub logCurvature_centered_cubic_tendsto

end
end RHTower.IntegerLagCurvature
