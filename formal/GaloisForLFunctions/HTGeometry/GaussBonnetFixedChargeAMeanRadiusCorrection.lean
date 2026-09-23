import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanCriticalCorrection

/-!
# Critical rate of the arithmetic mean and the two physical radii

The mean radius has a positive quadratic displacement from criticality.
The individual radii split with equal and opposite linear coefficients.
All limits refer to the actual fixed-charge coexistence branch.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanRadiusCorrection (w φ : ℝ) : ℝ :=
  -egbFixedChargeAMeanCriticalCorrection φ * egbFixedChargeACriticalRadius w φ / (2 * egbFixedChargeACriticalWeight φ)

theorem egbFixedChargeAMeanRadiusCorrection_pos (w φ : ℝ) : 0 < egbFixedChargeAMeanRadiusCorrection w φ := by
  have hS := egbFixedChargeAMeanCriticalCorrection_neg φ
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hs := egbFixedChargeACriticalWeight_pos φ
  unfold egbFixedChargeAMeanRadiusCorrection
  exact div_pos (mul_pos (neg_pos.mpr hS) hr) (mul_pos (by norm_num) hs)

theorem egbFixedChargeAMeanRadius_difference_cross (w φ τ : ℝ) :
    (egbFixedChargeAMeanRadius w φ τ - egbFixedChargeACriticalRadius w φ) *
      (egbFixedChargeAMeanRadius w φ τ + egbFixedChargeACriticalRadius w φ) * egbFixedChargeACriticalWeight φ =
    -(egbFixedChargeAMeanWeight τ φ - egbFixedChargeACriticalWeight φ) * egbFixedChargeAMeanRadius w φ τ ^ (2 : ℕ) := by
  linear_combination egbFixedChargeA_mean_effective_scale w φ τ - egbFixedChargeACritical_effective_scale w φ

theorem egbFixedChargeAMeanRadius_normalized_difference (w φ τ : ℝ) :
    (egbFixedChargeAMeanRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
      -((egbFixedChargeAMeanWeight τ φ - egbFixedChargeACriticalWeight φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) *
        egbFixedChargeAMeanRadius w φ τ ^ (2 : ℕ) /
        ((egbFixedChargeAMeanRadius w φ τ + egbFixedChargeACriticalRadius w φ) * egbFixedChargeACriticalWeight φ) := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hs := egbFixedChargeACriticalWeight_pos φ
  apply (eq_div_iff (by positivity)).2
  calc
    _ = ((egbFixedChargeAMeanRadius w φ τ - egbFixedChargeACriticalRadius w φ) *
      (egbFixedChargeAMeanRadius w φ τ + egbFixedChargeACriticalRadius w φ) * egbFixedChargeACriticalWeight φ) /
      egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by ring
    _ = _ := by rw [egbFixedChargeAMeanRadius_difference_cross]; ring

theorem egbFixedChargeAMeanRadius_quadratic_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanRadiusCorrection w φ)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hs := egbFixedChargeACriticalWeight_pos φ
  simp only [egbFixedChargeAMeanRadius_normalized_difference]
  have hnum := (egbFixedChargeAMeanWeight_quadratic_critical_limit φ).neg.mul ((egbFixedChargeAMeanRadius_critical_limit w φ).pow 2)
  have hden := ((egbFixedChargeAMeanRadius_critical_limit w φ).add (tendsto_const_nhds (x := egbFixedChargeACriticalRadius w φ))).mul
    (tendsto_const_nhds (x := egbFixedChargeACriticalWeight φ))
  have h := hnum.div hden (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  unfold egbFixedChargeAMeanRadiusCorrection
  field_simp <;> ring

theorem egbFixedChargeAMeanRadius_linear_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMeanRadius_quadratic_critical_limit w φ).mul egbCoexistenceASymmetricRatio_critical_limit
  simp only [mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeA_radius_gap_normalized_mean (w φ τ : ℝ) :
    (egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ) / egbCoexistenceASymmetricRatio τ =
      2 * egbFixedChargeAMeanRadius w φ τ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeA_radius_gap_mean]
  field_simp

theorem egbFixedChargeA_radius_gap_asymmetry_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (2 * egbFixedChargeACriticalRadius w φ)) := by
  simp only [egbFixedChargeA_radius_gap_normalized_mean]
  exact (tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanRadius_critical_limit w φ)

theorem egbFixedChargeALargeRadius_linear_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeALargeRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (egbFixedChargeACriticalRadius w φ)) := by
  have h := (egbFixedChargeAMeanRadius_linear_critical_limit w φ).add (egbFixedChargeAMeanRadius_critical_limit w φ)
  simp only [zero_add] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeA_large_radius_mean]
  field_simp <;> ring

theorem egbFixedChargeASmallRadius_linear_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeASmallRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (-egbFixedChargeACriticalRadius w φ)) := by
  have h := (egbFixedChargeAMeanRadius_linear_critical_limit w φ).sub (egbFixedChargeAMeanRadius_critical_limit w φ)
  simp only [zero_sub] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeA_small_radius_mean]
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
