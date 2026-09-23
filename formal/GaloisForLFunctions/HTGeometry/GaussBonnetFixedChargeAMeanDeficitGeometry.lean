import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitCriticalLimit

/-!
# Force and spatial laws of the collapsing mean deficit

The deficit is asymptotically half the product of the mean force and its
displacement to the intermediate root. It is cubic in that shrinking
spatial separation, with a positive vanishing quadratic stiffness.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMean_force_displacement_sixth_limit (w φ l : ℝ) :
    Tendsto (fun τ => ((egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeAMeanRadius w φ τ) *
      deriv (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l) (egbFixedChargeAMeanRadius w φ τ)) /
      egbCoexistenceASymmetricRatio τ ^ (6 : ℕ)) atBot (𝓝 (2 * egbFixedChargeAMeanDeficitCoefficient w φ)) := by
  have h := (egbFixedChargeAMiddleRadius_mean_quadratic_limit w φ).mul (egbFixedChargeAMeanGibbs_quartic_force_limit w φ l)
  rw [egbFixedChargeAMeanDeficitCoefficient_force_product] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_force_displacement_ratio_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l₁ /
      ((egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeAMeanRadius w φ τ) *
        deriv (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
          (exp w * cos φ) (exp w * sin φ) l₂) (egbFixedChargeAMeanRadius w φ τ)))
      atBot (𝓝 (1 / 2 : ℝ)) := by
  have hK := egbFixedChargeAMeanDeficitCoefficient_pos w φ
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l₁).div
    (egbFixedChargeAMean_force_displacement_sixth_limit w φ l₂) (by positivity)
  have he : egbFixedChargeAMeanDeficitCoefficient w φ / (2 * egbFixedChargeAMeanDeficitCoefficient w φ) = (1 / 2 : ℝ) := by
    field_simp
  rw [he] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanDeficitCoefficient_spatial_ratio (w φ : ℝ) :
    egbFixedChargeAMeanDeficitCoefficient w φ /
      (egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ) ^ (2 : ℕ) =
      2 * egbFixedChargeAGibbsBarrierCoefficient w φ / egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  rw [egbFixedChargeAMeanDeficitCoefficient_barrier_product]
  field_simp [hc.ne]

theorem egbFixedChargeAMeanGibbsDeficit_squared_distance_quadratic_limit (w φ l : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanGibbsDeficit w φ τ l /
      (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeAMeanRadius w φ τ) ^ (2 : ℕ)) /
      egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (2 * egbFixedChargeAGibbsBarrierCoefficient w φ / egbFixedChargeACriticalRadius w φ ^ (2 : ℕ))) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have hprod : egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ ≠ 0 :=
    (mul_neg_of_pos_of_neg hr hc).ne
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).div
    ((egbFixedChargeAMiddleRadius_mean_quadratic_limit w φ).pow 2) (pow_ne_zero 2 hprod)
  rw [egbFixedChargeAMeanDeficitCoefficient_spatial_ratio] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_distance_cubic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l /
      (egbFixedChargeAMeanRadius w φ τ - egbFixedChargeAMiddleRadius w φ τ) ^ (3 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ /
        (-(egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ)) ^ (3 : ℕ))) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have hprod : 0 < -(egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ) :=
    neg_pos.mpr (mul_neg_of_pos_of_neg hr hc)
  have hgap : Tendsto (fun τ => (egbFixedChargeAMeanRadius w φ τ - egbFixedChargeAMiddleRadius w φ τ) /
      egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (-(egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ))) := by
    convert (egbFixedChargeAMiddleRadius_mean_quadratic_limit w φ).neg using 1
    funext τ
    ring
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).div (hgap.pow 3) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

end GaloisForLFunctions.HTGeometry
