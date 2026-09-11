import GaloisForLFunctions.HTGeometry.ChargedStringTwoSiteGapMaximum
import GaloisForLFunctions.HTGeometry.ChargedStringTwoSiteModes
import GaloisForLFunctions.HTGeometry.ChargedTwoSiteStrongCoupling

/-! # Actual growing modes approaching the sharp thermal growth ceiling -/
namespace GaloisForLFunctions.HTGeometry.CPV
noncomputable section
open Filter

/-- Positive charged half-gap at the exact gap-maximizing exterior radius. -/
def stringTwoSiteThermalGap (h ell tau : ℝ) : ℝ :=
  stringTwoSiteHalfGap (Real.exp h) ell tau (stringTwoSiteOptimalRadiusCoordinate ell)

/-- Corresponding charged midpoint frequency. -/
def stringTwoSiteThermalCenter (h ell tau : ℝ) : ℝ :=
  stringTwoSiteCenter (Real.exp h) ell tau (stringTwoSiteOptimalRadiusCoordinate ell)

/-- Temperature-calibrated upper bound on squared growth. -/
def stringTwoSiteThermalGrowthCeiling (h ell tau : ℝ) : ℝ :=
  (Real.exp h) ^ 2 * (1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell) / 64

/-- An explicit sequence of finite positive couplings, all within the massless instability window. -/
def stringTwoSiteThermalLimitCoupling (h ell tau : ℝ) (j : ℕ) : ℝ :=
  chargedTwoSiteStrongCoupling (stringTwoSiteThermalGap h ell tau) j

/-- Actual candidate frequency at every stage of the coupling path. -/
def stringTwoSiteThermalLimitFrequency (h ell tau : ℝ) (j : ℕ) : ℂ :=
  chargedTwoSiteGrowingFrequency (stringTwoSiteThermalLimitCoupling h ell tau j) 0
    (stringTwoSiteThermalCenter h ell tau) (stringTwoSiteThermalGap h ell tau)

/-- Explicit two-site state for the actual frequency path. -/
def stringTwoSiteThermalLimitVector (h ell tau : ℝ) (j : ℕ) : ℂ × ℂ :=
  chargedTwoSiteModeVector (stringTwoSiteThermalLimitCoupling h ell tau j) 0
    (stringTwoSiteThermalCenter h ell tau) (stringTwoSiteThermalGap h ell tau)
    (stringTwoSiteThermalLimitFrequency h ell tau j)

/-- The fixed charged half-gap is strictly positive on every thermal background. -/
theorem stringTwoSiteThermalGap_pos (h ell tau : ℝ) : 0 < stringTwoSiteThermalGap h ell tau := by
  unfold stringTwoSiteThermalGap stringTwoSiteHalfGap
  exact div_pos (mul_pos (Real.exp_pos h) (stringTwoSiteGap_pos ell tau _)) (by norm_num)

/-- The squared selected gap is exactly the temperature-calibrated ceiling. -/
theorem stringTwoSiteThermalGap_sq (h ell tau : ℝ) :
    stringTwoSiteThermalGap h ell tau ^ 2 = stringTwoSiteThermalGrowthCeiling h ell tau := by
  unfold stringTwoSiteThermalGap
  rw [stringTwoSiteHalfGap_sq, stringTwoSiteGap_at_optimal_temperature]
  unfold stringTwoSiteThermalGrowthCeiling
  ring

/-- The limiting thermal ceiling is positive for every finite thermal parameter. -/
theorem stringTwoSiteThermalGrowthCeiling_pos (h ell tau : ℝ) :
    0 < stringTwoSiteThermalGrowthCeiling h ell tau := by
  rw [← stringTwoSiteThermalGap_sq]
  exact sq_pos_of_pos (stringTwoSiteThermalGap_pos h ell tau)

/-- Every stage is an actual growing mode of the original sampled-potential operator. -/
theorem stringTwoSiteThermalLimitFrequency_mode (h ell tau : ℝ) (j : ℕ) :
    StringTwoSiteHasMode (stringTwoSiteThermalLimitCoupling h ell tau j) 0 (Real.exp h) ell tau
      (stringTwoSiteOptimalRadiusCoordinate ell) (stringTwoSiteThermalLimitFrequency h ell tau j) ∧
        0 < (stringTwoSiteThermalLimitFrequency h ell tau j).im :=
  (chargedTwoSiteStrongCoupling_growing_iff (stringTwoSiteThermalCenter h ell tau)
    (stringTwoSiteThermalGap h ell tau) j).2 (stringTwoSiteThermalGap_pos h ell tau).ne'

/-- The displayed state is nonzero and solves the exact wave equation at every finite coupling. -/
theorem stringTwoSiteThermalLimitVector_mode (h ell tau : ℝ) (j : ℕ) :
    stringTwoSiteThermalLimitVector h ell tau j ≠ 0 ∧
      stringTwoSitePencil (stringTwoSiteThermalLimitCoupling h ell tau j) 0 (Real.exp h) ell tau
        (stringTwoSiteOptimalRadiusCoordinate ell) (stringTwoSiteThermalLimitFrequency h ell tau j)
        (stringTwoSiteThermalLimitVector h ell tau j) = 0 ∧
          0 < (stringTwoSiteThermalLimitFrequency h ell tau j).im := by
  have hm := stringTwoSiteThermalLimitFrequency_mode h ell tau j
  have hd := (chargedTwoSiteHasMode_iff_determinant (stringTwoSiteThermalLimitCoupling h ell tau j) 0
    (stringTwoSiteThermalCenter h ell tau) (stringTwoSiteThermalGap h ell tau) _).1 hm.1
  refine ⟨chargedTwoSiteModeVector_ne_zero _ _ _ _ _, ?_, hm.2⟩
  change chargedTwoSitePencil (stringTwoSiteThermalLimitCoupling h ell tau j) 0
    (stringTwoSiteThermalCenter h ell tau) (stringTwoSiteThermalGap h ell tau)
    (stringTwoSiteThermalLimitFrequency h ell tau j)
    (chargedTwoSiteModeVector (stringTwoSiteThermalLimitCoupling h ell tau j) 0
      (stringTwoSiteThermalCenter h ell tau) (stringTwoSiteThermalGap h ell tau)
      (stringTwoSiteThermalLimitFrequency h ell tau j)) = 0
  rw [chargedTwoSiteModeVector_residual, hd]
  rfl

/-- Actual squared growth along the frequency path equals the exact algebraic branch. -/
theorem stringTwoSiteThermalLimitFrequency_growth (h ell tau : ℝ) (j : ℕ) :
    (stringTwoSiteThermalLimitFrequency h ell tau j).im ^ 2 =
      chargedTwoSiteGrowthSquare (stringTwoSiteThermalLimitCoupling h ell tau j) 0
        (stringTwoSiteThermalGap h ell tau) :=
  ((chargedTwoSite_growing_frequency_classification (stringTwoSiteThermalLimitCoupling h ell tau j) 0
    (stringTwoSiteThermalCenter h ell tau) (stringTwoSiteThermalGap h ell tau) _).1
      (stringTwoSiteThermalLimitFrequency_mode h ell tau j)).2.2

/-- Actual growing-mode rates tend to the sharp thermal ceiling. -/
theorem stringTwoSiteThermalLimitFrequency_growth_limit (h ell tau : ℝ) :
    Tendsto (fun j => (stringTwoSiteThermalLimitFrequency h ell tau j).im ^ 2) atTop
      (nhds (stringTwoSiteThermalGrowthCeiling h ell tau)) := by
  simp only [stringTwoSiteThermalLimitFrequency_growth]
  change Tendsto (fun j => chargedTwoSiteGrowthSquare
    (chargedTwoSiteStrongCoupling (stringTwoSiteThermalGap h ell tau) j) 0
    (stringTwoSiteThermalGap h ell tau)) atTop (nhds (stringTwoSiteThermalGrowthCeiling h ell tau))
  simpa only [stringTwoSiteThermalGap_sq] using chargedTwoSiteStrongCoupling_growth_limit
    (stringTwoSiteThermalGap h ell tau)

/-- Every finite-coupling mode stays strictly below the limiting ceiling. -/
theorem stringTwoSiteThermalLimitFrequency_growth_lt (h ell tau : ℝ) (j : ℕ) :
    (stringTwoSiteThermalLimitFrequency h ell tau j).im ^ 2 < stringTwoSiteThermalGrowthCeiling h ell tau := by
  have hm := stringTwoSiteThermalLimitFrequency_mode h ell tau j
  by_contra hn
  have hb : stringTwoSiteThermalGrowthCeiling h ell tau ≤
      (stringTwoSiteThermalLimitFrequency h ell tau j).im ^ 2 := by linarith
  exact stringTwoSite_no_growth_at_temperature_bound (stringTwoSiteThermalLimitCoupling h ell tau j) 0
    (Real.exp h) ell tau (stringTwoSiteOptimalRadiusCoordinate ell)
    ⟨stringTwoSiteThermalLimitFrequency h ell tau j, hm.1, hm.2, hb⟩

end
end GaloisForLFunctions.HTGeometry.CPV
