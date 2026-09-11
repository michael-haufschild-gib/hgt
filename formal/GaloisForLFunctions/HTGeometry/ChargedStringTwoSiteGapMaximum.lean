import GaloisForLFunctions.HTGeometry.ChargedStringTwoSiteGeometry

/-! # An actual positive exterior radius attaining the sharp electrostatic gap -/
namespace GaloisForLFunctions.HTGeometry.CPV
noncomputable section

/-- Logarithmic radius coordinate of the exact half-attenuation point. -/
def stringTwoSiteOptimalRadiusCoordinate (ell : ℝ) : ℝ := Real.log (Real.log 2 / Real.exp ell)

/-- The maximizing sample is an actual positive exterior radius. -/
theorem stringTwoSiteOptimalRadius_value (ell : ℝ) :
    Real.exp (stringTwoSiteOptimalRadiusCoordinate ell) = Real.log 2 / Real.exp ell := by
  exact Real.exp_log (div_pos (Real.log_pos (by norm_num)) (Real.exp_pos ell))

/-- The explicit maximizing radius attains half attenuation exactly. -/
theorem stringTwoSiteAttenuation_at_optimal (ell : ℝ) :
    stringTwoSiteAttenuation ell (stringTwoSiteOptimalRadiusCoordinate ell) = 1 / 2 := by
  unfold stringTwoSiteAttenuation
  rw [stringTwoSiteOptimalRadius_value]
  have he : -Real.exp ell * (Real.log 2 / Real.exp ell) = -Real.log 2 := by
    field_simp [(Real.exp_pos ell).ne']
    <;> ring
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Every thermal background attains the sharp electrostatic gap on its actual exterior geometry. -/
theorem stringTwoSiteGap_at_optimal (ell tau : ℝ) :
    stringTwoSiteGap ell tau (stringTwoSiteOptimalRadiusCoordinate ell) = coherentRadius tau / 4 :=
  (stringTwoSiteGap_maximum_iff ell tau _).2 (stringTwoSiteAttenuation_at_optimal ell)

/-- The gap maximizer also attains the exact temperature-calibrated squared bound. -/
theorem stringTwoSiteGap_at_optimal_temperature (ell tau : ℝ) :
    stringTwoSiteGap ell tau (stringTwoSiteOptimalRadiusCoordinate ell) ^ 2 =
      (1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell) / 16 := by
  rw [stringTwoSiteGap_at_optimal]
  have ht := stringBlackHole_charge_temperature ell tau
  nlinarith

end
end GaloisForLFunctions.HTGeometry.CPV
