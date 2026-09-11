import GaloisForLFunctions.HTGeometry.ChargedStringThermalOccupation

/-! # Sharp electrostatic gap for two actual exterior string-black-hole sites -/
namespace GaloisForLFunctions.HTGeometry.CPV
noncomputable section

/-- Exponential attenuation at an automatically positive exterior radius. -/
def stringTwoSiteAttenuation (ell x : ℝ) : ℝ := Real.exp (-Real.exp ell * Real.exp x)

/-- The actual charged-string potential sampled at radii r and 2r. -/
def stringTwoSitePotential (ell tau x : ℝ) : ℝ × ℝ :=
  (stringBlackHolePotential ell tau (Real.exp x), stringBlackHolePotential ell tau (2 * Real.exp x))

/-- Electrostatic potential difference of these actual exterior samples. -/
def stringTwoSiteGap (ell tau x : ℝ) : ℝ :=
  (stringTwoSitePotential ell tau x).1 - (stringTwoSitePotential ell tau x).2

/-- Both the positive radius and positive decay rate force attenuation strictly inside the unit interval. -/
theorem stringTwoSiteAttenuation_bounds (ell x : ℝ) :
    0 < stringTwoSiteAttenuation ell x ∧ stringTwoSiteAttenuation ell x < 1 := by
  constructor
  · exact Real.exp_pos _
  · unfold stringTwoSiteAttenuation
    apply Real.exp_lt_one_iff.mpr
    have h := mul_pos (Real.exp_pos ell) (Real.exp_pos x)
    linarith

/-- Doubling the exterior radius squares the attenuation of the actual potential. -/
theorem stringTwoSitePotential_formula (ell tau x : ℝ) :
    stringTwoSitePotential ell tau x =
      (coherentRadius tau * stringTwoSiteAttenuation ell x,
        coherentRadius tau * stringTwoSiteAttenuation ell x ^ 2) := by
  have h : Real.exp (-Real.exp ell * (2 * Real.exp x)) =
      Real.exp (-Real.exp ell * Real.exp x) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply Prod.ext
  · rfl
  · change coherentRadius tau * _ = coherentRadius tau * _
    rw [h]
    rfl

/-- The actual two-site potential gap is a scaled concave quadratic in attenuation. -/
theorem stringTwoSiteGap_formula (ell tau x : ℝ) :
    stringTwoSiteGap ell tau x = coherentRadius tau * stringTwoSiteAttenuation ell x *
      (1 - stringTwoSiteAttenuation ell x) := by
  unfold stringTwoSiteGap
  rw [stringTwoSitePotential_formula]
  dsimp
  ring

/-- Distinct positive exterior radii produce a strictly positive electrostatic gap. -/
theorem stringTwoSiteGap_pos (ell tau x : ℝ) : 0 < stringTwoSiteGap ell tau x := by
  rw [stringTwoSiteGap_formula]
  exact mul_pos (mul_pos (coherentRadius_pos tau) (stringTwoSiteAttenuation_bounds ell x).1)
    (sub_pos.mpr (stringTwoSiteAttenuation_bounds ell x).2)

/-- The exact nonnegative defect exposes the sharp quarter-radius gap bound. -/
theorem stringTwoSiteGap_defect (ell tau x : ℝ) :
    coherentRadius tau / 4 - stringTwoSiteGap ell tau x =
      coherentRadius tau * (stringTwoSiteAttenuation ell x - 1 / 2) ^ 2 := by
  rw [stringTwoSiteGap_formula]
  ring

/-- The doubled-radius electrostatic gap is at most one quarter of the horizon potential. -/
theorem stringTwoSiteGap_le_quarter (ell tau x : ℝ) :
    stringTwoSiteGap ell tau x ≤ coherentRadius tau / 4 := by
  have hd := stringTwoSiteGap_defect ell tau x
  have hn := mul_nonneg (coherentRadius_pos tau).le (sq_nonneg (stringTwoSiteAttenuation ell x - 1 / 2))
  linarith

/-- Equality in the sharp gap bound occurs exactly at half attenuation. -/
theorem stringTwoSiteGap_maximum_iff (ell tau x : ℝ) :
    stringTwoSiteGap ell tau x = coherentRadius tau / 4 ↔ stringTwoSiteAttenuation ell x = 1 / 2 := by
  constructor
  · intro h
    have hd := stringTwoSiteGap_defect ell tau x
    have hs : (stringTwoSiteAttenuation ell x - 1 / 2) ^ 2 = 0 := by
      have hp : coherentRadius tau * (stringTwoSiteAttenuation ell x - 1 / 2) ^ 2 = 0 := by linarith
      exact (mul_eq_zero.mp hp).resolve_left (coherentRadius_pos tau).ne'
    have hz := sq_eq_zero_iff.mp hs
    linarith
  · intro h
    rw [stringTwoSiteGap_formula, h]
    ring

/-- The exact charge-temperature identity bounds the squared electrostatic gap. -/
theorem stringTwoSiteGap_temperature_bound (ell tau x : ℝ) :
    stringTwoSiteGap ell tau x ^ 2 ≤
      (1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell) / 16 := by
  have hb := stringTwoSiteGap_le_quarter ell tau x
  have hp := stringTwoSiteGap_pos ell tau x
  have ha := coherentRadius_pos tau
  have hn := mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ coherentRadius tau / 4 + stringTwoSiteGap ell tau x by linarith)
  have ht := stringBlackHole_charge_temperature ell tau
  nlinarith

end
end GaloisForLFunctions.HTGeometry.CPV
