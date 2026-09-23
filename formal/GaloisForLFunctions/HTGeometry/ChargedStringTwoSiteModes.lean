import GaloisForLFunctions.HTGeometry.ChargedStringTwoSiteGeometry
import GaloisForLFunctions.HTGeometry.ChargedTwoSiteVarianceDefect

/-!
# Actual charged-string samples in the finite wave equation

The two site values are the existing charged-string potential at positive exterior
radii r and2r. Mode claims concern this exact finite operator, not the continuum PDE.
-/
namespace GaloisForLFunctions.HTGeometry.CPV
noncomputable section

/-- Mean charged electrostatic site frequency. -/
def stringTwoSiteCenter (e ell tau x : ℝ) : ℝ :=
  e * ((stringTwoSitePotential ell tau x).1 + (stringTwoSitePotential ell tau x).2) / 2

/-- Half the actual charged potential difference. -/
def stringTwoSiteHalfGap (e ell tau x : ℝ) : ℝ := e * stringTwoSiteGap ell tau x / 2

/-- The exact two-site wave pencil for actual exterior potential samples. -/
def stringTwoSitePencil (k m e ell tau x : ℝ) (ω : ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  chargedTwoSitePencil k m (stringTwoSiteCenter e ell tau x) (stringTwoSiteHalfGap e ell tau x) ω

/-- Nonzero modes of the actual sampled-potential wave operator. -/
def StringTwoSiteHasMode (k m e ell tau x : ℝ) (ω : ℂ) : Prop :=
  ChargedTwoSiteHasMode k m (stringTwoSiteCenter e ell tau x) (stringTwoSiteHalfGap e ell tau x) ω

/-- The charged half-gap has its exact variance-scale value. -/
theorem stringTwoSiteHalfGap_sq (e ell tau x : ℝ) :
    stringTwoSiteHalfGap e ell tau x ^ (2 : ℕ) = e ^ (2 : ℕ) * stringTwoSiteGap ell tau x ^ (2 : ℕ) / 4 := by
  unfold stringTwoSiteHalfGap
  ring

/-- The concrete operator uses the original site potentials, without a substitute variance budget. -/
theorem stringTwoSitePencil_apply (k m e ell tau x : ℝ) (ω : ℂ) (v : ℂ × ℂ) :
    stringTwoSitePencil k m e ell tau x ω v =
      ((((chargedTwoSiteBase k m : ℝ) : ℂ) -
        (ω - ((e * (stringTwoSitePotential ell tau x).1 : ℝ) : ℂ)) ^ (2 : ℕ)) * v.1 - (Real.exp k : ℂ) * v.2,
      (((chargedTwoSiteBase k m : ℝ) : ℂ) -
        (ω - ((e * (stringTwoSitePotential ell tau x).2 : ℝ) : ℂ)) ^ (2 : ℕ)) * v.2 - (Real.exp k : ℂ) * v.1) := by
  have h0 : stringTwoSiteCenter e ell tau x + stringTwoSiteHalfGap e ell tau x =
      e * (stringTwoSitePotential ell tau x).1 := by
    unfold stringTwoSiteCenter stringTwoSiteHalfGap stringTwoSiteGap
    ring
  have h1 : stringTwoSiteCenter e ell tau x - stringTwoSiteHalfGap e ell tau x =
      e * (stringTwoSitePotential ell tau x).2 := by
    unfold stringTwoSiteCenter stringTwoSiteHalfGap stringTwoSiteGap
    ring
  unfold stringTwoSitePencil
  rw [chargedTwoSitePencil_apply, h0, h1]

/-- Actual growing frequencies have the exact midpoint and unique growth branch for these exterior samples. -/
theorem stringTwoSite_growing_frequency_classification (k m e ell tau x : ℝ) (ω : ℂ) :
    (StringTwoSiteHasMode k m e ell tau x ω ∧ 0 < ω.im) ↔
      ω.re = stringTwoSiteCenter e ell tau x ∧ 0 < ω.im ∧
        ω.im ^ (2 : ℕ) = chargedTwoSiteGrowthSquare k m (stringTwoSiteHalfGap e ell tau x) :=
  chargedTwoSite_growing_frequency_classification k m _ _ ω

/-- The entire actual string-sample instability window is exactly the two strict charge-gap inequalities. -/
theorem stringTwoSite_exists_growing_mode_iff (k m e ell tau x : ℝ) :
    (∃ ω : ℂ, StringTwoSiteHasMode k m e ell tau x ω ∧ 0 < ω.im) ↔
      m ^ (2 : ℕ) < e ^ (2 : ℕ) * stringTwoSiteGap ell tau x ^ (2 : ℕ) / 4 ∧
        e ^ (2 : ℕ) * stringTwoSiteGap ell tau x ^ (2 : ℕ) / 4 < m ^ (2 : ℕ) + 2 * Real.exp k := by
  unfold StringTwoSiteHasMode
  rw [chargedTwoSite_exists_growing_mode_iff, stringTwoSiteHalfGap_sq]

/-- Temperature controls the actual charged half-gap with the sharp doubled-radius geometric coefficient. -/
theorem stringTwoSiteHalfGap_temperature_bound (e ell tau x : ℝ) :
    stringTwoSiteHalfGap e ell tau x ^ (2 : ℕ) ≤
      e ^ (2 : ℕ) * (1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell) / 64 := by
  rw [stringTwoSiteHalfGap_sq]
  have h := mul_le_mul_of_nonneg_left (stringTwoSiteGap_temperature_bound ell tau x) (sq_nonneg e)
  nlinarith

/-- No actual growing mode reaches the temperature-calibrated upper squared growth bound. -/
theorem stringTwoSite_no_growth_at_temperature_bound (k m e ell tau x : ℝ) :
    ¬ ∃ ω : ℂ, StringTwoSiteHasMode k m e ell tau x ω ∧ 0 < ω.im ∧
      e ^ (2 : ℕ) * (1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell) / 64 ≤ ω.im ^ (2 : ℕ) := by
  rintro ⟨ω, hm, hy, hb⟩
  apply chargedTwoSite_no_growth_at_or_above_variance k m
    (stringTwoSiteCenter e ell tau x) (stringTwoSiteHalfGap e ell tau x)
  exact ⟨ω, hm, hy, (stringTwoSiteHalfGap_temperature_bound e ell tau x).trans hb⟩

end
end GaloisForLFunctions.HTGeometry.CPV
