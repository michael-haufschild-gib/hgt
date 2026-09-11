import GaloisForLFunctions.HTGeometry.ChargedStringTwoSiteModes
import GaloisForLFunctions.HTGeometry.ChargedTwoSiteGrowthMaximum

/-! # An actual exterior-sample charge attaining the coupling-controlled fastest mode -/
namespace GaloisForLFunctions.HTGeometry.CPV
noncomputable section

/-- Charge chosen using the actual positive exterior potential gap. -/
def stringTwoSiteOptimalCharge (k m ell tau x : ℝ) : ℝ :=
  2 * chargedTwoSiteOptimalGap k m / stringTwoSiteGap ell tau x

/-- The constructed maximizing charge is positive for every background and positive sample radius. -/
theorem stringTwoSiteOptimalCharge_pos (k m ell tau x : ℝ) :
    0 < stringTwoSiteOptimalCharge k m ell tau x := by
  unfold stringTwoSiteOptimalCharge chargedTwoSiteOptimalGap
  exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (chargedTwoSiteOptimalGapSquare_pos k m)))
    (stringTwoSiteGap_pos ell tau x)

/-- The actual charged site difference attains the exact optimal gap. -/
theorem stringTwoSiteOptimalCharge_halfGap (k m ell tau x : ℝ) :
    stringTwoSiteHalfGap (stringTwoSiteOptimalCharge k m ell tau x) ell tau x =
      chargedTwoSiteOptimalGap k m := by
  unfold stringTwoSiteHalfGap stringTwoSiteOptimalCharge
  field_simp [(stringTwoSiteGap_pos ell tau x).ne']
  <;> ring

/-- Every exterior potential pair supports an actual nonzero fastest growing state at the constructed charge. -/
theorem stringTwoSiteOptimalCharge_fastest_mode (k m ell tau x : ℝ) :
    ∃ ω : ℂ, ∃ v : ℂ × ℂ, v ≠ 0 ∧
      stringTwoSitePencil k m (stringTwoSiteOptimalCharge k m ell tau x) ell tau x ω v = 0 ∧
      0 < ω.im ∧ ω.im ^ 2 = (Real.exp k) ^ 2 / (4 * chargedTwoSiteBase k m) := by
  obtain ⟨ω, v, hv, hp, hy, hg⟩ := chargedTwoSite_fastest_mode_exists k m
    (stringTwoSiteCenter (stringTwoSiteOptimalCharge k m ell tau x) ell tau x)
  refine ⟨ω, v, hv, ?_, hy, hg⟩
  unfold stringTwoSitePencil
  rw [stringTwoSiteOptimalCharge_halfGap]
  exact hp

end
end GaloisForLFunctions.HTGeometry.CPV
