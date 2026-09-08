import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoordinate
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerJets

/-! The compact exterior radius as an actual smooth function of tortoise time. -/
open Set
namespace RHTower.D4BMJointSource
open D4BMJointWave
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def radialUnit (t : ℝ) : ℝ := -Real.sinh t / Real.cosh t

theorem radialUnit_inverse_radius (t : ℝ) : radialUnit t = (tortoiseRadius t)⁻¹ := by
  simp [radialUnit,tortoiseRadius,inv_div,neg_div]

theorem radialUnit_bounds (t : ℝ) (ht : t < 0) : 0 < radialUnit t ∧ radialUnit t < 1 := by
  rw [radialUnit_inverse_radius]
  have hr := tortoiseRadius_exterior t ht
  exact ⟨inv_pos.mpr (by linarith),(inv_lt_one₀ (by linarith)).mpr hr⟩

theorem radialUnit_add_one_pos (t : ℝ) : 0 < 1+radialUnit t := by
  have hc := Real.cosh_pos t
  have he := Real.cosh_sub_sinh t
  have hp := Real.exp_pos (-t)
  have hid : 1+radialUnit t = (Real.cosh t-Real.sinh t)/Real.cosh t := by
    unfold radialUnit
    field_simp
    ring
  rw [hid]
  exact div_pos (by linarith) hc

theorem radialUnit_hasDerivAt (t : ℝ) :
    HasDerivAt radialUnit (radialUnit t ^ 2-1) t := by
  have hc : Real.cosh t ≠ 0 := ne_of_gt (Real.cosh_pos t)
  convert! ((Real.hasDerivAt_sinh t).neg.div (Real.hasDerivAt_cosh t) hc) using 1
  dsimp only [radialUnit,Pi.neg_apply]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

end
end RHTower.D4BMJointSource
