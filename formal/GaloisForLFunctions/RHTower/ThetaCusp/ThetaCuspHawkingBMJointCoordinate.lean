import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointRadialCore
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMIngoingCoordinates

/-! Identification of the joint energy weight with the actual original tortoise vector field. -/
open Set
namespace RHTower.D4BMJointWave
noncomputable section

/-- Exterior radius in the negative tortoise coordinate. -/
def tortoiseRadius (t : ℝ) : ℝ := -Real.cosh t / Real.sinh t

theorem tortoiseRadius_exterior (t : ℝ) (ht : t < 0) : 1 < tortoiseRadius t := by
  have hs : Real.sinh t < 0 := Real.sinh_neg_iff.mpr ht
  rw [tortoiseRadius,lt_div_iff_of_neg hs]
  have hp := Real.exp_pos t
  have he := Real.cosh_add_sinh t
  linarith

/-- Radial differentiation is the original vector field (r²−1)∂r. -/
theorem tortoiseRadius_hasDerivAt (t : ℝ) (ht : t < 0) :
    HasDerivAt tortoiseRadius ((tortoiseRadius t)^(2 : ℕ)-1) t := by
  have hs : Real.sinh t ≠ 0 := ne_of_lt (Real.sinh_neg_iff.mpr ht)
  have hc := Real.cosh_sq_sub_sinh_sq t
  convert! ((Real.hasDerivAt_cosh t).neg.div (Real.hasDerivAt_sinh t) hs) using 1
  dsimp only [tortoiseRadius,Pi.neg_apply]
  field_simp
  nlinarith

/-- The constructed radius is an exact inverse of the original logarithmic tortoise coordinate. -/
theorem tortoise_original_inverse (t : ℝ) (ht : t < 0) :
    D4BMIngoingCoordinates.tortoise (tortoiseRadius t) = t := by
  have hs : Real.sinh t ≠ 0 := ne_of_lt (Real.sinh_neg_iff.mpr ht)
  have hr := tortoiseRadius_exterior t ht
  have hm : tortoiseRadius t - 1 ≠ 0 := by linarith
  have hp : tortoiseRadius t + 1 ≠ 0 := by linarith
  have hminus : tortoiseRadius t - 1 = -Real.exp t / Real.sinh t := by
    rw [← Real.cosh_add_sinh]
    unfold tortoiseRadius
    field_simp
    ring
  have hplus : tortoiseRadius t + 1 = -Real.exp (-t) / Real.sinh t := by
    rw [← Real.cosh_sub_sinh]
    unfold tortoiseRadius
    field_simp
    ring
  have hratio : (tortoiseRadius t-1)/(tortoiseRadius t+1) = Real.exp (2*t) := by
    rw [hminus,hplus]
    calc
      _ = Real.exp t / Real.exp (-t) := by field_simp
      _ = Real.exp (2*t) := by rw [← Real.exp_sub]; congr 1; ring
  rw [D4BMIngoingCoordinates.tortoise,← Real.log_div hm hp,hratio,Real.log_exp]
  ring

/-- The original static-to-ingoing tortoise has unit derivative along the constructed radius. -/
theorem originalTortoise_radius_derivative (t : ℝ) (ht : t < 0) :
    HasDerivAt (fun x => D4BMIngoingCoordinates.tortoise (tortoiseRadius x)) 1 t := by
  have hr := tortoiseRadius_exterior t ht
  have hn : (tortoiseRadius t)^(2 : ℕ)-1 ≠ 0 := by nlinarith
  convert! (D4BMIngoingCoordinates.tortoise_hasDerivAt _ hr).comp t
    (tortoiseRadius_hasDerivAt t ht) using 1
  exact (inv_mul_cancel₀ hn).symm

/-- The squared weight in the joint angular energy is exactly the original stream-wave coefficient. -/
theorem angularWeight_original_coefficient (t : ℝ) (ht : t < 0) :
    angularWeight t ^ (2 : ℕ) =
      (((tortoiseRadius t : ℝ) : ℂ)^(2 : ℕ)-1) / ((tortoiseRadius t : ℝ) : ℂ)^(2 : ℕ) := by
  have hs : Real.sinh t ≠ 0 := ne_of_lt (Real.sinh_neg_iff.mpr ht)
  have hc : Real.cosh t ≠ 0 := ne_of_gt (Real.cosh_pos t)
  have he : ((Real.cosh t)⁻¹)^(2 : ℕ) = ((tortoiseRadius t)^(2 : ℕ)-1)/(tortoiseRadius t)^(2 : ℕ) := by
    unfold tortoiseRadius
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  change (((Real.cosh t)⁻¹ : ℝ) : ℂ)^(2 : ℕ) = _
  exact_mod_cast he

end
end RHTower.D4BMJointWave
