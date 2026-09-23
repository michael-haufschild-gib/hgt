import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGreenAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceAmplitude

/-! Actual tortoise derivatives of the constructed principal radial Green response. -/
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def coordinateFirst (t : ℝ) : ℝ := 2*radialUnit t*horizonCoordinate t
def coordinateSecond (t : ℝ) : ℝ := 2*horizonCoordinate t*(3*radialUnit t^(2 : ℕ)-1)

theorem horizonCoordinate_hasDerivAt (t : ℝ) : HasDerivAt horizonCoordinate (coordinateFirst t) t := by
  apply (((radialUnit_hasDerivAt t).pow 2).const_sub 1).congr_deriv
  dsimp [coordinateFirst,horizonCoordinate]
  ring

theorem coordinateFirst_hasDerivAt (t : ℝ) : HasDerivAt coordinateFirst (coordinateSecond t) t := by
  apply (((radialUnit_hasDerivAt t).const_mul 2).mul (horizonCoordinate_hasDerivAt t)).congr_deriv
  dsimp [coordinateSecond,coordinateFirst,horizonCoordinate]
  ring

def tortoiseGreenFirst (w chi s a J K T : ℂ) (t : ℝ) : ℂ :=
  (coordinateFirst t:ℂ)*responseFirst w chi s a J K T (horizonCoordinate t)

def tortoiseGreenSecond (w chi s a J K T : ℂ) (t : ℝ) : ℂ :=
  (coordinateFirst t:ℂ)^(2 : ℕ)*responseSecond w chi s a J K T (horizonCoordinate t)+
    (coordinateSecond t:ℂ)*responseFirst w chi s a J K T (horizonCoordinate t)

/-- The two displayed tortoise jets are derivatives of the actual endpoint integral response. -/
theorem tortoiseGreen_hasDerivAt {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    (t : ℝ) (ht : t < 0) :
    HasDerivAt (tortoiseGreen w chi s a J K T) (tortoiseGreenFirst w chi s a J K T t) t ∧
      HasDerivAt (tortoiseGreenFirst w chi s a J K T) (tortoiseGreenSecond w chi s a J K T t) t := by
  have hz := horizonCoordinate_interior t ht
  have hd := response_derivatives h s a J K T hz
  have hc := horizonCoordinate_hasDerivAt t
  have hF := hd.1.scomp t hc
  have hF1 := hd.2.scomp t hc
  constructor
  · simpa only [tortoiseGreen,tortoiseGreenFirst,Function.comp_def,Complex.real_smul] using! hF
  · apply (((coordinateFirst_hasDerivAt t).ofReal_comp).mul hF1).congr_deriv
    dsimp only [tortoiseGreenSecond,Function.comp_apply]
    simp only [Complex.real_smul]
    ring

/-- Full actual source profile in compact radius, preserving the original smooth-onset factor. -/
theorem sourceProfile_tortoise (s w a J K T : ℂ) (t : ℝ) (ht : t < 0) :
    sourceProfile s w a J K T (horizonCoordinate t) = sourceAmplitude s w a T t*
      (((5*s^(2 : ℕ)+15*s+4)/4)*J+s*(s-1)*(radialUnit t:ℂ)^(2 : ℕ)/4*((s+2)^(2 : ℕ)*J-K)) := by
  have hr := D4BMJointWave.tortoiseRadius_exterior t ht
  have hr0 : (D4BMJointWave.tortoiseRadius t:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < D4BMJointWave.tortoiseRadius t))
  rw [horizonCoordinate,radialUnit_inverse_radius,sourceProfile_original _ _ _ _ _ _ hr,
    D4BMJointWave.tortoise_original_inverse t ht,sourceAmplitude_original,radialUnit_inverse_radius]
  push_cast
  unfold D4BMQuadraticMixedSource.current
  field_simp
  ring

/-- The two-derivative actual tortoise response solves the original normalized radial wave. -/
theorem tortoiseGreen_equation {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*tortoiseGreen w chi s a J K T t-tortoiseGreenSecond w chi s a J K T t+
      (horizonCoordinate t:ℂ)*(1/4+chi^(2 : ℕ))*tortoiseGreen w chi s a J K T t =
        originalForcing s w a T J K t := by
  have hz := horizonCoordinate_interior t ht
  have hz0 : (horizonCoordinate t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)
  have he := response_equation h s a J K T hz
  have hs : Real.sqrt (1-horizonCoordinate t) = radialUnit t := by
    rw [horizonCoordinate,sub_sub_cancel,Real.sqrt_sq (radialUnit_bounds t ht).1.le]
  rw [hs,sourceProfile_tortoise s w a J K T t ht] at he
  dsimp only [D4BMPhysicalMaster.radialJet] at he
  rw [mul_pow,Complex.I_sq] at he
  field_simp at he
  dsimp only [tortoiseGreen,tortoiseGreenSecond,coordinateFirst,coordinateSecond,originalForcing]
  have hu : (radialUnit t:ℂ)^(2 : ℕ) = 1-(horizonCoordinate t:ℂ) := by
    simp only [horizonCoordinate,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    ring
  push_cast
  simp only [mul_pow,hu] at he ⊢
  linear_combination (-1/8 : ℂ)*he

end
end RHTower.D4BMJointSource
