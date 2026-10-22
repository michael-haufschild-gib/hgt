import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceContinuedForcedODE
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceGreenTortoiseJets

/-! The original continued radial response in the actual tortoise chart. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The fixed smooth-onset transform with its original source pole continued. -/
def continuedOnset (s w : ℂ) : ℂ := 1/(w-2*s)+onsetCorrection (2*s) w

/-- The existing continued native response evaluated in the original tortoise chart. -/
def continuedTortoiseGreen (w chi s a J K : ℂ) (t : ℝ) : ℂ :=
  continuedResponse s chi a J K (horizonCoordinate t) w

def continuedTortoiseGreenFirst (w chi s a J K : ℂ) (t : ℝ) : ℂ :=
  (coordinateFirst t:ℂ)*continuedResponseFirst s chi a J K (horizonCoordinate t) w

def continuedTortoiseGreenSecond (w chi s a J K : ℂ) (t : ℝ) : ℂ :=
  (coordinateFirst t:ℂ)^(2 : ℕ)*continuedResponseSecond s chi a J K (horizonCoordinate t) w+
    (coordinateSecond t:ℂ)*continuedResponseFirst s chi a J K (horizonCoordinate t) w

/-- The continued chart response agrees with the original causal Green response in its source chamber. -/
theorem continuedTortoiseGreen_eq_original (w chi s a J K : ℂ) (hw : w.im ≠ 0)
    (hwre : -1 < w.re) (hs : (2*s).re < w.re) (t : ℝ) (ht : t < 0) :
    continuedTortoiseGreen w chi s a J K t =
      tortoiseGreen w chi s a J K (onsetTransform (2*s) w) t := by
  have hb := horizonCoordinate_interior t ht
  exact continuedResponse_eq_original s chi a J K w hw hwre hs hb.1 hb.2

/-- The actual chart pullback retains frequency meromorphy throughout the continued strip. -/
theorem continuedTortoiseGreen_meromorphicAt (w chi s a J K : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (t : ℝ) (ht : t < 0) :
    MeromorphicAt (fun u => continuedTortoiseGreen u chi s a J K t) w := by
  have hb := horizonCoordinate_interior t ht
  exact continuedResponse_meromorphicAt s chi a J K w hw hwre hb.1 hb.2

/-- Both chart jets are derivatives of the actual continued endpoint response. -/
theorem continuedTortoiseGreen_hasDerivAt (w chi s a J K : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (t : ℝ) (ht : t < 0) :
    HasDerivAt (continuedTortoiseGreen w chi s a J K) (continuedTortoiseGreenFirst w chi s a J K t) t ∧
      HasDerivAt (continuedTortoiseGreenFirst w chi s a J K) (continuedTortoiseGreenSecond w chi s a J K t) t := by
  have hd := continuedResponse_hasDerivAt s chi a J K w hw hwre (horizonCoordinate_interior t ht)
  have hc := horizonCoordinate_hasDerivAt t
  have hF := hd.1.scomp t hc
  have hF1 := hd.2.scomp t hc
  constructor
  · simpa only [continuedTortoiseGreen,continuedTortoiseGreenFirst,Function.comp_def,Complex.real_smul] using! hF
  · apply (((coordinateFirst_hasDerivAt t).ofReal_comp).mul hF1).congr_deriv
    dsimp only [continuedTortoiseGreenSecond,Function.comp_apply]
    simp only [Complex.real_smul]
    ring

/-- The continued original response solves the literal tortoise wave off the actual connection zeros. -/
theorem continuedTortoiseGreen_equation (w chi s a J K : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (hc : connection w chi ≠ 0) (t : ℝ) (ht : t < 0) :
    w^(2 : ℕ)*continuedTortoiseGreen w chi s a J K t-continuedTortoiseGreenSecond w chi s a J K t+
      (horizonCoordinate t:ℂ)*(1/4+chi^(2 : ℕ))*continuedTortoiseGreen w chi s a J K t =
        originalForcing s w a (continuedOnset s w) J K t := by
  have hz := horizonCoordinate_interior t ht
  have hz0 : (horizonCoordinate t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)
  have he := continuedResponse_original_equation s chi a J K w hw hwre hc hz
  obtain ⟨hd,hdd⟩ := continuedResponse_deriv_eq s chi a J K w hw hwre hz
  rw [hd,hdd] at he
  have hs : Real.sqrt (1-horizonCoordinate t) = radialUnit t := by
    rw [horizonCoordinate,sub_sub_cancel,Real.sqrt_sq (radialUnit_bounds t ht).1.le]
  rw [hs,continuedSourceProfile,sourceProfile_tortoise s w a J K _ t ht] at he
  dsimp only [D4BMPhysicalMaster.radialJet] at he
  rw [mul_pow,Complex.I_sq] at he
  field_simp at he
  dsimp only [continuedTortoiseGreen,continuedTortoiseGreenSecond,coordinateFirst,coordinateSecond,originalForcing,continuedOnset]
  have hu : (radialUnit t:ℂ)^(2 : ℕ) = 1-(horizonCoordinate t:ℂ) := by
    simp only [horizonCoordinate,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    ring
  push_cast
  simp only [mul_pow,hu] at he ⊢
  linear_combination (-1/8 : ℂ)*he

end
end RHTower.D4BMJointSource
