import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedGreenContinuation

/-! Exact source-amplitude linearity, including the restored finite-part horizon moment. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMLaplaceRadial
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem sourceRemainder_scale (s w a J K T c : ℂ) (t : ℝ) :
    sourceRemainder s w a (J*c) (K*c) T t = sourceRemainder s w a J K T t*c := by
  unfold sourceRemainder
  ring

theorem horizonMellinCore_scale (s chi a J K c w : ℂ) (t : ℝ) :
    horizonMellinCore s chi a (J*c) (K*c) w t = horizonMellinCore s chi a J K w t*c := by
  unfold horizonMellinCore
  rw [sourceRemainder_scale]
  ring

/-- Scaling the actual source scales its entire restored endpoint moment, including the subtraction. -/
theorem horizonFirstMellin_scale (s chi a J K c w : ℂ) (b : ℝ) :
    firstEndpointMellin (horizonMellinCore s chi a (J*c) (K*c)) b w =
      firstEndpointMellin (horizonMellinCore s chi a J K) b w*c := by
  unfold firstEndpointMellin firstEndpointMellinRemainder
  simp_rw [horizonMellinCore_scale]
  have he : (fun t : ℝ => (t:ℂ)^w*(horizonMellinCore s chi a J K w t*c-horizonMellinCore s chi a J K w 0*c)) =
      (fun t : ℝ => ((t:ℂ)^w*(horizonMellinCore s chi a J K w t-horizonMellinCore s chi a J K w 0))*c) := by
    funext t
    ring
  rw [he,integral_mul_const]
  ring

/-- The original continued response is exactly linear in its retained angular source amplitudes. -/
theorem continuedResponse_scale (s chi a J K c w : ℂ) (b : ℝ) :
    continuedResponse s chi a (J*c) (K*c) b w = continuedResponse s chi a J K b w*c := by
  have hO : (∫ t in Ioc b (1:ℝ), normalizable w chi t*sourceProfile s w a (J*c) (K*c) 1 t) =
      (∫ t in Ioc b (1:ℝ), normalizable w chi t*sourceProfile s w a J K 1 t)*c := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t
    unfold sourceProfile
    rw [sourceRemainder_scale]
    ring
  unfold continuedResponse continuedHorizonMoment continuedOuterMoment
  rw [horizonFirstMellin_scale,hO]
  ring

end
end RHTower.D4BMLaplaceRadial

namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The continued reduced response keeps exactly its original scalar source amplitude. -/
theorem continuedReducedGreen_amplitude (w chi s a J : ℂ) (t : ℝ) :
    continuedReducedGreen w chi s a J t = J*continuedReducedGreen w chi s a 1 t := by
  have hg : reducedGreenGradient chi s J = reducedGreenGradient chi s 1*J := by
    unfold reducedGreenGradient
    ring
  have hR := continuedResponse_scale s chi a 1 (reducedGreenGradient chi s 1) J w (horizonCoordinate t)
  simp only [one_mul] at hR
  unfold continuedReducedGreen continuedTortoiseGreen
  rw [hg,hR]
  ring

end
end RHTower.D4BMJointSource
