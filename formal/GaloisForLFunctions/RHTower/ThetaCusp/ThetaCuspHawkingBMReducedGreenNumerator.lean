import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedGreenContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceClearedPrincipal

/-! The full undivided numerator of the original unit-amplitude reduced Green response. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def reducedGreenClearingFactor (w chi s : ℂ) : ℂ := -(w-2*s)*connection w chi

/-- Both literal source moments and the source-dependent lift remain in the analytic numerator. -/
def clearedReducedGreen (w chi s a : ℂ) (t : ℝ) : ℂ :=
  let K := reducedGreenGradient chi s 1
  let b := horizonCoordinate t
  (normalizable w chi b*firstEndpointMellin (horizonMellinCore s chi a 1 K) b w+
    horizon w chi b*(∫ r in Ioc b (1:ℝ), normalizable w chi r*sourceProfile s w a 1 K 1 r))*clearedOnset s w+
      connection w chi*radialLift s w a (clearedOnset s w) t

theorem clearedReducedGreen_eq (w chi s a : ℂ) (hs : w-2*s ≠ 0)
    (hc : connection w chi ≠ 0) (t : ℝ) :
    clearedReducedGreen w chi s a t = reducedGreenClearingFactor w chi s*continuedReducedGreen w chi s a 1 t := by
  dsimp [clearedReducedGreen,reducedGreenClearingFactor,continuedReducedGreen,
    continuedTortoiseGreen,continuedResponse,continuedHorizonMoment,continuedOuterMoment,
    radialLift,sourceAmplitude,clearedOnset,continuedOnset]
  field_simp [hs,hc]
  ring

/-- The actual cleared numerator is analytic through both fundamental resonances. -/
theorem clearedReducedGreen_analyticAt (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => clearedReducedGreen v chi s a t) w := by
  let K := reducedGreenGradient chi s 1
  have hb := horizonCoordinate_interior t ht
  have hM := horizonFirstMellin_analyticAt s chi a 1 K w hw hwre hb.1 hb.2
  have hO := (outerSourceIntegral_entire s chi a 1 K hb.1 hb.2).analyticAt w
  have hS := (clearedOnset_entire s).analyticAt w
  have hc := connection_frequency_analyticAt w chi hw
  have hL : AnalyticAt ℂ (fun v => radialLift s v a (clearedOnset s v) t) w := by
    unfold radialLift sourceAmplitude
    fun_prop
  exact ((((normalizable_frequency_entire chi hb).analyticAt w).mul hM).add
    ((horizon_frequency_analyticAt w chi hw hb).mul hO)).mul hS |>.add (hc.mul hL)

/-- At a connection zero the lift contributes no pole numerator; both actual source moments survive. -/
theorem clearedReducedGreen_at_connection_zero (w chi s a : ℂ) (hc : connection w chi = 0) (t : ℝ) :
    clearedReducedGreen w chi s a t =
      (normalizable w chi (horizonCoordinate t)*firstEndpointMellin
        (horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1)) (horizonCoordinate t) w+
       horizon w chi (horizonCoordinate t)*(∫ r in Ioc (horizonCoordinate t) (1:ℝ),
        normalizable w chi r*sourceProfile s w a 1 (reducedGreenGradient chi s 1) 1 r))*clearedOnset s w := by
  simp only [clearedReducedGreen,hc,zero_mul,add_zero]

end
end RHTower.D4BMJointSource
