import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourcePrincipalContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceJetHolomorphy

/-! Explicit analytic numerators of the original principal differences and their first spatial jets. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The undivided numerator of the literal smooth-onset transform. -/
def clearedOnset (s w : ℂ) : ℂ := 1+(w-2*s)*onsetCorrection (2*s) w

def principalClearingFactor (q : XiZeroCopy) (branch : Bool) (w : ℂ) (i : Fin 3) : ℂ :=
  -(w-2*physicalRate q branch)*connection w (principalFrequency q i)

/-- Explicit undivided Green/lift numerator; its value at a pole is defined by the analytic formula. -/
def clearedPrincipalDifference (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3) (t : ℝ) : ℂ :=
  let s := physicalRate q branch
  let chi := principalFrequency q i
  let J := principalAmplitude q i
  let K := principalGradient q branch i
  let b := horizonCoordinate t
  (normalizable w chi b*firstEndpointMellin (horizonMellinCore s chi a J K) b w+
    horizon w chi b*(∫ r in Ioc b (1:ℝ), normalizable w chi r*sourceProfile s w a J K 1 r))*clearedOnset s w+
      connection w chi*radialLift s w a (clearedOnset s w) t*J

/-- The original first spatial jet with the same source and connection denominators cleared. -/
def clearedPrincipalDifferenceFirst (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3) (t : ℝ) : ℂ :=
  let s := physicalRate q branch
  let chi := principalFrequency q i
  let J := principalAmplitude q i
  let K := principalGradient q branch i
  let b := horizonCoordinate t
  (coordinateFirst t:ℂ)*(normalizableFirst w chi b*firstEndpointMellin (horizonMellinCore s chi a J K) b w+
    horizonFirst w chi b*(∫ r in Ioc b (1:ℝ), normalizable w chi r*sourceProfile s w a J K 1 r))*clearedOnset s w+
      connection w chi*radialLiftFirst s w a (clearedOnset s w) t*J

/-- The exact original denominator clears the principal response away from its zeros. -/
theorem clearedPrincipalDifference_eq (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3)
    (hs : w-2*physicalRate q branch ≠ 0) (hc : connection w (principalFrequency q i) ≠ 0) (t : ℝ) :
    clearedPrincipalDifference q branch w a i t =
      principalClearingFactor q branch w i*continuedPrincipalDifference q branch w a i t := by
  dsimp [clearedPrincipalDifference,principalClearingFactor,continuedPrincipalDifference,
    continuedTortoiseGreen,continuedResponse,continuedHorizonMoment,continuedOuterMoment,
    radialLift,sourceAmplitude,clearedOnset,continuedOnset]
  field_simp [hs,hc]
  ring

/-- The first-jet identity uses the same clearing factor, before taking a frequency limit. -/
theorem clearedPrincipalDifferenceFirst_eq (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (i : Fin 3)
    (hs : w-2*physicalRate q branch ≠ 0) (hc : connection w (principalFrequency q i) ≠ 0) (t : ℝ) :
    clearedPrincipalDifferenceFirst q branch w a i t =
      principalClearingFactor q branch w i*continuedPrincipalDifferenceFirst q branch w a i t := by
  dsimp [clearedPrincipalDifferenceFirst,principalClearingFactor,continuedPrincipalDifferenceFirst,
    continuedTortoiseGreenFirst,continuedResponseFirst,continuedHorizonMoment,continuedOuterMoment,
    radialLiftFirst,sourceAmplitude,clearedOnset,continuedOnset]
  field_simp [hs,hc]
  ring

/-- Clearing the source pole retains its entire smooth-onset numerator. -/
theorem clearedOnset_entire (s : ℂ) : Differentiable ℂ (clearedOnset s) := by
  intro w
  have hc : DifferentiableAt ℂ (fun _ : ℂ => (1:ℂ)) w := differentiableAt_const 1
  exact hc.add ((differentiableAt_id.sub_const (2*s)).mul ((onsetCorrection_entire (2*s)) w))

/-- Both actual undivided principal jets are analytic in frequency throughout the continued strip. -/
theorem clearedPrincipalDifference_analyticAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun u => clearedPrincipalDifference q branch u a i t) w ∧
      AnalyticAt ℂ (fun u => clearedPrincipalDifferenceFirst q branch u a i t) w := by
  let s := physicalRate q branch
  let chi := principalFrequency q i
  let J := principalAmplitude q i
  let K := principalGradient q branch i
  have hb := horizonCoordinate_interior t ht
  have hM := horizonFirstMellin_analyticAt s chi a J K w hw hwre hb.1 hb.2
  have hO := (outerSourceIntegral_entire s chi a J K hb.1 hb.2).analyticAt w
  have hS := (clearedOnset_entire s).analyticAt w
  have hc := connection_frequency_analyticAt w chi hw
  have hL : AnalyticAt ℂ (fun u => radialLift s u a (clearedOnset s u) t) w := by
    unfold radialLift sourceAmplitude
    fun_prop
  have hL1 : AnalyticAt ℂ (fun u => radialLiftFirst s u a (clearedOnset s u) t) w := by
    unfold radialLiftFirst sourceAmplitude liftFirstPolynomial amplitudeRate
    fun_prop
  constructor
  · exact ((((normalizable_frequency_entire chi hb).analyticAt w).mul hM).add
      ((horizon_frequency_analyticAt w chi hw hb).mul hO)).mul hS |>.add
        ((hc.mul hL).mul analyticAt_const)
  · exact (analyticAt_const.mul ((((normalizableFirst_frequency_entire chi hb).analyticAt w).mul hM).add
      ((horizonFirst_frequency_analyticAt w chi hw hb).mul hO))).mul hS |>.add
        ((hc.mul hL1).mul analyticAt_const)

end
end RHTower.D4BMJointSource
