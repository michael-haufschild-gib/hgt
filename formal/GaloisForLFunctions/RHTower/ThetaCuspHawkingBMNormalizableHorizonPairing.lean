import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingPairingFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOppositePairingFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalNormalizableHorizonDomain

/-! The original normalizable horizon pairing with both derived endpoint subtractions. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The original incoming cutoff integral and its two power counterterms. -/
def incomingPairingCutoff (s chi a J K : ℂ) (b : ℝ) (w : ℂ) (e : ℝ) : ℂ :=
  (∫ z in e..b, continuedResponse s chi a J K z w*horizon w chi z/
    (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))+
  (incomingResponseEndpoint s chi a J K w b/2)*(e:ℂ)^w/w+
  ((horizonGaussFirstCoefficient w chi+1/4)*incomingResponseEndpoint s chi a J K w b+
    incomingResponseSlope s a J K w/2)*(e:ℂ)^(w+1)/(w+1)

/-- The original opposite cutoff integral and its logarithmic counterterm. -/
def oppositePairingCutoff (s chi a J K : ℂ) (b : ℝ) (w : ℂ) (e : ℝ) : ℂ :=
  (∫ z in e..b, (connection w chi/(2*w))*(continuedResponse s chi a J K z w*horizon (-w) chi z/
    (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))))+
  (connection w chi/(2*w))*(incomingResponseEndpoint s chi a J K w b/2)*(Real.log e:ℂ)

/-- Both original horizon branches, with their actual Wronskian coefficients. -/
def normalizableHorizonPairingFinitePart (s chi a J K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)*
    incomingPairingFinitePart s chi a J K b w+oppositePairingFinitePart s chi a J K b w

/-- The single original normalizable-mode integral with all three derived counterterms. -/
def normalizableHorizonPairingCutoff (s chi a J K : ℂ) (b : ℝ) (w : ℂ) (e : ℝ) : ℂ :=
  (∫ z in e..b, continuedResponse s chi a J K z w*normalizable w chi z/
    (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))+
  horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)*
    ((incomingResponseEndpoint s chi a J K w b/2)*(e:ℂ)^w/w+
      ((horizonGaussFirstCoefficient w chi+1/4)*incomingResponseEndpoint s chi a J K w b+
        incomingResponseSlope s a J K w/2)*(e:ℂ)^(w+1)/(w+1))+
  (connection w chi/(2*w))*(incomingResponseEndpoint s chi a J K w b/2)*(Real.log e:ℂ)

private theorem horizonPairing_intervalIntegrable (s chi a J K w v : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) {e b : ℝ} (he : 0 < e) (heb : e ≤ b) (hb : b < 1) :
    IntervalIntegrable (fun z : ℝ => continuedResponse s chi a J K z w*horizon v chi z/
      (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))) volume e b := by
  apply ContinuousOn.intervalIntegrable
  intro z hz
  rw [uIcc_of_le heb] at hz
  have hzI : z ∈ Ioo (0:ℝ) 1 := ⟨he.trans_le hz.1,hz.2.trans_lt hb⟩
  have hU := (continuedResponse_hasDerivAt s chi a J K w hw hwr hzI).1.continuousAt
  have hH := (horizon_derivatives_continued (w := v) (chi := chi) hzI).1.continuousAt
  exact ((hU.mul hH).div (by fun_prop)
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hzI.1.ne'))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hzI.2)))))).continuousWithinAt

/-- Before either endpoint limit, the actual normalizable integral splits into its two original horizon branches. -/
theorem normalizableHorizonPairingCutoff_eq (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) {e b : ℝ} (he : 0 < e) (heb : e ≤ b) (hb : b < 1) :
    normalizableHorizonPairingCutoff s chi a J K b w e=
      horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)*
        incomingPairingCutoff s chi a J K b w e+oppositePairingCutoff s chi a J K b w e := by
  let A := horizonRegularCoefficient w chi (normalizable w chi) (normalizableFirst w chi)
  let C := connection w chi/(2*w)
  have hI := horizonPairing_intervalIntegrable s chi a J K w w hw hwr he heb hb
  have hO := horizonPairing_intervalIntegrable s chi a J K w (-w) hw hwr he heb hb
  have hsplit : (∫ z in e..b, continuedResponse s chi a J K z w*normalizable w chi z/
      (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))=
      A*(∫ z in e..b, continuedResponse s chi a J K z w*horizon w chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)))+
      C*(∫ z in e..b, continuedResponse s chi a J K z w*horizon (-w) chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hI.const_mul A) (hO.const_mul C)]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le heb] at hz
    have hzI : z ∈ Ioo (0:ℝ) 1 := ⟨he.trans_le hz.1,hz.2.trans_lt hb⟩
    have hn := (original_homogeneous_horizon_representation w chi hw
      (fun t ht => (normalizable_derivatives_continued ht).1)
      (fun t ht => (normalizable_derivatives_continued ht).2)
      (fun t ht => normalizable_equation_continued ht) hzI).1
    rw [normalizable_opposite_coefficient w chi hw] at hn
    dsimp only
    rw [hn]
    dsimp only [A,C]
    ring
  unfold normalizableHorizonPairingCutoff incomingPairingCutoff oppositePairingCutoff
  rw [hsplit,intervalIntegral.integral_const_mul]
  dsimp only [A,C]
  ring

end
end RHTower.D4BMLaplaceRadial
