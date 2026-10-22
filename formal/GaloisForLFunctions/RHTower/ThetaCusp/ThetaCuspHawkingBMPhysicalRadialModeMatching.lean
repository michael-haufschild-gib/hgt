import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalResponseClassical
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceHorizonModeJets

/-! Original horizon modes match the actual physical angular parameter and its classical response operator. -/
open Complex Set Filter MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The radial frequency of the original physical angular testing field. -/
def physicalRadialFrequency (r : XiZeroCopy) : ℂ := -I*physicalAngularParameter r

theorem physicalRadialFrequency_eq (r : XiZeroCopy) :
    physicalRadialFrequency r = thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint r) := by
  unfold physicalRadialFrequency physicalAngularParameter
  rw [neg_mul,← mul_assoc,← pow_two,Complex.I_sq,neg_one_mul,neg_neg]

/-- The actual angular eigenvalue matches the original radial hypergeometric parameter exactly. -/
theorem physicalRadialFrequency_parameter (r : XiZeroCopy) :
    1/4+physicalRadialFrequency r^(2 : ℕ) = -(physicalAngularParameter r^(2 : ℕ)-1/4) := by
  unfold physicalRadialFrequency
  rw [mul_pow,neg_sq,Complex.I_sq]
  ring

/-- The physical angular parameter lies in the original connection-nonzero chamber throughout the response overlap. -/
theorem physicalRadialFrequency_chamber (r : XiZeroCopy) (w : ℂ) (hw : 1/2 < w.re) :
    Chamber w (physicalRadialFrequency r) := by
  have hr := xi_divisor_support_re_mem_open_unit r.1
  change |(physicalRadialFrequency r).im| < w.re
  rw [physicalRadialFrequency,physicalAngularParameter_eq]
  simp only [neg_mul,Complex.neg_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_add,Complex.div_ofNat_re,Complex.sub_re,Complex.one_re]
  apply (abs_lt.mpr ?_).trans hw
  constructor <;> linarith [hr.1,hr.2]

/-- Both original homogeneous modes have the same radial coefficient as the actual projected response. -/
theorem physicalTortoiseMode_hasDerivAt (r : XiZeroCopy) (w : ℂ) (hw : 1/2 < w.re)
    (outer : Bool) (t : ℝ) (ht : t < 0) :
    HasDerivAt (tortoiseMode outer w (physicalRadialFrequency r))
      (tortoiseModeFirst outer w (physicalRadialFrequency r) t) t ∧
    HasDerivAt (tortoiseModeFirst outer w (physicalRadialFrequency r))
      ((w^(2 : ℕ)-(physicalAngularParameter r^(2 : ℕ)-1/4)*angularWeight t^(2 : ℕ))*
        tortoiseMode outer w (physicalRadialFrequency r) t) t := by
  have hc := physicalRadialFrequency_chamber r w hw
  have h := tortoiseMode_hasDerivAt hc outer t ht
  refine ⟨h.1,h.2.congr_deriv ?_⟩
  rw [tortoiseMode_equation hc outer t ht,physicalRadialFrequency_parameter,horizonCoordinate_jointWeight t ht]
  ring

end
end RHTower.D4BMJointSource
