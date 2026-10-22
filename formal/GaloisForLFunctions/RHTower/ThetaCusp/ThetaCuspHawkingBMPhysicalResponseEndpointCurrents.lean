import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalResponseDerivativeBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceOuterModeLimits
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalResponseGreenTransport

/-! Both endpoint current conditions are consequences of the actual complete physical response. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual physical current against the original horizon mode vanishes at the horizon. -/
theorem physicalCuspModeCurrent_horizon_zero (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    Tendsto (physicalCuspModeCurrent q r branch w a hw hd hwi hwr false) atBot (𝓝 0) := by
  obtain ⟨C,_,hP⟩ := physicalCuspProfile_bounded q r branch w a hw hd hwi hwr
  obtain ⟨D,_,hD⟩ := physicalCuspProfile_deriv_bounded q r branch w a hw hd hwi hwr
  have hc := physicalRadialFrequency_chamber r w (by linarith)
  have hH := tortoiseHorizon_tendsto_horizon hc
  have hH' := tortoiseHorizonFirst_tendsto_horizon hc
  have hz : Tendsto (fun t => ‖tortoiseModeFirst false w (physicalRadialFrequency r) t‖*C+
      ‖tortoiseMode false w (physicalRadialFrequency r) t‖*D) atBot (𝓝 0) := by
    simpa only [norm_zero,zero_mul,zero_add] using (hH'.norm.mul_const C).add (hH.norm.mul_const D)
  apply squeeze_zero_norm' ?_ hz
  filter_upwards [eventually_lt_atBot (0:ℝ)] with t ht
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (hP t) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (hD t ht) (norm_nonneg _))

/-- The actual physical current against the normalizable mode vanishes at the original outer endpoint. -/
theorem physicalCuspModeCurrent_boundary_zero (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    Tendsto (physicalCuspModeCurrent q r branch w a hw hd hwi hwr true) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  obtain ⟨D,_,hD⟩ := physicalCuspProfile_deriv_bounded q r branch w a hw hd hwi hwr
  have hc := physicalRadialFrequency_chamber r w (by linarith)
  have hN := tortoiseNormalizable_boundary hc
  have hN' := tortoiseNormalizableFirst_boundary hc
  have hP := physicalCuspProfile_boundary q r branch w a hw hd hwi hwr
  have hprod : Tendsto (fun t => tortoiseMode true w (physicalRadialFrequency r) t*
      deriv (physicalCuspProfile q r branch w a hw hd hwi hwr) t) (𝓝[<] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (show Tendsto
      (fun t => ‖tortoiseMode true w (physicalRadialFrequency r) t‖*D) (𝓝[<] (0:ℝ)) (𝓝 0) from by
        simpa only [norm_zero,zero_mul] using hN.norm.mul_const D)
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hD t ht) (norm_nonneg _)
  simpa only [physicalCuspModeCurrent,mul_zero,sub_zero] using! (hN'.mul hP).sub hprod

end
end RHTower.D4BMJointSource
