import GaloisForLFunctions.RHTower.ThetaQuantileTwoEndedSelector
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceSpectrumExact

/-! # Entire-parameter connection formula for the literal theta mode

All exponential moments of the actual theta source are already proved. They
remove the strip restriction from the flat character, connection and derivative
identities used in logarithmic endpoint admission.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource HedenmalmQuantile HedenmalmPrimeTranslation
  GaloisForLFunctions.HTGeometry

theorem integrable_flatCharDensity_all (z : ℂ) : Integrable (flatCharDensity z) := by
  have h := (integrable_k_sourceChar thetaSource
    (hasShiftedTail_thetaSource_all z)).div_const (thetaSource.mass : ℂ)
  refine h.congr (Eventually.of_forall fun y => ?_)
  rw [flatCharDensity, PositiveDensitySource.normalized]
  push_cast
  ring

theorem flatConnection_eq_all (z : ℂ) :
    flatConnection z = XiC z / (thetaSource.mass : ℂ) := by
  rw [← xiC_thetaSource_all, xiC, flatConnection, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [flatCharDensity, PositiveDensitySource.normalized]
  push_cast
  ring

theorem flatCharDensity_right_integral (z : ℂ) (x : ℝ) :
    ∫ y in Ioi x, flatCharDensity z y =
      flatConnection z - ∫ y in Iic x, flatCharDensity z y := by
  have h := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := x)
    (integrable_flatCharDensity_all z).integrableOn
    (integrable_flatCharDensity_all z).integrableOn
  rw [flatConnection, ← h]
  ring

theorem flatPrimitiveMode_eq_all (z : ℂ) (x : ℝ) :
    flatPrimitiveMode z x = flatConnection z * Complex.exp (-(Complex.I * z) * x) -
      Complex.exp (-(Complex.I * z) * x) * ∫ y in Iic x, flatCharDensity z y := by
  rw [flatPrimitiveMode, flatCharDensity_right_integral]
  ring

theorem hasDerivAt_flatPrimitiveMode_all (z : ℂ) (x : ℝ) :
    HasDerivAt (flatPrimitiveMode z) (flatMode z x) x := by
  have hI := hasDerivAt_setIntegral_Iic (continuous_flatCharDensity z)
    (integrable_flatCharDensity_all z) x
  have he : HasDerivAt (fun x : ℝ => Complex.exp (-(Complex.I * z) * x))
      (-(Complex.I * z) * Complex.exp (-(Complex.I * z) * x)) x := by
    have h := ((hasDerivAt_id (x : ℂ)).const_mul (-(Complex.I * z))).cexp
    simpa [mul_comm] using h.comp_ofReal
  have hfun : flatPrimitiveMode z = fun x : ℝ => Complex.exp (-(Complex.I * z) * x) *
      (flatConnection z - ∫ y in Iic x, flatCharDensity z y) := by
    funext x
    rw [flatPrimitiveMode, flatCharDensity_right_integral]
  rw [hfun]
  refine (he.mul ((hasDerivAt_const x (flatConnection z)).sub hI)).congr_deriv ?_
  change _ = -(Complex.I * z) * flatPrimitiveMode z x - thetaSource.normalized x
  rw [flatPrimitiveMode, flatCharDensity_right_integral, flatCharDensity]
  simp only [Pi.sub_apply]
  linear_combination (-(thetaSource.normalized x : ℂ)) * exp_mul_sourceChar z x

theorem continuous_flatPrimitiveMode_all (z : ℂ) : Continuous (flatPrimitiveMode z) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_flatPrimitiveMode_all z x).continuousAt

theorem continuous_flatMode_all (z : ℂ) : Continuous (flatMode z) :=
  (continuous_const.mul (continuous_flatPrimitiveMode_all z)).sub
    (Complex.continuous_ofReal.comp continuous_normalized_theta)

/-- The zero spectral parameter is an exceptional, exactly normalized mode. -/
theorem flatMode_zero_parameter (x : ℝ) : flatMode 0 x = -(thetaSource.normalized x : ℂ) := by
  simp [flatMode]

end RHTower.PaperThetaEndpoint
