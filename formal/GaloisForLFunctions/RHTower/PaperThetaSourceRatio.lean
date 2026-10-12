import GaloisForLFunctions.RHTower.PaperThetaPrimitivePair
import GaloisForLFunctions.RHTower.ThetaTailFinitePairTransport
import GaloisForLFunctions.RHTower.ThetaHalfPortStieltjesSpectral

/-! # Monotone source ratios for the literal Fourier mode

The existing finite-pair source ratio extends monotonically over the whole
source line. Every real tilt is integrable, and its character integral is
exactly the original source-relative mode.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource HedenmalmQuantile ThetaFiniteTransport

theorem sourceRatio_normalized (h x : ℝ) :
    sourceRatio h x = thetaSource.normalized (x+h) / thetaSource.normalized x := by
  change thetaCuspFullSource (h+x) / thetaCuspFullSource x =
    (thetaCuspFullSource (x+h) / thetaSource.mass) /
      (thetaCuspFullSource x / thetaSource.mass)
  rw [add_comm h x]
  field_simp [thetaSource.mass_ne_zero]

/-- Global ratio monotonicity, including zero shift, is paid by the native log-slope law. -/
theorem sourceRatio_antitone_all (h : NNReal) : Antitone (sourceRatio h) := by
  apply antitone_of_hasDerivAt_nonpos (sourceRatio_hasDerivAt h)
  intro x
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sub_nonneg.mpr
      (monotone_thetaCuspLogDecaySlope (by linarith [h.coe_nonneg]))))
    (sourceRatio_pos h x).le

/-- Every tilted ratio is integrable, without a strip or source-coordinate restriction. -/
theorem integrable_sourceRatio_tilt (b x : ℝ) :
    Integrable (fun h : ℝ => sourceRatio h x * Real.exp (b*h)) := by
  have ht : Integrable (fun y : ℝ => thetaSource.normalized y * Real.exp (b*y)) := by
    simpa [norm_flatCharDensity] using
      (integrable_flatCharDensity_all (-(b : ℂ)*Complex.I)).norm
  have hs := ((measurePreserving_add_left volume x).integrable_comp_of_integrable ht).const_mul
    (Real.exp (-b*x) / thetaSource.normalized x)
  apply hs.congr
  filter_upwards [] with h
  change (Real.exp (-b*x) / thetaSource.normalized x) *
    (thetaSource.normalized (x+h) * Real.exp (b*(x+h))) = _
  rw [sourceRatio_normalized]
  calc
    _ = (thetaSource.normalized (x+h) / thetaSource.normalized x) *
        (Real.exp (-b*x)*Real.exp (b*(x+h))) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem norm_sourceRatio_character (z : ℂ) (x h : ℝ) :
    ‖(sourceRatio h x : ℂ)*sourceChar z h‖ = sourceRatio h x * Real.exp (-z.im*h) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sourceRatio_pos h x), norm_sourceChar]

theorem integrable_sourceRatio_character (z : ℂ) (x : ℝ) :
    Integrable (fun h : ℝ => (sourceRatio h x : ℂ)*sourceChar z h) := by
  have hc : Continuous (fun h : ℝ => (sourceRatio h x : ℂ)*sourceChar z h) := by
    dsimp [sourceRatio]
    have hk := continuous_thetaCuspFullSource
    have hz := continuous_sourceChar z
    fun_prop
  apply (integrable_sourceRatio_tilt (-z.im) x).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun h => (norm_sourceRatio_character z x h).le

/-- The original quotient is the character integral of the actual monotone source ratio. -/
theorem flatQuotient_eq_sourceRatio_integral (z : ℂ) (x : ℝ) :
    flatQuotient z x + 1 = -(Complex.I*z) *
      ∫ h in Ioi (0 : ℝ), (sourceRatio h x : ℂ)*sourceChar z h := by
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  have hG : flatPrimitiveMode z x = (thetaSource.normalized x : ℂ) *
      ∫ h in Ioi (0 : ℝ), (sourceRatio h x : ℂ)*sourceChar z h := by
    rw [flatPrimitiveMode_shifted, ← integral_Ioi_comp_add
      (fun y : ℝ => (thetaSource.normalized y : ℂ) *
        Complex.exp (Complex.I*z*((y-x : ℝ) : ℂ))) x, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with h
    rw [sourceRatio_normalized, sourceChar, show x+h-x = h by ring]
    push_cast
    field_simp
  rw [flatQuotient, flatMode, hG]
  field_simp
  ring

end RHTower.PaperThetaEndpoint
