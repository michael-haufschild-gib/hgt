import GaloisForLFunctions.RHTower.PaperThetaEntireMode

/-! # Every exponential rate for the actual normalized theta source

The double-exponential cusp supplies a global majorant at any real rate. No
spectral strip or moment premise is needed.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

def exponentialEnvelopeConstant (b : ℝ) : ℝ :=
  thetaEnvelopeUpper / thetaSource.mass * Real.exp ((b + 9 / 2) ^ 2)

theorem exponentialEnvelopeConstant_pos (b : ℝ) : 0 < exponentialEnvelopeConstant b :=
  mul_pos (div_pos thetaEnvelopeUpper_pos thetaSource.mass_pos) (Real.exp_pos _)

private theorem envelope_le_exponential (b : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    thetaEnvelope x ≤ Real.exp ((b + 9 / 2) ^ 2) * Real.exp (-b * x) := by
  rw [thetaEnvelope, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by linarith)
  have hp : Real.exp (2 * x) ≤ Real.pi * Real.exp (2 * x) :=
    le_mul_of_one_le_left (Real.exp_nonneg _) (by linarith [Real.pi_gt_three])
  nlinarith [sq_nonneg (b + 9 / 2 - x)]

/-- Every real exponential rate has an explicit global source majorant. -/
theorem normalized_le_exponential (b x : ℝ) :
    thetaSource.normalized x ≤ exponentialEnvelopeConstant b * Real.exp (-b * |x|) := by
  have hk : thetaSource.k x ≤ thetaEnvelopeUpper * thetaEnvelope |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      exact thetaCuspFullSource_le_envelope hx
    · rw [abs_of_nonpos hx, ← thetaSource_even x]
      exact thetaCuspFullSource_le_envelope (by linarith)
  have h := hk.trans (mul_le_mul_of_nonneg_left (envelope_le_exponential b (abs_nonneg x))
    thetaEnvelopeUpper_pos.le)
  change thetaSource.k x / thetaSource.mass ≤ _
  rw [div_le_iff₀ thetaSource.mass_pos]
  calc
    thetaSource.k x ≤ thetaEnvelopeUpper *
        (Real.exp ((b + 9 / 2) ^ 2) * Real.exp (-b * |x|)) := h
    _ = exponentialEnvelopeConstant b * Real.exp (-b * |x|) * thetaSource.mass := by
      unfold exponentialEnvelopeConstant
      field_simp [thetaSource.mass_ne_zero]

/-- The left source cusp beats every exponential tilt, with no rate restriction. -/
theorem tendsto_normalized_mul_exp_atBot_all (a : ℝ) :
    Tendsto (fun x : ℝ => thetaSource.normalized x * Real.exp (-a * x)) atBot (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => exponentialEnvelopeConstant (a + 1) * Real.exp x)
      atBot (𝓝 0) := by
    simpa using Real.tendsto_exp_atBot.const_mul (exponentialEnvelopeConstant (a + 1))
  refine squeeze_zero' (Eventually.of_forall fun x =>
    mul_nonneg (thetaSource.normalized_pos x).le (Real.exp_nonneg _)) ?_ hlim
  filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
  have h := mul_le_mul_of_nonneg_right (normalized_le_exponential (a + 1) x)
    (Real.exp_nonneg (-a * x))
  rw [abs_of_nonpos hx] at h
  calc
    _ ≤ exponentialEnvelopeConstant (a + 1) * Real.exp (-(a + 1) * -x) *
        Real.exp (-a * x) := h
    _ = exponentialEnvelopeConstant (a + 1) * Real.exp x := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem tendsto_sourceChar_mul_normalized_atBot_all (z : ℂ) :
    Tendsto (fun x : ℝ => HedenmalmQuantile.sourceChar z x *
      (thetaSource.normalized x : ℂ)) atBot (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_mul, HedenmalmQuantile.norm_sourceChar, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (thetaSource.normalized_pos _), mul_comm]
    using tendsto_normalized_mul_exp_atBot_all z.im

/-- Exact left connection limit for every complex spectral parameter. -/
theorem tendsto_sourceChar_mul_flatMode_atBot_all (z : ℂ) :
    Tendsto (fun x : ℝ => HedenmalmQuantile.sourceChar z x * flatMode z x) atBot
      (𝓝 (-(Complex.I * z) * flatConnection z)) := by
  have hI := tendsto_setIntegral_Iic_atBot (integrable_flatCharDensity_all z)
  have h1 := ((tendsto_const_nhds (x := flatConnection z)).sub hI).const_mul (-(Complex.I * z))
  have h2 := h1.sub (tendsto_sourceChar_mul_normalized_atBot_all z)
  simp only [sub_zero] at h2
  refine h2.congr fun x => ?_
  rw [flatMode, flatPrimitiveMode_eq_all]
  linear_combination (Complex.I * z * (flatConnection z -
    ∫ y in Iic x, flatCharDensity z y)) * exp_mul_sourceChar z x

end RHTower.PaperThetaEndpoint
