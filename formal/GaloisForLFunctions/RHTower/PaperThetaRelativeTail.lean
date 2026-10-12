import GaloisForLFunctions.RHTower.PaperThetaEntireTails

/-! # Source-relative right tails of the literal theta mode

Matching upper and lower theta envelopes control the actual quotient by the
source, even though that source vanishes faster than every exponential.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

def flatQuotient (z : ℂ) (x : ℝ) : ℂ :=
  flatMode z x / (thetaSource.normalized x : ℂ)

theorem continuous_flatQuotient (z : ℂ) : Continuous (flatQuotient z) :=
  (continuous_flatMode_all z).div
    (Complex.continuous_ofReal.comp continuous_normalized_theta)
    (fun x => by exact_mod_cast (thetaSource.normalized_pos x).ne')

private theorem primitive_le_relative_envelope (z : ℂ) {x : ℝ} (hx : 1 ≤ x)
    (hr : 0 < Real.pi * Real.exp (2 * x) + z.im) :
    ‖flatPrimitiveMode z x‖ ≤
      (thetaEnvelopeUpper / thetaSource.mass * thetaEnvelope x) *
        (1 / (Real.pi * Real.exp (2 * x) + z.im)) := by
  let K := thetaEnvelopeUpper / thetaSource.mass * thetaEnvelope x
  let r := Real.pi * Real.exp (2 * x) + z.im
  have hb : ∀ y ∈ Ioi x, Real.exp (z.im * x) * ‖flatCharDensity z y‖ ≤
      K * Real.exp (-r * (y - x)) := by
    intro y hy
    have hρ : thetaSource.normalized y ≤
        K * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := by
      have hs := thetaCuspFullSource_le_shift hx (le_of_lt hy)
      change thetaSource.k y / thetaSource.mass ≤ _
      rw [div_le_iff₀ thetaSource.mass_pos]
      calc
        thetaSource.k y ≤ (thetaEnvelopeUpper * thetaEnvelope x) *
            Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x)) := hs
        _ = _ := by dsimp [K]; field_simp [thetaSource.mass_ne_zero]
    rw [norm_flatCharDensity]
    calc
      _ ≤ Real.exp (z.im * x) *
          ((K * Real.exp (-(Real.pi * Real.exp (2 * x)) * (y - x))) *
            Real.exp (-z.im * y)) := by gcongr
      _ = K * Real.exp (-r * (y - x)) := by
        rw [mul_left_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        dsimp [r]
        ring
  calc
    ‖flatPrimitiveMode z x‖ = Real.exp (z.im * x) *
        ‖∫ y in Ioi x, flatCharDensity z y‖ := by
      rw [flatPrimitiveMode, norm_mul, norm_exp_neg_I_mul]
    _ ≤ ∫ y in Ioi x, Real.exp (z.im * x) * ‖flatCharDensity z y‖ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_nonneg _)
    _ ≤ ∫ y in Ioi x, K * Real.exp (-r * (y - x)) :=
      setIntegral_mono_on ((integrable_flatCharDensity_all z).norm.integrableOn.const_mul _)
        ((integrableOn_exp_neg_shift hr).const_mul K) measurableSet_Ioi hb
    _ = K * (1 / r) := by rw [integral_const_mul, integral_Ioi_exp_neg_shift hr]

private theorem primitive_quotient_le (z : ℂ) {x : ℝ} (hx : 1 ≤ x)
    (hr : 0 < Real.pi * Real.exp (2 * x) + z.im) :
    ‖flatPrimitiveMode z x‖ / thetaSource.normalized x ≤
      (thetaEnvelopeUpper / thetaEnvelopeLower) /
        (Real.pi * Real.exp (2 * x) + z.im) := by
  have hl : thetaEnvelopeLower / thetaSource.mass * thetaEnvelope x ≤ thetaSource.normalized x := by
    have h := thetaCuspFullSource_ge_envelope (show 0 < x by linarith)
    change _ ≤ thetaSource.k x / thetaSource.mass
    rw [le_div_iff₀ thetaSource.mass_pos]
    calc
      _ = thetaEnvelopeLower * thetaEnvelope x := by field_simp [thetaSource.mass_ne_zero]
      _ ≤ _ := h
  have hL : 0 < thetaEnvelopeLower / thetaSource.mass * thetaEnvelope x :=
    mul_pos (div_pos thetaEnvelopeLower_pos thetaSource.mass_pos) (thetaEnvelope_pos x)
  have hU : 0 ≤ (thetaEnvelopeUpper / thetaSource.mass * thetaEnvelope x) *
      (1 / (Real.pi * Real.exp (2 * x) + z.im)) := by
    exact mul_nonneg (mul_pos (div_pos thetaEnvelopeUpper_pos thetaSource.mass_pos)
      (thetaEnvelope_pos x)).le (one_div_pos.mpr hr).le
  calc
    _ ≤ ((thetaEnvelopeUpper / thetaSource.mass * thetaEnvelope x) *
        (1 / (Real.pi * Real.exp (2 * x) + z.im))) /
          (thetaEnvelopeLower / thetaSource.mass * thetaEnvelope x) :=
      div_le_div₀ hU (primitive_le_relative_envelope z hx hr) hL hl
    _ = _ := by
      field_simp [thetaSource.mass_ne_zero, thetaEnvelopeLower_pos.ne',
        (thetaEnvelope_pos x).ne', hr.ne']

theorem tendsto_theta_relative_rate (z : ℂ) :
    Tendsto (fun x : ℝ => Real.pi * Real.exp (2 * x) + z.im) atTop atTop :=
  ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).const_mul_atTop
    Real.pi_pos).atTop_add (tendsto_const_nhds (x := z.im))

/-- The primitive is negligible relative to the actual source at the right end. -/
theorem tendsto_primitive_quotient_norm_atTop (z : ℂ) :
    Tendsto (fun x : ℝ => ‖flatPrimitiveMode z x‖ / thetaSource.normalized x)
      atTop (𝓝 0) := by
  have hlim := (tendsto_theta_relative_rate z).inv_tendsto_atTop.const_mul
    (thetaEnvelopeUpper / thetaEnvelopeLower)
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun x =>
    div_nonneg (norm_nonneg _) (thetaSource.normalized_pos x).le) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_theta_relative_rate z).eventually_gt_atTop 0]
    with x hx hr
  simpa only [Pi.inv_apply, div_eq_mul_inv] using primitive_quotient_le z hx hr

/-- Every complex parameter has the same normalized right boundary trace. -/
theorem tendsto_flatQuotient_atTop (z : ℂ) :
    Tendsto (flatQuotient z) atTop (𝓝 (-1)) := by
  have hg : Tendsto (fun x : ℝ => flatPrimitiveMode z x / (thetaSource.normalized x : ℂ))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (thetaSource.normalized_pos _)] using tendsto_primitive_quotient_norm_atTop z
  have h := (hg.const_mul (-(Complex.I * z))).sub_const 1
  simp only [mul_zero, zero_sub] at h
  refine h.congr fun x => ?_
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  dsimp [flatQuotient, flatMode]
  field_simp

end RHTower.PaperThetaEndpoint
