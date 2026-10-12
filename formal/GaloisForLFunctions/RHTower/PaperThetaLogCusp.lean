import GaloisForLFunctions.RHTower.PaperThetaEntireEnergy
import GaloisForLFunctions.RHTower.ThetaArithmeticTerminalCusp

/-! # The exact logarithmic cusp scale of the literal quantile mode

The coefficient is the actual theta cusp constant π. No atom is truncated and
the logarithm retains the original normalized source denominator.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

theorem normalized_div_envelope_tendsto :
    Tendsto (fun x : ℝ => thetaSource.normalized x / thetaEnvelope x) atTop
      (𝓝 (4 * Real.pi ^ 2 / thetaSource.mass)) := by
  refine (thetaCuspFullSource_div_envelope_tendsto.div_const thetaSource.mass).congr
    fun x => ?_
  simp only [PositiveDensitySource.normalized, thetaSource_k]
  ring

theorem tendsto_exp_neg_two_mul :
    Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))

theorem tendsto_exp_two_mul_atBot :
    Tendsto (fun x : ℝ => Real.exp (2 * x)) atBot (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by norm_num))

theorem tendsto_mul_exp_two_atBot :
    Tendsto (fun x : ℝ => x * Real.exp (2 * x)) atBot (𝓝 0) := by
  have h := (tendsto_mul_exp_neg_mul_atTop (by norm_num : (0 : ℝ) < 2)).comp
    tendsto_neg_atBot_atTop
  simpa only [Function.comp_apply, mul_neg, neg_neg, neg_mul, neg_zero]
    using h.neg

/-- Exact logarithmic source asymptotic at the positive cusp. -/
theorem tendsto_scaled_log_normalized_atTop :
    Tendsto (fun x : ℝ => Real.exp (-2 * x) * Real.log (thetaSource.normalized x))
      atTop (𝓝 (-Real.pi)) := by
  have hlog := normalized_div_envelope_tendsto.log
    (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ Real.pi_ne_zero)) thetaSource.mass_ne_zero)
  have h0 := tendsto_exp_neg_two_mul.mul hlog
  have hlin := (tendsto_mul_exp_neg_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_mul (9 / 2)
  have h := (h0.add hlin).sub (tendsto_const_nhds (x := Real.pi))
  simp only [zero_mul, mul_zero, add_zero, zero_sub] at h
  refine h.congr fun x => ?_
  rw [Real.log_div (thetaSource.normalized_pos x).ne' (thetaEnvelope_pos x).ne',
    thetaEnvelope, Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp]
  have he : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simp only [neg_mul] at he ⊢
  linear_combination Real.pi * he

/-- Reflection keeps the same exact logarithmic cusp constant. -/
theorem tendsto_scaled_log_normalized_atBot :
    Tendsto (fun x : ℝ => Real.exp (2 * x) * Real.log (thetaSource.normalized x))
      atBot (𝓝 (-Real.pi)) := by
  have h := tendsto_scaled_log_normalized_atTop.comp tendsto_neg_atBot_atTop
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, neg_mul, mul_neg, neg_neg, PositiveDensitySource.normalized,
    thetaSource_even]

private theorem scaled_log_of_scaled_limit {f : ℝ → ℝ} {a c : ℝ}
    (hf : ∀ x, 0 < f x) (hc : c ≠ 0)
    (h : Tendsto (fun x => Real.exp (-a * x) * f x) atBot (𝓝 c)) :
    Tendsto (fun x => Real.exp (2 * x) * Real.log (f x)) atBot (𝓝 0) := by
  have h0 := tendsto_exp_two_mul_atBot.mul (h.log hc)
  have hlin := tendsto_mul_exp_two_atBot.const_mul a
  have ht := h0.add hlin
  simp only [zero_mul, mul_zero, add_zero] at ht
  refine ht.congr fun x => ?_
  rw [Real.log_mul (Real.exp_ne_zero _) (hf x).ne', Real.log_exp]
  ring

/-- Off the exceptional zero coefficient, the quantile logarithm grows as π exp(-2x). -/
theorem tendsto_scaled_mode_log {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    Tendsto (fun x : ℝ => Real.exp (2 * x) *
      Real.log (2 + ‖flatMode z x‖ / thetaSource.normalized x)) atBot (𝓝 Real.pi) := by
  have hC : flatConnection z ≠ 0 := by
    rw [flatConnection_eq_all]
    exact div_ne_zero hXi (by exact_mod_cast thetaSource.mass_ne_zero)
  have hc : ‖z‖ * ‖flatConnection z‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.mpr hz)
    (norm_ne_zero_iff.mpr hC)
  have hplus : Tendsto (fun x : ℝ => Real.exp (-z.im * x) *
      (‖flatMode z x‖ + 2 * thetaSource.normalized x)) atBot
        (𝓝 (‖z‖ * ‖flatConnection z‖)) := by
    have h := (tendsto_scaled_flatMode_norm z).add
      ((tendsto_normalized_mul_exp_atBot_all z.im).const_mul 2)
    simp only [mul_zero, add_zero] at h
    exact h.congr fun x => by ring
  have hpos : ∀ x, 0 < ‖flatMode z x‖ + 2 * thetaSource.normalized x := fun x => by
    have := thetaSource.normalized_pos x
    positivity
  have hlog := scaled_log_of_scaled_limit hpos hc hplus
  have h := hlog.sub tendsto_scaled_log_normalized_atBot
  simp only [zero_sub, neg_neg] at h
  refine h.congr fun x => ?_
  have hρ := thetaSource.normalized_pos x
  rw [← mul_sub, ← Real.log_div (by positivity) hρ.ne']
  congr 2
  field_simp
  ring

end RHTower.PaperThetaEndpoint
