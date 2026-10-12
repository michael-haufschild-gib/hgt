import GaloisForLFunctions.RHTower.PaperThetaExponentialEnvelope

/-! # The exact square-integrable domain over the whole spectral plane

The zero parameter contributes the constant quantile mode. Every other
square-integrable literal quantile mode is exactly on the Xi divisor.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

theorem measurable_pullback_all (z : ℂ) : Measurable (flatModePullback z) :=
  ((continuous_flatMode_all z).measurable.comp thetaSource.measurable_quantileFun).div
    (measurable_metricSymbol thetaSource)

theorem tendsto_scaled_flatMode_norm (z : ℂ) :
    Tendsto (fun x : ℝ => Real.exp (-z.im * x) * ‖flatMode z x‖) atBot
      (𝓝 (‖z‖ * ‖flatConnection z‖)) := by
  simpa only [norm_mul, norm_sourceChar, norm_neg, Complex.norm_I, one_mul]
    using (tendsto_sourceChar_mul_flatMode_atBot_all z).norm

private theorem not_integrable_energy {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    ¬ Integrable (flatModeWeightedDensity z) := by
  intro hint
  have hC : flatConnection z ≠ 0 := by
    rw [flatConnection_eq_all]
    exact div_ne_zero hXi (by exact_mod_cast thetaSource.mass_ne_zero)
  let c : ℝ := ‖z‖ * ‖flatConnection z‖ / 2
  have hc : 0 < c := by positivity
  have hl : c < ‖z‖ * ‖flatConnection z‖ := by dsimp [c] at *; linarith
  have hev1 := (tendsto_scaled_flatMode_norm z).eventually (lt_mem_nhds hl)
  have hev2 := (tendsto_normalized_mul_exp_atBot_all (2 * z.im)).eventually
    (gt_mem_nhds (show 0 < c ^ 2 by positivity))
  obtain ⟨X, hX⟩ := eventually_atBot.1 (hev1.and hev2)
  have hon : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic X) := by
    refine (hint.integrableOn (s := Iic X)).mono' aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun x hx => ?_)
    obtain ⟨h1, h2⟩ := hX x hx
    have hsq : c ^ 2 ≤ (Real.exp (-z.im * x) * ‖flatMode z x‖) ^ 2 :=
      pow_le_pow_left₀ hc.le h1.le 2
    have he : (Real.exp (-z.im * x)) ^ 2 = Real.exp (-(2 * z.im) * x) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, he] at hsq
    have hepos := Real.exp_pos (-(2 * z.im) * x)
    have hlow : thetaSource.normalized x ≤ ‖flatMode z x‖ ^ 2 := by nlinarith
    rw [norm_one, flatModeWeightedDensity, le_div_iff₀ (thetaSource.normalized_pos x), one_mul]
    exact hlow
  rw [integrableOn_const_iff] at hon
  rcases hon with h0 | hfin
  · simp at h0
  · rw [Real.volume_Iic] at hfin
    exact lt_irrefl _ hfin

/-- The zero parameter and the entire Xi divisor are the complete energy domain. -/
theorem integrable_energy_iff_all (z : ℂ) :
    Integrable (flatModeWeightedDensity z) ↔ z = 0 ∨ XiC z = 0 := by
  constructor
  · intro h
    by_cases hz : z = 0
    · exact Or.inl hz
    · exact Or.inr (by_contra fun hXi => not_integrable_energy hz hXi h)
  · rintro (rfl | hXi)
    · refine thetaSource.integrable_normalized.congr (Eventually.of_forall fun x => ?_)
      rw [flatModeWeightedDensity, flatMode_zero_parameter, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (thetaSource.normalized_pos x)]
      field_simp
    · exact integrable_flatModeWeightedDensity_of_zero hXi

/-- Literal quantile L² admission, including the exceptional constant mode. -/
theorem memLp_pullback_iff_all (z : ℂ) :
    MemLp (flatModePullback z) 2 unitIntervalMeasure ↔ z = 0 ∨ XiC z = 0 := by
  have hm := measurable_pullback_all z
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable,
    integrable_unitInterval_iff_cdf (hm.norm.pow_const 2).aestronglyMeasurable,
    ← integrable_energy_iff_all]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  simp only [flatModePullback, smul_eq_mul, flatModeWeightedDensity]
  rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaSource.normalized_pos x)]
  field_simp

end RHTower.PaperThetaEndpoint
