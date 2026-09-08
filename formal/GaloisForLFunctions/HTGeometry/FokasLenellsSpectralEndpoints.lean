import GaloisForLFunctions.HTGeometry.FokasLenellsGlobalSmallScattering

/-!
# Reflection vanishes at both positive spectral endpoints

The reciprocal estimates (3.15)–(3.17) in Yan–Zhang–Zhu,
arXiv:2607.19649v1, give two explicit exponential envelopes in the logarithmic
spectral parameter. For every Schwartz potential, both reflection numerators
tend to zero as the positive spectral parameter tends to zero or infinity.
The limits are proved from the constructed scattering data, not assumed
scattering regularity.

For the globally normalized potentials, the transmission lower bound carries
these two endpoint limits to both reflection quotients. No transmission
asymptotic, spectral continuity, or nonlinear reconstruction is asserted.
-/

open Complex Matrix Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The two explicit endpoint decay envelopes behind the reciprocal minimum in (3.17). -/
theorem reflectionAmplitude_exponential_envelopes (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    ‖reflectionAmplitude q κ‖ ≤ (2*potentialScatteringError q)*Real.exp κ ∧
    ‖reflectionAmplitude q κ‖ ≤ (potentialScatteringError q/2)*Real.exp (-κ) := by
  have hb := reflectionAmplitude_reciprocal_bounds q κ
  have hp : 0 < 2*Real.exp κ := by positivity
  constructor
  · have he := (div_le_iff₀ hp).mp hb.2
    nlinarith
  · have he : ‖reflectionAmplitude q κ‖ ≤ potentialScatteringError q/(2*Real.exp κ) := by
      apply (le_div_iff₀ hp).mpr
      simpa only [mul_comm] using hb.1
    refine he.trans_eq ?_
    rw [Real.exp_neg]
    ring

/-- The original reflection numerator vanishes at high positive spectral frequency. -/
theorem reflectionAmplitude_tendsto_high (q : SchwartzMap ℝ ℂ) :
    Tendsto (reflectionAmplitude q) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hh : Tendsto (fun κ => (potentialScatteringError q/2)*Real.exp (-κ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (potentialScatteringError q/2)
  exact squeeze_zero (fun κ => norm_nonneg _) (fun κ => (reflectionAmplitude_exponential_envelopes q κ).2) hh

/-- The original reflection numerator also vanishes as the positive spectral parameter approaches zero. -/
theorem reflectionAmplitude_tendsto_low (q : SchwartzMap ℝ ℂ) :
    Tendsto (reflectionAmplitude q) atBot (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hl : Tendsto (fun κ => (2*potentialScatteringError q)*Real.exp κ) atBot (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_atBot.const_mul (2*potentialScatteringError q)
  exact squeeze_zero (fun κ => norm_nonneg _) (fun κ => (reflectionAmplitude_exponential_envelopes q κ).1) hl

theorem reverseReflectionAmplitude_tendsto_high (q : SchwartzMap ℝ ℂ) :
    Tendsto (reverseReflectionAmplitude q) atTop (𝓝 0) := by
  have hn := (reflectionAmplitude_tendsto_high q).neg
  simpa only [neg_zero, ← reverseReflectionAmplitude_eq_neg] using hn

theorem reverseReflectionAmplitude_tendsto_low (q : SchwartzMap ℝ ℂ) :
    Tendsto (reverseReflectionAmplitude q) atBot (𝓝 0) := by
  have hn := (reflectionAmplitude_tendsto_low q).neg
  simpa only [neg_zero, ← reverseReflectionAmplitude_eq_neg] using hn

/-- The nonvanishing transmission bound transports numerator decay to both reflection quotients. -/
theorem globalSmallScatteringPotential_reflection_by_numerator (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    ‖reflectionCoefficient (globalSmallScatteringPotential q) κ‖ ≤
      (4/3 : ℝ)*‖reflectionAmplitude (globalSmallScatteringPotential q) κ‖ ∧
    ‖reverseReflectionCoefficient (globalSmallScatteringPotential q) κ‖ ≤
      (4/3 : ℝ)*‖reflectionAmplitude (globalSmallScatteringPotential q) κ‖ := by
  have ht := globalSmallScatteringPotential_transmission_lower q κ
  have hn := norm_nonneg (reflectionAmplitude (globalSmallScatteringPotential q) κ)
  constructor
  · rw [reflectionCoefficient, norm_div]
    apply (div_le_iff₀ (by linarith [ht.1])).mpr
    nlinarith [mul_nonneg hn (by linarith : 0 ≤ ‖transmission (globalSmallScatteringPotential q) κ‖-3/4)]
  · rw [reverseReflectionCoefficient, norm_div, reverseReflectionAmplitude_eq_neg, norm_neg]
    apply (div_le_iff₀ (by linarith [ht.2])).mpr
    nlinarith [mul_nonneg hn (by linarith : 0 ≤ ‖reverseTransmission (globalSmallScatteringPotential q) κ‖-3/4)]

theorem globalSmallScatteringPotential_reflection_tendsto_high (q : SchwartzMap ℝ ℂ) :
    Tendsto (reflectionCoefficient (globalSmallScatteringPotential q)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hn := (reflectionAmplitude_tendsto_high (globalSmallScatteringPotential q)).norm.const_mul (4/3:ℝ)
  simp only [norm_zero, mul_zero] at hn
  exact squeeze_zero (fun κ => norm_nonneg _)
    (fun κ => (globalSmallScatteringPotential_reflection_by_numerator q κ).1) hn

theorem globalSmallScatteringPotential_reflection_tendsto_low (q : SchwartzMap ℝ ℂ) :
    Tendsto (reflectionCoefficient (globalSmallScatteringPotential q)) atBot (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hn := (reflectionAmplitude_tendsto_low (globalSmallScatteringPotential q)).norm.const_mul (4/3:ℝ)
  simp only [norm_zero, mul_zero] at hn
  exact squeeze_zero (fun κ => norm_nonneg _)
    (fun κ => (globalSmallScatteringPotential_reflection_by_numerator q κ).1) hn

theorem globalSmallScatteringPotential_reverseReflection_tendsto_high (q : SchwartzMap ℝ ℂ) :
    Tendsto (reverseReflectionCoefficient (globalSmallScatteringPotential q)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hn := (reflectionAmplitude_tendsto_high (globalSmallScatteringPotential q)).norm.const_mul (4/3:ℝ)
  simp only [norm_zero, mul_zero] at hn
  exact squeeze_zero (fun κ => norm_nonneg _)
    (fun κ => (globalSmallScatteringPotential_reflection_by_numerator q κ).2) hn

theorem globalSmallScatteringPotential_reverseReflection_tendsto_low (q : SchwartzMap ℝ ℂ) :
    Tendsto (reverseReflectionCoefficient (globalSmallScatteringPotential q)) atBot (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hn := (reflectionAmplitude_tendsto_low (globalSmallScatteringPotential q)).norm.const_mul (4/3:ℝ)
  simp only [norm_zero, mul_zero] at hn
  exact squeeze_zero (fun κ => norm_nonneg _)
    (fun κ => (globalSmallScatteringPotential_reflection_by_numerator q κ).2) hn

end
end GaloisForLFunctions.HTGeometry.FokasLenells
