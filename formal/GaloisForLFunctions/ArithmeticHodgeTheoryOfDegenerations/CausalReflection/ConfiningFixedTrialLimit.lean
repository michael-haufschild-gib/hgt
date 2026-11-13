import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningPotentialLimit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningGammaSpectralLimit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.HalfLineConfinementPoleDecay
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation

/-!
# The confining limit on fixed logarithmic trials

Compression separates the actual energy into its linear strength, its
logarithm, and a limiting logarithmic-plus-linear form. The Gamma remainder
vanishes by dominated convergence; concentration removes the arithmetic terms.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Ratio whose actual confinement coefficient equals the prescribed positive strength. -/
def confiningHalfLineRatio (a : ℝ) : ℝ := criticalAliasCoefficient 1 / a

theorem confiningHalfLineRatio_pos {a : ℝ} (ha : 0 < a) :
    0 < confiningHalfLineRatio a :=
  div_pos (criticalAliasCoefficient_positive zero_lt_one) ha

theorem criticalAliasCoefficient_confiningHalfLineRatio {a : ℝ} (ha : 0 < a) :
    criticalAliasCoefficient (confiningHalfLineRatio a) = a := by
  rw [criticalAliasCoefficient_eq_div (confiningHalfLineRatio a), confiningHalfLineRatio]
  have hk : criticalAliasCoefficient 1 ≠ 0 :=
    (criticalAliasCoefficient_positive zero_lt_one).ne'
  field_simp [hk, ha.ne']

/-- The limiting logarithmic spectral energy with linear half-line confinement. -/
def softLogarithmicHalfLineEnergy (F : ℝ → ℝ) : ℝ :=
  logarithmicFourierEnergy F + 8 * criticalHalfLineFirstMoment F

theorem SoftLogarithmicHalfLineDomain.integrable_signedLogarithm {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    Integrable (fun ξ => Real.log |ξ| * ‖𝓕 (cx F) ξ‖ ^ 2) := by
  have hft := RHTower.continuous_fourier_of_integrable
    (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
  have hm : Measurable (fun ξ => Real.log |ξ| * ‖𝓕 (cx F) ξ‖ ^ 2) := by fun_prop
  apply hF.logarithmic.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖𝓕 (cx F) ξ‖)]

/-- The rescaled Gamma form splits exactly into mass, logarithm, and the controlled remainder. -/
theorem SoftLogarithmicHalfLineDomain.archForm_unitaryDilation {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) {a : ℝ} (ha : 1 ≤ a) :
    archForm (unitaryRealDilation a F) = logarithmicFourierEnergy F +
      Real.log a * (∫ u, F u ^ 2) + confiningGammaErrorForm a (cx F) := by
  have ha0 := zero_lt_one.trans_le ha
  have hm := RHTower.integrable_norm_sq_fourier
    (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ)) hF.memLp_complex
  have he := integrable_confiningGammaError (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
    hF.memLp_complex hF.logarithmic ha
  rw [archForm_eq_integral_confiningGammaSymbol,
    integral_weighted_fourier_sq_unitaryRealDilation ha0 F confiningGammaSymbol]
  calc
    _ = ∫ ξ, (Real.log |ξ| * ‖𝓕 (cx F) ξ‖ ^ 2 + Real.log a * ‖𝓕 (cx F) ξ‖ ^ 2) +
        confiningGammaError a ξ * ‖𝓕 (cx F) ξ‖ ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by dsimp only [confiningGammaError]; ring
    _ = _ := by
      rw [integral_add (hF.integrable_signedLogarithm.add (hm.const_mul (Real.log a))) he,
        integral_add hF.integrable_signedLogarithm (hm.const_mul (Real.log a)),
        integral_const_mul,
        RHTower.integral_norm_sq_fourier_eq
          (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ)) hF.memLp_complex]
      simp only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        logarithmicFourierEnergy, confiningGammaErrorForm]

theorem SoftLogarithmicHalfLineDomain.tendsto_exponentialDefect {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    Tendsto (fun a : ℝ => criticalHalfLineExponentialDefect (unitaryRealDilation a F))
      atTop (𝓝 0) := by
  have h := hF.tendsto_scaled_exponentialDefect.mul tendsto_inv_atTop_zero
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  change (a * criticalHalfLineExponentialDefect (unitaryRealDilation a F)) * a⁻¹ = _
  rw [mul_right_comm, mul_inv_cancel₀ ha.ne', one_mul]

theorem SoftLogarithmicHalfLineDomain.tendsto_arithmeticRemainder {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) (hm : (∫ u, F u ^ 2) = 1) :
    Tendsto (fun a : ℝ => criticalHalfLineArithmeticRemainder (unitaryRealDilation a F))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d, hd, hsmall⟩ := exists_arithmeticRemainder_small_of_excess hε
  filter_upwards [hF.eventually_actual_dilation, eventually_gt_atTop (0 : ℝ),
    hF.tendsto_exponentialDefect.eventually (ge_mem_nhds hd)] with a hda ha hδ
  rw [Real.dist_eq, sub_zero]
  exact hsmall hda (by rw [integral_sq_unitaryRealDilation ha, hm]) hδ

/-- Fixed trials converge to the same logarithmic-plus-linear energy without arithmetic terms. -/
theorem SoftLogarithmicHalfLineDomain.tendsto_renormalized_trialEnergy {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) (hm : (∫ u, F u ^ 2) = 1) :
    Tendsto (fun a : ℝ => criticalHalfLineFullEnergy (confiningHalfLineRatio a)
      (unitaryRealDilation a F) - a - Real.log a)
      atTop (𝓝 (softLogarithmicHalfLineEnergy F)) := by
  have hs := tendsto_confiningGammaErrorForm (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
    hF.memLp_complex hF.logarithmic
  have hp := hF.tendsto_scaled_exponentialDefect
  have ha := hF.tendsto_arithmeticRemainder hm
  have hc : Tendsto (fun _ : ℝ => logarithmicFourierEnergy F) atTop
      (𝓝 (logarithmicFourierEnergy F)) := tendsto_const_nhds
  have h := ((hc.add hp).add hs).add ha
  have hl : logarithmicFourierEnergy F + 8 * criticalHalfLineFirstMoment F + 0 + 0 =
      softLogarithmicHalfLineEnergy F := by simp only [add_zero, softLogarithmicHalfLineEnergy]
  rw [hl] at h
  apply h.congr'
  filter_upwards [hF.eventually_actual_dilation, eventually_ge_atTop (1 : ℝ)] with a hda ha1
  change ((logarithmicFourierEnergy F +
    a * criticalHalfLineExponentialDefect (unitaryRealDilation a F)) +
    confiningGammaErrorForm a (cx F)) + criticalHalfLineArithmeticRemainder (unitaryRealDilation a F) =
    criticalHalfLineFullEnergy (confiningHalfLineRatio a) (unitaryRealDilation a F) - a - Real.log a
  have ha0 := zero_lt_one.trans_le ha1
  have harch := hF.archForm_unitaryDilation ha1
  rw [hm, mul_one] at harch
  have hmass : (∫ u, unitaryRealDilation a F u ^ 2) = 1 := by
    rw [integral_sq_unitaryRealDilation ha0, hm]
  rw [criticalHalfLineFullEnergy_eq_arch_add_remainder _ hda,
    criticalAliasCoefficient_confiningHalfLineRatio ha0, harch,
    criticalHalfLineExponentialDefect, hmass]
  ring

#print axioms SoftLogarithmicHalfLineDomain.archForm_unitaryDilation
#print axioms SoftLogarithmicHalfLineDomain.tendsto_renormalized_trialEnergy
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
