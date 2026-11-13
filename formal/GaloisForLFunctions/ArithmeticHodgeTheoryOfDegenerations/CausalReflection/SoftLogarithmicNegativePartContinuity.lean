import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicClosedDomain
import GaloisForLFunctions.HTGeometry.HardyBoundary.WeightedL2MomentContinuity
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

/-!
# Continuity of the negative logarithmic Fourier energy

A uniform physical first moment controls the Fourier mass near zero.
The resulting exponential tail bound removes bounded logarithmic caps
along strong L² limits of normalized trial profiles.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

private theorem tendsto_negativeLog_tail_majorant (M : ℝ) :
    Tendsto (fun T : ℝ => (8 + 2 * M) * (T + 2) * Real.exp (-(T / 2)))
      atTop (𝓝 0) := by
  have h1 := HTGeometry.tendsto_pow_mul_exp_neg_scaled 1 (δ := (1 / 2 : ℝ)) (by norm_num)
  have h0 := HTGeometry.tendsto_pow_mul_exp_neg_scaled 0 (δ := (1 / 2 : ℝ)) (by norm_num)
  have h := (h1.add (h0.const_mul 2)).const_mul (8 + 2 * M)
  simp only [pow_one, pow_zero, one_mul, mul_zero, add_zero] at h
  refine h.congr fun T => ?_
  rw [show -(T / 2) = -((1 / 2 : ℝ) * T) by ring]
  ring

/-- Uniform physical first moments remove the singular negative-logarithm cap
along strong L² limits of unit trial profiles. -/
theorem negativeLog_integral_tendsto_of_softLogarithmic_trials
    {F : ℕ → ℝ → ℝ} (hF : ∀ n, SoftLogarithmicHalfLineDomain (F n))
    (hm : ∀ n, (∫ u, F n u ^ 2) = 1)
    {V : ℕ → SoninL2} {v : SoninL2}
    (hV : ∀ n, (V n : ℝ → ℂ) =ᵐ[volume] cx (F n))
    (hconv : Tendsto V atTop (𝓝 v))
    {M : ℝ} (hM : ∀ n, criticalHalfLineFirstMoment (F n) ≤ M) :
    Integrable (fun ξ : ℝ => max (-Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2) ∧
      Tendsto (fun n => ∫ ξ : ℝ, max (-Real.log |ξ|) 0 * ‖fourierUnitary (V n) ξ‖ ^ 2)
        atTop (𝓝 (∫ ξ : ℝ, max (-Real.log |ξ|) 0 * ‖fourierUnitary v ξ‖ ^ 2)) := by
  have hfourier (n : ℕ) := (hF n).fourier_representative (hV n)
  have hmc (n : ℕ) : (∫ u, ‖cx (F n) u‖ ^ 2) = 1 := by
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hm n
  have hfirst (n : ℕ) : (∫ u, |u| * ‖cx (F n) u‖ ^ 2) ≤ M := by
    rw [(hF n).integral_absMoment]
    exact hM n
  have hi (n : ℕ) : Integrable (fun ξ : ℝ =>
      max (-Real.log |ξ|) 0 * ‖fourierUnitary (V n) ξ‖ ^ 2) := by
    apply (hF n).integrable_negativeLogarithm.congr
    filter_upwards [hfourier n] with ξ hξ
    exact congrArg (fun z : ℂ => max (-Real.log |ξ|) 0 * ‖z‖ ^ 2) hξ.symm
  have hb (n : ℕ) : (∫ ξ : ℝ, max (-Real.log |ξ|) 0 *
      ‖fourierUnitary (V n) ξ‖ ^ 2) ≤ 16 + 4 * M := by
    have he : (∫ ξ : ℝ, max (-Real.log |ξ|) 0 * ‖fourierUnitary (V n) ξ‖ ^ 2) =
        ∫ ξ : ℝ, max (-Real.log |ξ|) 0 * ‖𝓕 (cx (F n)) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hfourier n] with ξ hξ
      exact congrArg (fun z : ℂ => max (-Real.log |ξ|) 0 * ‖z‖ ^ 2) hξ
    rw [he]
    exact integral_negativeLog_fourier_le_firstMoment
      ((hF n).integrable.ofReal (𝕜 := ℂ)) (hF n).memLp_complex
      (hmc n) (hF n).integrable_absMoment (hfirst n)
  apply tendsto_weighted_norm_sq_of_uniform_tails
    ((fourierUnitary.continuous.tendsto v).comp hconv)
    (by fun_prop : Measurable (fun ξ : ℝ => max (-Real.log |ξ|) 0))
    (fun _ => le_max_right _ _) hi hb
  intro ε hε
  obtain ⟨T, hT, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    ((tendsto_negativeLog_tail_majorant M).eventually (gt_mem_nhds hε))).exists
  refine ⟨T, hT, fun n => ?_⟩
  have he : (∫ ξ in {ξ : ℝ | T < max (-Real.log |ξ|) 0},
      max (-Real.log |ξ|) 0 * ‖fourierUnitary (V n) ξ‖ ^ 2) =
      ∫ ξ in {ξ : ℝ | T < max (-Real.log |ξ|) 0},
        max (-Real.log |ξ|) 0 * ‖𝓕 (cx (F n)) ξ‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hfourier n)] with ξ hξ
    exact congrArg (fun z : ℂ => max (-Real.log |ξ|) 0 * ‖z‖ ^ 2) hξ
  dsimp only [Function.comp_apply]
  rw [he]
  exact (integral_negativeLog_fourier_tail_le_firstMoment
    ((hF n).integrable.ofReal (𝕜 := ℂ)) (hF n).memLp_complex
    (hmc n) (hF n).integrable_absMoment (hfirst n) hT).trans hsmall.le

#print axioms negativeLog_integral_tendsto_of_softLogarithmic_trials
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

