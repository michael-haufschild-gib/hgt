import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.UndampedCausalLaplaceMoments
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.GammaIntegrabilityFromLinearFourierDecay
import GaloisForLFunctions.HTGeometry.FourierTailSup

/-!
# Boundary cancellation admits the full Gamma energy

The undamped resolvent identity controls frequency times its Fourier
transform. Its L¹ norm controls the remaining bounded-frequency part.
Together these give first-order decay and the actual Gamma integrability.
-/

noncomputable section
open MeasureTheory Filter FourierTransform

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- A boundary-cancelled resolvent has global first-order Fourier decay.
The bound uses its actual L¹ mass, including the resonant frequency. -/
theorem linear_decay_fourier_undampedCausalConvolution (b : ℝ)
    {f : ℝ → ℂ} (hm : Measurable f) (hf : Integrable f)
    (hw : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate 0 b) = 0) (ξ : ℝ) :
    (1 + |ξ|) * ‖𝓕 (modulatedCausalConvolution 0 b f) ξ‖ ≤
      (1 + |b|) * (∫ u, ‖modulatedCausalConvolution 0 b f u‖) +
        (∫ u, ‖f u‖) / 2 := by
  let K := modulatedCausalConvolution 0 b f
  have he := congrArg norm (fourier_undampedCausalConvolution_mul b hm hf hw hs hz ξ)
  change ‖(((2 * (b + ξ) : ℝ) : ℂ) * Complex.I) * 𝓕 K ξ‖ = ‖𝓕 f ξ‖ at he
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), Complex.norm_I, mul_one] at he
  have hfreq : |ξ| ≤ |b + ξ| + |b| := by
    have h := norm_add_le (b + ξ) (-b)
    simpa only [Real.norm_eq_abs, show b + ξ + -b = ξ by ring, abs_neg] using h
  have hK := norm_fourierIntegral_le_mass K ξ
  have hF := norm_fourierIntegral_le_mass f ξ
  have hmass := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ 1 + |b|)
  have hshift := mul_le_mul_of_nonneg_right hfreq (norm_nonneg (𝓕 K ξ))
  change (1 + |ξ|) * ‖𝓕 K ξ‖ ≤ _
  nlinarith only [he, hF, hmass, hshift]

/-- Every fixed nonzero Fourier scaling retains first-order decay. -/
theorem linear_decay_fourier_rescale {H : ℝ → ℂ} {M c : ℝ}
    (hc : 0 < c) (hdec : ∀ ξ, (1 + |ξ|) * ‖H ξ‖ ≤ M) (r : ℝ) :
    (1 + |r|) * ‖H (-r / c)‖ ≤ (1 + c) * M := by
  have he : c * |-r / c| = |r| := by
    rw [abs_div, abs_neg, abs_of_pos hc]
    field_simp [ne_of_gt hc]
  have hsize : 1 + |r| ≤ (1 + c) * (1 + |-r / c|) := by
    nlinarith only [he, hc, abs_nonneg (-r / c)]
  calc
    _ ≤ ((1 + c) * (1 + |-r / c|)) * ‖H (-r / c)‖ :=
      mul_le_mul_of_nonneg_right hsize (norm_nonneg _)
    _ = (1 + c) * ((1 + |-r / c|) * ‖H (-r / c)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hdec _) (by positivity)

/-- First-order decay also holds in the paper Fourier normalization. -/
theorem exists_linear_decay_paperFT_undampedCausalConvolution (b : ℝ)
    {f : ℝ → ℂ} (hm : Measurable f) (hf : Integrable f)
    (hw : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate 0 b) = 0) :
    ∃ M : ℝ, ∀ r : ℝ,
      (1 + |r|) * ‖Zeta23.paperFT (modulatedCausalConvolution 0 b f) r‖ ≤ M := by
  refine ⟨(1 + 2 * Real.pi) *
    ((1 + |b|) * (∫ u, ‖modulatedCausalConvolution 0 b f u‖) + (∫ u, ‖f u‖) / 2),
    fun r => ?_⟩
  rw [Zeta23.paperFT_ofReal_eq_fourier]
  exact linear_decay_fourier_rescale (mul_pos (by norm_num) Real.pi_pos)
    (linear_decay_fourier_undampedCausalConvolution b hm hf hw hs hz) r

/-- An imaginary-axis zero supplies the complete Gamma-domain admission
of its literal undamped resolvent in the paper Fourier normalization. -/
theorem integrable_gamma_undampedCausalConvolution (b : ℝ)
    {f : ℝ → ℂ} (hm : Measurable f) (hf : Integrable f)
    (hw : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate 0 b) = 0) :
    Integrable (fun r : ℝ =>
      ‖Zeta23.paperFT (modulatedCausalConvolution 0 b f) r‖ ^ 2 * Zeta23.EF.gammaBracket r) := by
  have hK := (undampedCausalConvolution_memLp_and_integrable b hm hw hs hz).2
  have hcont : Continuous (𝓕 (modulatedCausalConvolution 0 b f)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hK
  have hc : Continuous (fun r : ℝ => Zeta23.paperFT (modulatedCausalConvolution 0 b f) r) := by
    simp_rw [Zeta23.paperFT_ofReal_eq_fourier]
    exact hcont.comp (by fun_prop)
  obtain ⟨M, hM⟩ := exists_linear_decay_paperFT_undampedCausalConvolution b hm hf hw hs hz
  exact ArithmeticHodgeTheoryOfDegenerations.integrable_gammaEnergy_of_linear_decay hc hM

end GaloisForLFunctions.HTGeometry
