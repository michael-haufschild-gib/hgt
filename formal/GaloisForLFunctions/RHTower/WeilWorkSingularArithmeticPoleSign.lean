import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellinBound

/-!
# Full positivity forces the source double-pole coefficient to be nonpositive

The real Mellin transform has a uniform upper bound as its parameter
approaches one from the right. Multiplication by the squared distance to
one, together with the actual source pole limit, extracts its sign.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem continuousAt_GammaReal_one : ContinuousAt Complex.Gammaℝ 1 := by
  have h : ContinuousAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 1 :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hi := h.inv₀ (by simp : (Complex.Gammaℝ 1)⁻¹ ≠ 0)
  change ContinuousAt (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) 1 at hi
  simpa only [inv_inv] using hi

theorem tendsto_sq_mul_re_mellin_sourceGaussianProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun σ : ℝ => (σ - 1) ^ 2 *
      (mellin (sourceGaussianProfile lam) ((σ : ℂ) / 2)).re) (𝓝[>] 1)
      (𝓝 (sourcePoleNumerator hW 1).re) := by
  have hg : Tendsto (fun σ : ℝ => Complex.Gammaℝ (σ : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    simpa only [Complex.Gammaℝ_one, Function.comp_def] using continuousAt_GammaReal_one.tendsto.comp
      (tendsto_ofReal_nhdsWithin_ne_one.mono_right nhdsWithin_le_nhds)
  have hv := (tendsto_sq_mul_sourceZetaSquare hW).comp tendsto_ofReal_nhdsWithin_ne_one
  have h := Complex.continuous_re.tendsto _ |>.comp (hg.mul hv)
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ' : 1 < (σ : ℂ).re := by exact hσ
  rw [mellin_sourceGaussianProfile hW hσ']
  have he : Complex.Gammaℝ (σ : ℂ) *
      (((σ : ℂ) - 1) ^ 2 * sourceZetaSquare hW (σ : ℂ)) =
      (((σ - 1) ^ 2 : ℝ) : ℂ) *
        (Complex.Gammaℝ (σ : ℂ) * sourceZetaSquare hW (σ : ℂ)) := by
    push_cast
    ring
  simp only [Function.comp_apply, he, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A source conclusion from full positivity alone: the leading double-pole
coefficient of its signed arithmetic convolution is nonpositive. -/
theorem re_sourcePoleNumerator_one_nonpos {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (sourcePoleNumerator hW 1).re ≤ 0 := by
  obtain ⟨B, hB⟩ := exists_re_mellin_sourceGaussianProfile_le hW
  have hz : Tendsto (fun σ : ℝ => (σ - 1) ^ 2 * B) (𝓝[>] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun σ : ℝ => (σ - 1) ^ 2 * B) 1 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto (tendsto_sq_mul_re_mellin_sourceGaussianProfile hW) hz
  have hu : ∀ᶠ σ : ℝ in 𝓝[>] 1, σ < 3 / 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds (show (1 : ℝ) ∈ Iio (3 / 2) by norm_num))
  filter_upwards [self_mem_nhdsWithin, hu] with σ hσ hσ'
  exact mul_le_mul_of_nonneg_left (hB σ hσ hσ') (sq_nonneg _)

end RHTower.WeilSingularArithmetic
