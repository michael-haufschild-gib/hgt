import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexCausalLaplaceBoundary
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.UndampedCausalResolventBasicDomain

/-!
# Laplace moments of the undamped causal resolvent

Cancellation of an imaginary-axis Laplace value supplies actual integrability
of the undamped resolvent. Continuity from the anti-causal side then gives its
moment identity on the entire imaginary axis, including the resonant point.
The two exponentially decaying representations give all other admitted moments.
-/

noncomputable section
open MeasureTheory Filter Set Topology FourierTransform
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

private theorem neutral_moment_by_continuity {z q : ℂ}
    (hzre : z.re = 0) (hqre : q.re = 0) {f : ℝ → ℂ}
    (hf : Integrable f) (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f z = 0)
    (hK : Integrable (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f)) :
    (z - q) * negativeHalfLineLaplace
      (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) q =
      (Real.pi : ℂ) * negativeHalfLineLaplace f q := by
  let K := complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hi := integrable_negativeHalfLineLaplace hf hs hzre.ge
  have hKs : ∀ u, 0 ≤ u → K u = 0 :=
    complexCausalConvolution_support_of_laplace_zero hi hz hs
  let qs : ℕ → ℂ := fun n => q + Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹)
  have hseq : Tendsto qs atTop (𝓝 q) := by
    have hr : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
    have hc := Filter.Tendsto.comp (Complex.continuous_ofReal.tendsto 0) hr
    simpa only [qs, Function.comp_apply, Complex.ofReal_zero, add_zero] using
      (tendsto_const_nhds (x := q)).add hc
  have hpos (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hqs (n : ℕ) : 0 ≤ (qs n).re := by
    change 0 ≤ (q + Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹)).re
    simpa only [Complex.add_re, Complex.ofReal_re, hqre, zero_add] using (hpos n).le
  have hwithin : Tendsto qs atTop (𝓝[{w : ℂ | 0 ≤ w.re}] q) :=
    tendsto_nhdsWithin_iff.mpr ⟨hseq, Eventually.of_forall hqs⟩
  have hKL := Filter.Tendsto.comp
    (show Tendsto (negativeHalfLineLaplace K) (𝓝[{w : ℂ | 0 ≤ w.re}] q)
      (𝓝 (negativeHalfLineLaplace K q)) from
        continuousOn_negativeHalfLineLaplace hK hKs q hqre.ge) hwithin
  have hFL := Filter.Tendsto.comp
    (show Tendsto (negativeHalfLineLaplace f) (𝓝[{w : ℂ | 0 ≤ w.re}] q)
      (𝓝 (negativeHalfLineLaplace f q)) from
        continuousOn_negativeHalfLineLaplace hf hs q hqre.ge) hwithin
  have hleft : Tendsto (fun n => (z - qs n) * negativeHalfLineLaplace K (qs n))
      atTop (𝓝 ((z - q) * negativeHalfLineLaplace K q)) :=
    (tendsto_const_nhds.sub hseq).mul hKL
  have hright : Tendsto (fun n => (Real.pi : ℂ) * negativeHalfLineLaplace f (qs n))
      atTop (𝓝 ((Real.pi : ℂ) * negativeHalfLineLaplace f q)) :=
    tendsto_const_nhds.mul hFL
  have hidentity (n : ℕ) :
      (z - qs n) * negativeHalfLineLaplace K (qs n) =
        (Real.pi : ℂ) * negativeHalfLineLaplace f (qs n) := by
    have hd : 0 < (qs n - z).re := by
      change 0 < (q + Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹) - z).re
      simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        hzre, hqre, zero_add, sub_zero] using hpos n
    have hn : z - qs n ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re] at hr hd
      linarith only [hr, hd]
    rw [negativeHalfLineLaplace_causalConvolution_of_gt hd hi hz
      (integrable_negativeHalfLineLaplace hf hs (hqs n))]
    field_simp [hn]
  exact tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall fun n => (hidentity n).symm))

/-- The actual weighted domain supplies the undamped moment law at every
admitted argument; no resolvent-domain premise is needed. -/
theorem negativeHalfLineLaplace_undampedCausalConvolution_mul (b : ℝ)
    {f : ℝ → ℂ} (hm : Measurable f) (hf : Integrable f)
    (hw : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate 0 b) = 0)
    {q : ℂ} (hq : Integrable (complexLaplaceWeighted q f)) :
    (modulatedLaplaceRate 0 b - q) *
      negativeHalfLineLaplace (modulatedCausalConvolution 0 b f) q =
      (Real.pi : ℂ) * negativeHalfLineLaplace f q := by
  have hzre : (modulatedLaplaceRate 0 b).re = 0 := by
    simp [modulatedLaplaceRate]
  have he : modulatedCausalConvolution 0 b f =
      complexRateCausalKernel (modulatedLaplaceRate 0 b) ⋆[ContinuousLinearMap.mul ℂ ℂ] f := by
    rw [modulatedCausalConvolution, modulatedCausalExponential_eq_complexRate]
  rw [he]
  rcases lt_trichotomy q.re 0 with hlt | heq | hgt
  · have hd : 0 < (modulatedLaplaceRate 0 b - q).re := by
      simpa only [Complex.sub_re, hzre, zero_sub] using neg_pos.mpr hlt
    have hn : modulatedLaplaceRate 0 b - q ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hd
      exact (lt_irrefl 0) hd
    rw [negativeHalfLineLaplace_causalConvolution_of_lt hd hq]
    field_simp [hn]
  · apply neutral_moment_by_continuity hzre heq hf hs hz
    rw [← he]
    exact (undampedCausalConvolution_memLp_and_integrable b hm hw hs hz).2
  · have hd : 0 < (q - modulatedLaplaceRate 0 b).re := by
      simpa only [Complex.sub_re, hzre, sub_zero] using hgt
    have hn : modulatedLaplaceRate 0 b - q ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re, hzre, zero_sub] at hr
      linarith only [hr, hgt]
    rw [negativeHalfLineLaplace_causalConvolution_of_gt hd
      (integrable_negativeHalfLineLaplace hf hs hzre.ge) hz hq]
    field_simp [hn]

/-- Imaginary Laplace values are the ordinary Fourier transform with opposite frequency. -/
theorem negativeHalfLineLaplace_modulated_zero_eq_fourier (f : ℝ → ℂ) (b : ℝ) :
    negativeHalfLineLaplace f (modulatedLaplaceRate 0 b) = 𝓕 f (-b) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  refine Eventually.of_forall fun u => ?_
  change Complex.exp (modulatedLaplaceRate 0 b * (u : ℂ)) * f u =
    Complex.exp (((-2 * Real.pi * u * (-b) : ℝ) : ℂ) * Complex.I) * f u
  congr 2
  unfold modulatedLaplaceRate
  push_cast
  ring

/-- Cancellation admits the exact undamped Fourier multiplier even at its
resonance: there the multiplied identity states the input's vanishing. -/
theorem fourier_undampedCausalConvolution_mul (b : ℝ)
    {f : ℝ → ℂ} (hm : Measurable f) (hf : Integrable f)
    (hw : MemLp (causalLaplaceWeighted (4 / Real.pi) f) 2 volume)
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate 0 b) = 0) (ξ : ℝ) :
    ((2 * (b + ξ) : ℝ) : ℂ) * Complex.I *
      𝓕 (modulatedCausalConvolution 0 b f) ξ = 𝓕 f ξ := by
  have hq : 0 ≤ (modulatedLaplaceRate 0 (-ξ)).re := by simp [modulatedLaplaceRate]
  have he := negativeHalfLineLaplace_undampedCausalConvolution_mul b hm hf hw hs hz
    (integrable_negativeHalfLineLaplace hf hs hq)
  rw [negativeHalfLineLaplace_modulated_zero_eq_fourier,
    negativeHalfLineLaplace_modulated_zero_eq_fourier, neg_neg] at he
  have hr : modulatedLaplaceRate 0 b - modulatedLaplaceRate 0 (-ξ) =
      (Real.pi : ℂ) * (((2 * (b + ξ) : ℝ) : ℂ) * Complex.I) := by
    unfold modulatedLaplaceRate
    push_cast
    ring
  rw [hr, mul_assoc] at he
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) he

end GaloisForLFunctions.HTGeometry
