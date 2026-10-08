import GaloisForLFunctions.RHTower.WeilWorkQuantizationResonance

/-!
# Summing every frequency resonance of the actual Weil source

Exponential summability pays both the critical-edge integrals and their
radial errors. The full sum retains every rational arithmetic resonance;
no nonresonance assumption or continuous critical trace is required.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist RightEdgeKernel IntegerMassRigidity HamburgerStability

/-- Any exponentially summable frequency family has summable actual resonant coefficients. -/
theorem summable_quantizationFrequencyResidue {ι : Type} {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) {m : ℕ} (hm : 1 ≤ m) :
    Summable fun j => p j * quantizationFrequencyResidue lam (ω j) m := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_quantizationFrequencyResidue hW hm
  apply (hp.mul_left K).of_norm_bounded
  intro j
  rw [norm_mul]
  calc ‖p j‖ * ‖quantizationFrequencyResidue lam (ω j) m‖ ≤
      ‖p j‖ * (K * Real.exp (|ω j| / 2)) := mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
    _ = _ := by ring

/-- Sum the actual measurable critical-edge integrals before taking a radial limit. -/
theorem hasSum_quantization_frequency_integrals {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} (ω : ι → ℝ)
    (hp : Summable fun j => ‖p j‖) {τ : ℂ} (hτ : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) :
    HasSum (fun j => p j * ∫ y in Iic (-2 : ℝ),
      linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I) *
        (quantizationTraceF hW y * pairKernel y τ))
      (∫ y in Iic (-2 : ℝ), (∑' j, p j *
        linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)) *
          (quantizationTraceF hW y * pairKernel y τ)) := by
  let F : ι → ℝ → ℂ := fun j y => p j *
    (linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I) *
      (quantizationTraceF hW y * pairKernel y τ))
  have hF : ∀ j, IntegrableOn (F j) (Iic (-2 : ℝ)) := fun j =>
    (integrableOn_quantization_twist_left hW (ω j) hτ hτ1 le_rfl).const_mul (p j)
  have hnorm : ∀ j y, ‖F j y‖ = ‖p j‖ * ‖quantizationTraceF hW y * pairKernel y τ‖ := by
    intro j y
    simp [F, norm_linTwist]
  have hsum : Summable fun j => ∫ y in Iic (-2 : ℝ), ‖F j y‖ := by
    simp_rw [hnorm, integral_const_mul]
    exact hp.mul_right _
  have hs := hasSum_integral_of_summable_integral_norm hF hsum
  simp only [F, integral_const_mul] at hs
  simpa only [← mul_assoc, tsum_mul_right] using hs

/-- Full resonant frequency comparison for the actual source, with no separation hypothesis. -/
theorem tendsto_quantization_frequency_sum_resonance {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ =>
      (ε : ℂ) * (∫ y in Iic (-2 : ℝ), (∑' j, p j *
        linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)) *
          (quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I))) -
      (∑' j, p j * quantizationFrequencyResidue lam (ω j) m) *
        quantizationMainRadial m ε) (𝓝[>] 0) (𝓝 0) := by
  have hp1 : Summable fun j => ‖p j‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by positivity))) hp
  let J : ℝ → ι → ℂ := fun ε j => (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
    linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I) *
      (quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I))
  let R : ι → ℂ := fun j => quantizationFrequencyResidue lam (ω j) m
  obtain ⟨KJ, hKJ, hJ⟩ := exists_bound_quantization_twist_radial hW hm
  obtain ⟨KR, hKR, hR⟩ := exists_bound_quantizationFrequencyResidue hW hm
  obtain ⟨KM, hKM, hM⟩ := exists_bound_quantizationMainRadial hm
  have hlim := tendsto_tsum_of_dominated_convergence
    (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun (ε : ℝ) (j : ι) => p j * (J ε j - R j * quantizationMainRadial m ε))
    (g := fun _ => (0 : ℂ))
    (bound := fun j => (KJ + KR * KM) * (‖p j‖ * Real.exp (|ω j| / 2)))
    (hp.mul_left _) (fun j => ?_) ?_
  · have hlim' : Tendsto (fun ε : ℝ => ∑' j,
        p j * (J ε j - R j * quantizationMainRadial m ε)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hlim
    apply hlim'.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hτ : 0 < ((ε : ℂ) + (m : ℂ) * I).re := by simpa using hε
    have hτ1 : 1 ≤ ‖(ε : ℂ) + (m : ℂ) * I‖ := by
      have hi := Complex.abs_im_le_norm ((ε : ℂ) + (m : ℂ) * I)
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.natCast_re,
        zero_add] at hi
      rw [abs_of_nonneg (show (0 : ℝ) ≤ m by positivity)] at hi
      linarith
    have hsum := (hasSum_quantization_frequency_integrals hW ω hp1 hτ hτ1).mul_left (ε : ℂ)
    have hsum' : HasSum (fun j => p j * J ε j)
        ((ε : ℂ) * ∫ y in Iic (-2 : ℝ), (∑' j, p j *
          linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)) *
            (quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I))) := by
      simpa only [J, mul_left_comm] using hsum
    have hr := (summable_quantizationFrequencyResidue hW hp hm).mul_right
      (quantizationMainRadial m ε)
    simp_rw [mul_sub, ← mul_assoc]
    rw [hsum'.summable.tsum_sub hr, hsum'.tsum_eq, tsum_mul_right]
    simp only [mul_assoc]
  · simpa only [J, R, quantizationMainRadial, mul_zero] using (tendsto_quantization_trace_resonance hW (ω j) hm).const_mul (p j)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε j
    rw [norm_mul]
    have hb : ‖J ε j - R j * quantizationMainRadial m ε‖ ≤
        (KJ + KR * KM) * Real.exp (|ω j| / 2) := by
      calc _ ≤ ‖J ε j‖ + ‖R j * quantizationMainRadial m ε‖ := norm_sub_le _ _
        _ = ‖J ε j‖ + ‖R j‖ * ‖quantizationMainRadial m ε‖ := by rw [norm_mul (R j) (quantizationMainRadial m ε)]
        _ ≤ KJ * Real.exp (|ω j| / 2) + (KR * Real.exp (|ω j| / 2)) * KM := by
          gcongr
          · exact hJ _ _ hε.1 hε.2.le
          · exact hR _
          · exact hM _ hε.1 hε.2.le
        _ = _ := by ring
    calc _ ≤ ‖p j‖ * ((KJ + KR * KM) * Real.exp (|ω j| / 2)) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by ring

end RHTower.WeilSpectral
