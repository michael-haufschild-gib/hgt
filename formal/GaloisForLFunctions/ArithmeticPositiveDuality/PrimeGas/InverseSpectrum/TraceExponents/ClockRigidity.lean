import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.ImaginaryFactor
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.WarmFrontier
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-! # The real critical parameter from norm conservation and sharp trace stability -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- At a matched power a physical estimate with the sharp real-temperature coefficient singles out zero clock height. -/
theorem real_factor_iff_zero_height (r : ℕ) {z : ℂ} (hz : 0 < z.re) (h₂ : z.re ≤ 2) :
    traceControlsAt (r+1) z (2/z.re) (((r+1:ℕ):ℝ)^(2/z.re-1)) ↔ z.im = 0 := by
  constructor
  · intro h
    by_contra ht
    have hm : z.re*(2/z.re) = 2 := by rw [mul_comm,div_mul_cancel₀ _ hz.ne']
    exact (lt_irrefl _ (imaginary_matched_factor_strict r hz ht (div_pos (by norm_num) hz) hm h))
  · intro hi
    have he : (z.re:ℂ) = z := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi.symm)
    have h := (real_matched_factor_iff r hz h₂ _).mpr (le_refl _)
    rwa [he] at h

/-- Probability-preserving composition and the real quartic coefficient together select the single parameter one half. -/
theorem isometric_and_sharp_trace_iff_half (r : ℕ) (z : ℂ) :
    ((∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x) ∧
      traceControlsAt (r+1) z 4 (((r+1:ℕ):ℝ)^3)) ↔ z = 1/2 := by
  rw [split_isometric_iff]
  constructor
  · rintro ⟨he,h⟩
    have hp : 0 < z.re := by rw [he]; norm_num
    have h₂ : z.re ≤ 2 := by rw [he]; norm_num
    have hm : 2/z.re = 4 := by rw [he]; norm_num
    have hr : ((r+1:ℕ):ℝ)^((4:ℝ)-1) = ((r+1:ℕ):ℝ)^3 := by
      rw [show (4:ℝ)-1 = (3:ℕ) by norm_num,Real.rpow_natCast]
    have h' := real_factor_iff_zero_height r hp h₂
    rw [hm,hr] at h'
    apply Complex.ext
    · exact he.trans (by norm_num)
    · exact (h'.mp h).trans (by norm_num)
  · rintro rfl
    have h₀ : (1/2:ℂ).re = 1/2 := by norm_num
    have hz : 0 < (1/2:ℂ).re := by rw [h₀]; norm_num
    have h := (real_factor_iff_zero_height r hz (by rw [h₀]; norm_num)).mpr (by norm_num)
    have hm : 2/(1/2:ℂ).re = 4 := by rw [h₀]; norm_num
    rw [hm,show (4:ℝ)-1 = (3:ℕ) by norm_num,Real.rpow_natCast] at h
    exact ⟨h₀,h⟩

#print axioms real_factor_iff_zero_height
#print axioms isometric_and_sharp_trace_iff_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
