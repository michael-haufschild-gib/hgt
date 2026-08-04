import GaloisForLFunctions.RHTower.Sieve.TriangularInversion

/-!
# The triangular kernel as an integral against a phase

Fourier inversion, written out: the overlap kernel of two windows of common length `δ` is

    (δ - |t|)₊ = ∫_ℝ e^{2πitw} · 𝓕(δ - |·|)₊(w) dw ,

with `𝓕(δ - |·|)₊(w) = δ · fejerWeightAt δ (-2πw)` nonnegative and integrable.  In this form the
kernel of `LogWindowKernel.lean` separates the two indices `n` and `m`, which is what turns the exact
quadratic form into a weighted integral of `|∑ₙ aₙ n^{2πiw}|²`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory FourierTransform Real

/-- **The triangular kernel as an integral against a phase.** -/
theorem triC_eq_integral {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    triC δ t = ∫ w : ℝ, Complex.exp (((2 * Real.pi * (w * t) : ℝ) : ℂ) * Complex.I)
      * 𝓕 (triC δ) w := by
  have h := congrFun (fourierInv_fourier_triC hδ) t
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [show ((2 * Real.pi * -(w * -t) : ℝ) : ℂ) = ((2 * Real.pi * (w * t) : ℝ) : ℂ) by
    push_cast; ring]

/-- The transform of the triangular kernel is real. -/
theorem fourier_triC_conj {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    (starRingEnd ℂ) (𝓕 (triC δ) w) = 𝓕 (triC δ) w := by
  rw [fourier_triC hδ]
  rcases eq_or_ne (-(2 * Real.pi * w)) 0 with h | h
  · rw [h, fejerWeightAt_zero hδ, map_mul, Complex.conj_ofReal]
  · rw [fejerWeightAt, integral_fejer_symm_real _ h hδ, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal]

/-- The transform of the triangular kernel is nonnegative. -/
theorem fourier_triC_re_nonneg {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    0 ≤ (𝓕 (triC δ) w).re := by
  rw [fourier_triC hδ]
  rcases eq_or_ne (-(2 * Real.pi * w)) 0 with h | h
  · rw [h, fejerWeightAt_zero hδ, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  · rw [fejerWeightAt, integral_fejer_symm_real _ h hδ, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg hδ.le (fejer_transform_nonneg _ hδ)

end RHTower.Sieve
