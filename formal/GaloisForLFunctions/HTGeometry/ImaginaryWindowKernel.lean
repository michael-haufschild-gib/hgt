import GaloisForLFunctions.HTGeometry.PaperRotationPhaseSlope

/-! # Sinc and conjugation of the removable imaginary window kernel -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

theorem forwardWindowKernel_imaginary_re (t : ℝ) :
    (forwardWindowKernel ((t : ℂ) * Complex.I)).re = Real.sinc t := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [forwardWindowKernel_of_ne
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero), Real.sinc_of_ne_zero ht]
    simp [Complex.div_re, Complex.exp_re, Complex.exp_im, Complex.normSq_apply]
    field_simp

theorem forwardWindowKernel_imaginary_conj (t : ℝ) :
    starRingEnd ℂ (forwardWindowKernel ((t : ℂ) * Complex.I)) =
      forwardWindowKernel (((-t : ℝ) : ℂ) * Complex.I) := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [forwardWindowKernel_of_ne
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero),
      forwardWindowKernel_of_ne
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr ht)) Complex.I_ne_zero)]
    simp only [map_div₀, map_sub, map_one, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, mul_neg, neg_mul]

theorem sinc_pos_of_abs_lt_pi {t : ℝ} (ht : |t| < Real.pi) : 0 < Real.sinc t := by
  rcases lt_trichotomy t 0 with hn | rfl | hp
  · rw [← Real.sinc_neg, Real.sinc_of_ne_zero (neg_pos.mpr hn).ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hn)
      (by rwa [abs_of_neg hn] at ht)) (neg_pos.mpr hn)
  · simp
  · rw [Real.sinc_of_ne_zero hp.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hp (by rwa [abs_of_pos hp] at ht)) hp

end
end GaloisForLFunctions.HTGeometry
