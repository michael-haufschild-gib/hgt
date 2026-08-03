import GaloisForLFunctions.RHTower.Sieve.MultiplicativeDistance

/-!
# The pointwise comparison behind the distance

`‖u - v‖² = ‖u‖² + ‖v‖² - 2 Re(u conj v)`, so for values in the closed unit disc

`‖u - v‖²/2 ≤ 1 - Re(u conj v)`,

with equality when both are unimodular.  The summands of the distance therefore dominate the squared
Euclidean separation of the values, and agree with it on the unit circle.

This is the pointwise input to the metric properties of the Halász–Granville–Soundararajan distance.
The triangle inequality itself needs more than these comparisons and is not proved here.
-/

namespace RHTower.Sieve

/-- The polarisation identity. -/
theorem normSq_sub_eq (u v : ℂ) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (u * (starRingEnd ℂ) v).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **On the unit disc the distance summand dominates the Euclidean separation.** -/
theorem half_normSq_sub_le {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖u - v‖ ^ 2 / 2 ≤ 1 - (u * (starRingEnd ℂ) v).re := by
  have h := normSq_sub_eq u v
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith
  have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith
  linarith

/-- **On the unit circle the two agree.** -/
theorem one_sub_re_eq_half_normSq {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    1 - (u * (starRingEnd ℂ) v).re = ‖u - v‖ ^ 2 / 2 := by
  have h := normSq_sub_eq u v
  rw [hu, hv] at h
  simp only [one_pow] at h
  linarith

end RHTower.Sieve
