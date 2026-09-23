import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The principal square root on the right half-plane

An explicit principal square root, given by its real and imaginary parts

`p = sqrt ((‖z‖ + Re z) / 2)`,  `q = Im z / (2 p)`,

together with the three facts the spectral-family instantiation needs: `p^(2 : ℕ) = (‖z‖ + Re z)/2`, so
`p^(2 : ℕ) >= Re z`; `|q| = |Im z| / (2 p)`; and equivariance under conjugation.

No branch-cut theory is used: on the right half-plane `‖z‖ + Re z > 0`, so `p > 0` and the formulas
are unambiguous.
-/

open Complex

namespace HTGeometry

noncomputable section

/-- The real part of the principal square root. -/
def csqrtRe (z : ℂ) : ℝ := Real.sqrt ((‖z‖ + z.re) / 2)

/-- The imaginary part of the principal square root. -/
def csqrtIm (z : ℂ) : ℝ := z.im / (2 * csqrtRe z)

/-- The principal square root. -/
def csqrt (z : ℂ) : ℂ := Complex.mk (csqrtRe z) (csqrtIm z)

theorem csqrt_re (z : ℂ) : (csqrt z).re = csqrtRe z := rfl

theorem csqrt_im (z : ℂ) : (csqrt z).im = csqrtIm z := rfl

theorem re_le_norm (z : ℂ) : z.re ≤ ‖z‖ := Complex.re_le_norm z

theorem csqrtRe_nonneg (z : ℂ) : 0 ≤ csqrtRe z := Real.sqrt_nonneg _

theorem csqrtRe_pos {z : ℂ} (hz : 0 < z.re) : 0 < csqrtRe z := by
  rw [csqrtRe]
  refine Real.sqrt_pos.mpr ?_
  have := le_trans hz.le (re_le_norm z)
  linarith

theorem sq_csqrtRe {z : ℂ} (hz : 0 < z.re) : csqrtRe z ^ (2 : ℕ) = (‖z‖ + z.re) / 2 := by
  rw [csqrtRe, Real.sq_sqrt]
  have := le_trans hz.le (re_le_norm z)
  linarith

/-- The square of the real part dominates the real part of the argument. -/
theorem re_le_sq_csqrtRe {z : ℂ} (hz : 0 < z.re) : z.re ≤ csqrtRe z ^ (2 : ℕ) := by
  rw [sq_csqrtRe hz]
  have := re_le_norm z
  linarith

theorem abs_csqrtIm {z : ℂ} (hz : 0 < z.re) :
    |csqrtIm z| = |z.im| / (2 * csqrtRe z) := by
  have hp : (0 : ℝ) < 2 * csqrtRe z := by
    have := csqrtRe_pos hz
    linarith
  rw [csqrtIm, abs_div, abs_of_pos hp]

theorem csqrtIm_eq_zero_iff {z : ℂ} (hz : 0 < z.re) : csqrtIm z = 0 ↔ z.im = 0 := by
  rw [csqrtIm, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso
      have hp : (0 : ℝ) < 2 * csqrtRe z := by
        have := csqrtRe_pos hz
        linarith
      exact absurd h (ne_of_gt hp)
  · intro h
    exact Or.inl h

/-- The square of the imaginary part, in closed form. -/
theorem sq_csqrtIm {z : ℂ} (hz : 0 < z.re) : csqrtIm z ^ (2 : ℕ) = (‖z‖ - z.re) / 2 := by
  have hp : 0 < csqrtRe z := csqrtRe_pos hz
  have hsq : csqrtRe z ^ (2 : ℕ) = (‖z‖ + z.re) / 2 := sq_csqrtRe hz
  have hnorm : ‖z‖ ^ (2 : ℕ) = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hden : 0 < ‖z‖ + z.re := by
    have := Complex.re_le_norm z; linarith
  rw [csqrtIm, div_pow, show (2 * csqrtRe z) ^ (2 : ℕ) = 4 * csqrtRe z ^ (2 : ℕ) by ring, hsq]
  field_simp
  nlinarith [hnorm]

/-- **`csqrt` is a square root on the right half-plane.**  The two closed forms for the squares of
the real and imaginary parts differ by exactly `Re z`, and their product doubles to `Im z`. -/
theorem csqrt_sq {z : ℂ} (hz : 0 < z.re) : csqrt z ^ (2 : ℕ) = z := by
  have hp : 0 < csqrtRe z := csqrtRe_pos hz
  apply Complex.ext
  · rw [pow_two, Complex.mul_re, csqrt_re, csqrt_im]
    have h1 : csqrtRe z * csqrtRe z = (‖z‖ + z.re) / 2 := by
      rw [← pow_two]; exact sq_csqrtRe hz
    have h2 : csqrtIm z * csqrtIm z = (‖z‖ - z.re) / 2 := by
      rw [← pow_two]; exact sq_csqrtIm hz
    rw [h1, h2]; ring
  · rw [pow_two, Complex.mul_im, csqrt_re, csqrt_im, csqrtIm]
    field_simp
    ring

/-- The product of the two parts is half the imaginary part of the argument.  This is the
division-free form of the displacement law. -/
theorem csqrtIm_mul_csqrtRe {z : ℂ} (hz : 0 < z.re) :
    csqrtIm z * csqrtRe z = z.im / 2 := by
  have hp : 0 < csqrtRe z := csqrtRe_pos hz
  rw [csqrtIm]
  field_simp

theorem csqrt_conj (z : ℂ) : csqrt ((starRingEnd ℂ) z) = (starRingEnd ℂ) (csqrt z) := by
  have hre : ((starRingEnd ℂ) z).re = z.re := Complex.conj_re z
  have him : ((starRingEnd ℂ) z).im = -z.im := Complex.conj_im z
  have hnorm : ‖(starRingEnd ℂ) z‖ = ‖z‖ := by
    simp
  apply Complex.ext
  · rw [csqrt_re, Complex.conj_re, csqrt_re, csqrtRe, csqrtRe, hnorm, hre]
  · rw [csqrt_im, Complex.conj_im, csqrt_im, csqrtIm, csqrtIm, csqrtRe, csqrtRe, hnorm, hre, him]
    ring

end

end HTGeometry
