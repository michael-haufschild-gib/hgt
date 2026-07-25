import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The principal square root on the right half-plane

An explicit principal square root, given by its real and imaginary parts

`p = sqrt ((‖z‖ + Re z) / 2)`,  `q = Im z / (2 p)`,

together with the three facts the spectral-family instantiation needs: `p^2 = (‖z‖ + Re z)/2`, so
`p^2 >= Re z`; `|q| = |Im z| / (2 p)`; and equivariance under conjugation.

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

theorem sq_csqrtRe {z : ℂ} (hz : 0 < z.re) : csqrtRe z ^ 2 = (‖z‖ + z.re) / 2 := by
  rw [csqrtRe, Real.sq_sqrt]
  have := le_trans hz.le (re_le_norm z)
  linarith

/-- The square of the real part dominates the real part of the argument. -/
theorem re_le_sq_csqrtRe {z : ℂ} (hz : 0 < z.re) : z.re ≤ csqrtRe z ^ 2 := by
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
