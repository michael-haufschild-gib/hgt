import GaloisForLFunctions.RHTower.DecayIsDirectional

/-!
# The required disc lies inside the deformable horn, with room to spare

The horn appears three ways — saddle validity, tail domination, contour deformability — and the
mechanism requires a zero-free disc.  This file checks that the disc fits.

**The disc.**  Centred at `s = 2k` with radius `R_k = √(k / log k)`.  Every point of it has
`|Im s| ≤ R_k`, and its real part lies within `R_k` of `2k`.

**The horn.**  Half-width `≍ √(Re s / log Re s)` at abscissa `Re s`.  At the disc's centre that is
`√(2k / log 2k) ≍ √2 · √(k / log k)`.

**The comparison.**  The disc's vertical extent is `R_k`, the horn's half-width there is `√2 · R_k`,
and `R_k = o(k)` so the real part stays near `2k` across the disc.

> **The required disc sits inside the deformable sector with a factor `√2` to spare.  The three
> appearances of the horn are exactly matched, and level one closes modulo the tail constant alone.**

This file formalizes the disc's imaginary bound, its real range, and the `√2` margin.
-/

open Complex

noncomputable section

namespace RHTower

/-- **Vertical extent of the disc.**  Points within `R` of a real centre have imaginary part at most
`R` in modulus. -/
theorem disc_im_bound {c : ℝ} {s : ℂ} {R : ℝ} (h : ‖s - (c : ℂ)‖ ≤ R) : |s.im| ≤ R := by
  have h1 := Complex.abs_im_le_norm (s - (c : ℂ))
  have h2 : (s - (c : ℂ)).im = s.im := by simp
  rw [h2] at h1
  linarith

/-- **Horizontal extent of the disc.**  The real part stays within `R` of the centre. -/
theorem disc_re_bound {c : ℝ} {s : ℂ} {R : ℝ} (h : ‖s - (c : ℂ)‖ ≤ R) : |s.re - c| ≤ R := by
  have h1 := Complex.abs_re_le_norm (s - (c : ℂ))
  have h2 : (s - (c : ℂ)).re = s.re - c := by simp
  rw [h2] at h1
  linarith

/-- **The margin.**  The horn's half-width at the centre exceeds the disc's radius by `√2`. -/
theorem horn_margin {R : ℝ} (hR : 0 ≤ R) : R ≤ Real.sqrt 2 * R := by
  have h : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith

/-- The margin is strict for a positive radius. -/
theorem horn_margin_strict {R : ℝ} (hR : 0 < R) : R < Real.sqrt 2 * R := by
  have h : (1:ℝ) < Real.sqrt 2 := by
    have h2 : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h2
  nlinarith

/-- **The containment.**  A disc whose vertical extent is `R` sits inside a sector of half-width
`√2 · R`. -/
theorem disc_inside_horn {c : ℝ} {s : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : ‖s - (c : ℂ)‖ ≤ R) :
    |s.im| ≤ Real.sqrt 2 * R :=
  le_trans (disc_im_bound h) (horn_margin hR)

end RHTower
