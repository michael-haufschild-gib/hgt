import Mathlib

/-!
# The even aperture form as a frame operator minus one scalar level

Four exact mechanisms of the card are formalized.

*The digamma resolvent term.*  `1/A − Re(1/(A+ib)) = b²/(A(A²+b²))`, the termwise content of `(3)`
and hence of `(2)`: every digamma increment summand is a nonnegative resolvent square.

*The prime difference square.*  `|1 − e^{iθ}|² = 2 − 2cos θ`, hence
`−2c cos(h ξ) = c|1 − e^{i h ξ}|² − 2c`, which is `(7)`: every visible prime power is an explicit
positive translation-difference channel plus a contribution to the scalar level.

*The bilateral polar splitting.*  `2cosh((x−y)/2) = 2cosh(x/2)cosh(y/2) − 2sinh(x/2)sinh(y/2)`,
which is `(10)`, so the polar block splits into one positive even and one negative odd feature
`(12)`.

*Frame minus level.*  The exact identity `(14)` collapses to `(15)` on even vectors and to `(16)` on
odd ones, and positivity is exactly the lower-frame inequality `(17)`.

Plancherel, the digamma partial-fraction series itself, the resolvent operators `(4)` and the
Paley–Wiener aperture compression are cited parents and stay outside the Lean statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The digamma resolvent term -/

/-- The real part of a resolvent value. -/
theorem re_inv_add_mul_I (A b : ℝ) :
    (((A : ℂ) + Complex.I * (b : ℂ))⁻¹).re = A / (A ^ 2 + b ^ 2) := by
  rw [Complex.inv_re]
  have hns : Complex.normSq ((A : ℂ) + Complex.I * (b : ℂ)) = A ^ 2 + b ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hns]
  congr 1
  simp

/-- **Equation (3), termwise.**  Each digamma increment summand is a nonnegative resolvent
square. -/
theorem digamma_term_identity {A b : ℝ} (hA : 0 < A) :
    1 / A - A / (A ^ 2 + b ^ 2) = b ^ 2 / (A * (A ^ 2 + b ^ 2)) := by
  have hden : A ^ 2 + b ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Equation (2), positivity of each summand.** -/
theorem digamma_term_nonneg {A b : ℝ} (hA : 0 < A) :
    0 ≤ b ^ 2 / (A * (A ^ 2 + b ^ 2)) := by
  have hden : 0 < A * (A ^ 2 + b ^ 2) := by positivity
  positivity

/-! ## The prime difference square -/

/-- The exact modulus of a unimodular difference. -/
theorem normSq_one_sub_exp (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (Complex.I * (θ : ℂ))) = 2 - 2 * Real.cos θ := by
  rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  have hpyth : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  ring_nf
  nlinarith [hpyth]

/-- **Equation (7).**  Every visible prime power is a positive translation-difference channel plus a
contribution to the scalar level. -/
theorem prime_difference_square (c θ : ℝ) :
    -2 * c * Real.cos θ
      = c * Complex.normSq (1 - Complex.exp (Complex.I * (θ : ℂ))) - 2 * c := by
  rw [normSq_one_sub_exp]
  ring

/-! ## The bilateral polar splitting -/

/-- **Equation (10).**  The aperture polar kernel splits into an even product minus an odd
product. -/
theorem polar_kernel_split (x y : ℝ) :
    2 * Real.cosh ((x - y) / 2)
      = 2 * Real.cosh (x / 2) * Real.cosh (y / 2)
        - 2 * Real.sinh (x / 2) * Real.sinh (y / 2) := by
  rw [show (x - y) / 2 = x / 2 - y / 2 by ring, Real.cosh_sub]
  ring

/-! ## Frame minus level -/

/-- **Equations (14) → (15).**  On an even vector the odd polar feature vanishes and the exact
identity becomes frame minus level. -/
theorem frame_minus_level_even {QW Bsq mu nv bminus : ℝ}
    (h : QW = Bsq - mu * nv - bminus ^ 2) (heven : bminus = 0) :
    QW = Bsq - mu * nv := by
  rw [h, heven]
  ring

/-- **Equation (16).**  On an odd vector the even polar feature drops out of the frame. -/
theorem frame_minus_level_odd {QW Gam Prm mu nv bminus bplus : ℝ}
    (h : QW = (Gam + Prm + bplus ^ 2) - mu * nv - bminus ^ 2) (hodd : bplus = 0) :
    QW = Gam + Prm - mu * nv - bminus ^ 2 := by
  rw [h, hodd]
  ring

/-- **Equation (17).**  Positivity of the even form is exactly the lower-frame inequality at the
scalar level. -/
theorem lower_frame_iff {QW Bsq mu nv : ℝ} (h : QW = Bsq - mu * nv) :
    0 ≤ QW ↔ mu * nv ≤ Bsq := by
  constructor <;> intro hh <;> linarith

end GaloisForLFunctions.RHTower

end
