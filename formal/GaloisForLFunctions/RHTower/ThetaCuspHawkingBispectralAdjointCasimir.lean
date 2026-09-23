import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion

/-!
# Bispectral Birmingham--Mokhtari adjoint Casimir

The doubled `d = 4` angular Casimir has normal form `lambda(z) = 1/4 + z^(2 : ℕ)`.
Keeping right and left spectral parameters independent gives the defect

`lambda(z) - lambda(w) = (z - w) * (z + w)`.

Functional-equation reflection `w = -z` is invisible to this Casimir.  On the adjoint graph
`w = conj z`, the folded left--right product is a nonnegative Gram scalar and, on every Xi divisor
copy, vanishes exactly on the critical line.
-/

open Complex

namespace RHTower

noncomputable section

/-- Difference of doubled BM angular Casimirs at independent right and left parameters. -/
def d4BMBispectralAngularCasimirDefect (z w : ℂ) : ℂ :=
  (1 / 4 + z ^ (2 : ℕ)) - (1 / 4 + w ^ (2 : ℕ))

theorem d4BMBispectralAngularCasimirDefect_eq (z w : ℂ) :
    d4BMBispectralAngularCasimirDefect z w = (z - w) * (z + w) := by
  rw [d4BMBispectralAngularCasimirDefect]
  ring

/-- The even angular Casimir cannot distinguish functional-equation partners. -/
theorem d4BMBispectralAngularCasimirDefect_fe_eq_zero (z : ℂ) :
    d4BMBispectralAngularCasimirDefect z (-z) = 0 := by
  rw [d4BMBispectralAngularCasimirDefect_eq]
  ring

/-- Folded bilinear left--right angular Gram. -/
def d4BMBispectralAngularCasimirGram (z w : ℂ) : ℂ :=
  d4BMBispectralAngularCasimirDefect z w *
    d4BMBispectralAngularCasimirDefect w z

theorem d4BMBispectralAngularCasimirGram_fe_eq_zero (z : ℂ) :
    d4BMBispectralAngularCasimirGram z (-z) = 0 := by
  simp [d4BMBispectralAngularCasimirGram,
    d4BMBispectralAngularCasimirDefect_fe_eq_zero]

/-- On the Schwarz-adjoint graph the defect is the anti-self-adjoint Casimir part. -/
theorem d4BMBispectralAngularCasimirDefect_adjoint (z : ℂ) :
    d4BMBispectralAngularCasimirDefect z (starRingEnd ℂ z) =
      4 * Complex.I * (z.re : ℂ) * (z.im : ℂ) := by
  rw [d4BMBispectralAngularCasimirDefect_eq]
  apply Complex.ext <;> simp
  ring

/-- Adjoint folding converts the bilinear product to the Hermitian norm square. -/
theorem d4BMBispectralAngularCasimirGram_adjoint (z : ℂ) :
    d4BMBispectralAngularCasimirGram z (starRingEnd ℂ z) =
      (Complex.normSq
        (d4BMBispectralAngularCasimirDefect z (starRingEnd ℂ z)) : ℂ) := by
  have hreverse :
      d4BMBispectralAngularCasimirDefect (starRingEnd ℂ z) z =
        -4 * Complex.I * (z.re : ℂ) * (z.im : ℂ) := by
    rw [d4BMBispectralAngularCasimirDefect_eq]
    apply Complex.ext <;> simp
    ring
  rw [d4BMBispectralAngularCasimirGram,
    d4BMBispectralAngularCasimirDefect_adjoint, hreverse]
  apply Complex.ext <;> simp [Complex.normSq_apply]

/-- At an Xi divisor, the adjoint Casimir defect is nonzero exactly off the critical line. -/
theorem d4BMBispectralAngularCasimirDefect_xi_ne_zero_iff (q : XiZeroCopy) :
    d4BMBispectralAngularCasimirDefect
        (xiSpectralPoint q) (starRingEnd ℂ (xiSpectralPoint q)) ≠ 0 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [d4BMBispectralAngularCasimirDefect_adjoint]
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    rw [xiSpectralPoint_re_eq]
    exact xi_divisor_support_im_ne_zero q.1
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint, Complex.mul_im]
  have hprefix :
      (4 : ℂ) * Complex.I * ((xiSpectralPoint q).re : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hre)
  constructor
  · intro h hline
    have himne : (xiSpectralPoint q).im ≠ 0 :=
      Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp h).2
    apply himne
    rw [him, hline]
    norm_num
  · intro hline
    apply mul_ne_zero hprefix
    apply Complex.ofReal_ne_zero.mpr
    rw [him]
    exact sub_ne_zero.mpr hline.symm

theorem d4BMBispectralAngularCasimirDefect_xi_eq_zero_iff (q : XiZeroCopy) :
    d4BMBispectralAngularCasimirDefect
        (xiSpectralPoint q) (starRingEnd ℂ (xiSpectralPoint q)) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [← not_iff_not]
  exact d4BMBispectralAngularCasimirDefect_xi_ne_zero_iff q

/-- The Xi adjoint Gram vanishes exactly on the critical line. -/
theorem d4BMBispectralAngularCasimirGram_xi_eq_zero_iff (q : XiZeroCopy) :
    d4BMBispectralAngularCasimirGram
        (xiSpectralPoint q) (starRingEnd ℂ (xiSpectralPoint q)) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMBispectralAngularCasimirGram_adjoint]
  simp [d4BMBispectralAngularCasimirDefect_xi_eq_zero_iff]

/-- The real part of the Xi adjoint Gram is strictly positive exactly off line. -/
theorem d4BMBispectralAngularCasimirGram_xi_re_pos_iff (q : XiZeroCopy) :
    0 < (d4BMBispectralAngularCasimirGram
      (xiSpectralPoint q) (starRingEnd ℂ (xiSpectralPoint q))).re ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [d4BMBispectralAngularCasimirGram_adjoint]
  simp only [Complex.ofReal_re]
  rw [Complex.normSq_pos,
    d4BMBispectralAngularCasimirDefect_xi_ne_zero_iff]

end

end RHTower
