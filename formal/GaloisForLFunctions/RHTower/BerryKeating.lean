import GaloisForLFunctions.Core

/-!
# The Berry-Keating `u = s(1-s)` coordinate (Tier A scalar skeleton)

This file formalizes the elementary algebra behind the FE-invariant coordinate
used in the Hilbert-Polya/Berry-Keating reading:

* `u(s) = s(1-s)` is invariant under the functional-equation involution
  `s ↦ 1-s`;
* on the critical line `s = 1/2 + iγ`, it is exactly the real value
  `1/4 + γ^2`, hence at least `1/4`;
* for a point with nonzero imaginary part away from the critical line, `u(s)`
  has nonzero imaginary part;
* the Kapustin spectral coordinate `1/u(s)` is real exactly on the critical
  line, once the real-axis degeneracy `Im(s)=0` is excluded.

This is only scalar complex arithmetic. It does not construct a Hilbert-Polya
operator, prove self-adjointness, identify spectra, or prove RH.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The FE-invariant Berry-Keating coordinate `u = s(1-s)`. -/
def berryKeatingU (s : ℂ) : ℂ := s * (1 - s)

/-- Unfolding lemma: `u s = s·(1-s)`. -/
@[aesop safe, simp] theorem berryKeatingU_apply (s : ℂ) : berryKeatingU s = s * (1 - s) := rfl

/-- Centering the reflection coordinate turns `u = s(1-s)` into a square subtracted from
`1/4`. -/
theorem berryKeatingU_eq_centered (s : ℂ) :
    berryKeatingU s = 1 / 4 - (s - 1 / 2) ^ 2 := by
  rw [berryKeatingU]
  ring

/-- The coordinate `u=s(1-s)` is invariant under the functional-equation involution. -/
@[aesop safe]
theorem berryKeatingU_sigma (s : ℂ) : berryKeatingU (sigma s) = berryKeatingU s := by
  simp [berryKeatingU, sigma]
  ring

/-- Real part of the Berry-Keating coordinate in rectangular coordinates. -/
@[aesop safe]
theorem berryKeatingU_re (s : ℂ) :
    (berryKeatingU s).re = s.re * (1 - s.re) + s.im ^ 2 := by
  simp [berryKeatingU, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

/-- Imaginary part of the Berry-Keating coordinate in rectangular coordinates. -/
@[aesop safe]
theorem berryKeatingU_im (s : ℂ) :
    (berryKeatingU s).im = (1 - 2 * s.re) * s.im := by
  simp [berryKeatingU, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- On the critical line, `u=s(1-s)` is real and equals `1/4 + Im(s)^2`. -/
@[aesop safe]
theorem berryKeatingU_on_critical (s : ℂ) (hs : s.re = 1 / 2) :
    (berryKeatingU s).im = 0 ∧ (berryKeatingU s).re = 1 / 4 + s.im ^ 2 := by
  constructor
  · rw [berryKeatingU_im, hs]
    ring
  · rw [berryKeatingU_re, hs]
    ring

/-- On the critical line, the real `u`-coordinate lies on the ray `[1/4,∞)`. -/
@[aesop safe]
theorem berryKeatingU_re_ge_quarter_on_critical (s : ℂ) (hs : s.re = 1 / 2) :
    1 / 4 ≤ (berryKeatingU s).re := by
  rw [(berryKeatingU_on_critical s hs).2]
  nlinarith [sq_nonneg s.im]

/-- Parametrized critical-line formula: `u(1/2+iγ)=1/4+γ^2`. -/
@[aesop safe]
theorem berryKeatingU_critical_param (γ : ℝ) :
    berryKeatingU ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = (1 / 4 + γ ^ 2 : ℂ) := by
  apply Complex.ext
  · rw [berryKeatingU_re]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_cast
    ring
  · rw [berryKeatingU_im]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    norm_cast

/-- A non-real point away from the critical line maps to a non-real `u`-coordinate.
The `s.im ≠ 0` hypothesis is essential: real off-line points still have real `u`. -/
@[aesop safe]
theorem berryKeatingU_nonreal_of_offCritical_nonzero_im (s : ℂ)
    (hcrit : s.re ≠ 1 / 2) (him : s.im ≠ 0) :
    (berryKeatingU s).im ≠ 0 := by
  rw [berryKeatingU_im]
  apply mul_ne_zero
  · intro h
    apply hcrit
    linarith
  · exact him

/-- The spectral coordinate used by Kapustin's Krein-self-adjoint realization:
every nontrivial zeta zero `ρ` contributes the point `1 / (ρ(1-ρ))`. -/
def kapustinEigenvalue (s : ℂ) : ℂ := (berryKeatingU s)⁻¹

@[simp] theorem kapustinEigenvalue_apply (s : ℂ) :
    kapustinEigenvalue s = (s * (1 - s))⁻¹ := rfl

/-- The Kapustin spectral coordinate retains the functional-equation pairing. -/
@[aesop safe]
theorem kapustinEigenvalue_sigma (s : ℂ) :
    kapustinEigenvalue (sigma s) = kapustinEigenvalue s := by
  rw [kapustinEigenvalue, kapustinEigenvalue, berryKeatingU_sigma]

/-- Exact imaginary part of the reciprocal Berry--Keating coordinate. -/
theorem kapustinEigenvalue_im (s : ℂ) :
    (kapustinEigenvalue s).im =
      -((1 - 2 * s.re) * s.im) / Complex.normSq (berryKeatingU s) := by
  rw [kapustinEigenvalue, Complex.inv_im, berryKeatingU_im]

/-- Off the critical line, a point with nonzero ordinate gives a genuinely
nonreal Kapustin eigenvalue. -/
@[aesop safe]
theorem kapustinEigenvalue_nonreal_of_offCritical_nonzero_im (s : ℂ)
    (hcrit : s.re ≠ 1 / 2) (him : s.im ≠ 0) :
    (kapustinEigenvalue s).im ≠ 0 := by
  have huim := berryKeatingU_nonreal_of_offCritical_nonzero_im s hcrit him
  rw [kapustinEigenvalue, Complex.inv_im]
  have hu0 : berryKeatingU s ≠ 0 := by
    intro h
    rw [h] at huim
    exact huim rfl
  exact div_ne_zero (neg_ne_zero.mpr huim) (Complex.normSq_pos.mpr hu0).ne'

/-- Away from the real axis, reality of `1/(s(1-s))` is exactly the critical
line condition.  This is the scalar endpoint behind the Kapustin
Hilbert--Pólya proposal. -/
theorem kapustinEigenvalue_im_eq_zero_iff (s : ℂ) (him : s.im ≠ 0) :
    (kapustinEigenvalue s).im = 0 ↔ s.re = 1 / 2 := by
  constructor
  · intro hreal
    by_contra hcrit
    exact kapustinEigenvalue_nonreal_of_offCritical_nonzero_im s hcrit him hreal
  · intro hcrit
    rw [kapustinEigenvalue, Complex.inv_im, (berryKeatingU_on_critical s hcrit).1]
    simp

/-- Equivalent conjugation-fixed form consumed by the spectral theorem: a
Hilbert-symmetric eigenvalue must be fixed by complex conjugation, hence its
non-real source point lies on the critical line. -/
theorem conj_kapustinEigenvalue_eq_iff (s : ℂ) (him : s.im ≠ 0) :
    (starRingEnd ℂ) (kapustinEigenvalue s) = kapustinEigenvalue s ↔
      s.re = 1 / 2 := by
  rw [Complex.conj_eq_iff_im, kapustinEigenvalue_im_eq_zero_iff s him]

end

end GaloisForLFunctions
