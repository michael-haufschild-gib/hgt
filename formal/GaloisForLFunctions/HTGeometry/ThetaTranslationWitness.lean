import GaloisForLFunctions.HTGeometry.JacobiThetaDifferentialOrbitObstruction
import Mathlib.NumberTheory.Real.Irrational

/-!
# The theta translation conditions occur together

The theta orbit obstruction consumes `ThetaTranslationNontorsion τ q` — no nonzero integer multiple
of `q` lies in `ℤ + ℤτ` — together with `ThetaTranslationNonresonant τ q h` — the shift `h` lies
outside `ℤ + ℤτ + ℤq`.  Neither is exhibited anywhere, so the layer could be about an empty
configuration of translations.

It is not, and the witness is elementary.  Take `τ = i`, `q = √2`, `h = i/2`.  Nontorsion compares
imaginary parts to force the `τ`-coefficient to vanish and then reduces to irrationality of `√2`.
Nonresonance never needs the real part at all: the imaginary part of `h` is `1/2`, which is not an
integer.

* **`thetaTranslation_nontorsion_nonresonant_witness`** — the pair, jointly realized.
-/

namespace GaloisForLFunctions

/-- The `√2` translation is nontorsion over the Gaussian lattice. -/
theorem thetaTranslationNontorsion_I_sqrtTwo :
    ThetaTranslationNontorsion Complex.I ((Real.sqrt 2 : ℝ) : ℂ) := by
  intro a b n hn
  by_contra hn0
  have him := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
    zero_add, mul_one] at him
  have hre := congrArg Complex.re hn
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    mul_one, ← him] at hre
  have hirr : Irrational ((n : ℝ) * Real.sqrt 2) := irrational_sqrt_two.intCast_mul hn0
  exact hirr.ne_int a (by simpa using hre)

/-- The half-period shift `i/2` is nonresonant for that lattice: its imaginary part is not an
integer. -/
theorem thetaTranslationNonresonant_I_sqrtTwo_halfI :
    ThetaTranslationNonresonant Complex.I ((Real.sqrt 2 : ℝ) : ℂ)
      (((1 / 2 : ℝ) : ℂ) * Complex.I) := by
  rintro ⟨a, b, n, hh⟩
  have him := congrArg Complex.im hh
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.intCast_re, Complex.intCast_im, mul_zero, zero_mul, add_zero,
    zero_add, mul_one] at him
  have h2 : ((2 * b : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h2' : (2 * b : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- **The two translation conditions are jointly realized.** -/
theorem thetaTranslation_nontorsion_nonresonant_witness :
    ∃ τ q h : ℂ, ThetaTranslationNontorsion τ q ∧ ThetaTranslationNonresonant τ q h :=
  ⟨Complex.I, ((Real.sqrt 2 : ℝ) : ℂ), ((1 / 2 : ℝ) : ℂ) * Complex.I,
    thetaTranslationNontorsion_I_sqrtTwo, thetaTranslationNonresonant_I_sqrtTwo_halfI⟩

end GaloisForLFunctions
