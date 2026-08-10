import Mathlib.Analysis.Fourier.AddCircle

/-!
# Translation and modulation laws for Fourier coefficients on the circle

Two elementary transport rules for `fourierCoeff` that mathlib does not record:

* translating the argument multiplies the coefficient by a character value,
  `fourierCoeff (f ∘ (· - y)) n = fourier (-n) y * fourierCoeff f n`;
* modulating by a character shifts the index,
  `fourierCoeff (fourier k * f) n = fourierCoeff f (n - k)`.

Both come from the character law `fourier n (x + y) = fourier n x * fourier n y` together with the
translation invariance of the Haar measure of the circle.
-/

open MeasureTheory AddCircle

namespace GaloisForLFunctions

variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in
/-- The exponential monomials are characters in the argument. -/
theorem fourier_add_arg (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp_rw [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

/-- **Translation law.**  Translating the argument multiplies the Fourier coefficient by a
character value. -/
theorem fourierCoeff_comp_sub (f : AddCircle T → ℂ) (n : ℤ) (y : AddCircle T) :
    fourierCoeff (fun x => f (x - y)) n = fourier (-n) y * fourierCoeff f n := by
  rw [fourierCoeff, fourierCoeff,
    ← MeasureTheory.integral_add_right_eq_self
      (fun x : AddCircle T => fourier (-n) x • f (x - y)) y]
  simp_rw [fourier_add_arg, add_sub_cancel_right, smul_eq_mul]
  have hre : ∀ x : AddCircle T, fourier (-n) x * fourier (-n) y * f x
      = fourier (-n) y * (fourier (-n) x * f x) := fun x => by ring
  simp_rw [hre]
  rw [MeasureTheory.integral_const_mul]

/-- Additive form of the translation law. -/
theorem fourierCoeff_comp_add (f : AddCircle T → ℂ) (n : ℤ) (y : AddCircle T) :
    fourierCoeff (fun x => f (x + y)) n = fourier n y * fourierCoeff f n := by
  have h := fourierCoeff_comp_sub f n (-y)
  simpa [sub_neg_eq_add, fourier_neg] using h

/-- **Modulation law.**  Multiplying by a character shifts the Fourier index. -/
theorem fourierCoeff_fourier_mul (f : AddCircle T → ℂ) (n k : ℤ) :
    fourierCoeff (fun x => fourier k x * f x) n = fourierCoeff f (n - k) := by
  rw [fourierCoeff, fourierCoeff]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hchar : fourier (-n) x * fourier k x = fourier (-(n - k)) x := by
    rw [show -(n - k) = -n + k by ring, fourier_add]
  simp only [smul_eq_mul, ← mul_assoc, hchar]

end GaloisForLFunctions
