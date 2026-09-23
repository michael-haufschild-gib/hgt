import GaloisForLFunctions.RHTower.Sieve.FejerHalfBound

/-!
# The symmetric Fejér pairing is real and small

The sum of the half-interval transforms at `L` and `-L` is the real number
`(2 - 2 cos TL)/(TL²)`, so its modulus is bounded by both `4/(TL²)` and `T`.

This is the pairing a localisation argument must use.  The half-interval bound of
`FejerHalfBound.lean` carries a term `|L|^{-1}`, which is not summable over the frequencies `log n`;
symmetrising cancels it, and only then is the tail summable.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- The symmetric pairing is the cast of a real number. -/
theorem integral_fejer_symm_real (L : ℝ) (hL : L ≠ 0) {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      + (∫ t in (0 : ℝ)..T,
          ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * (-L) : ℝ) : ℂ) * Complex.I))
      = (((2 - 2 * Real.cos (T * L)) / (T * L ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [integral_fejer_symm L hL hT]
  push_cast [Complex.ofReal_cos]
  ring

/-- **The symmetric pairing decays in the frequency.** -/
theorem norm_integral_fejer_symm_le_inv (L : ℝ) (hL : L ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖(∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
        + (∫ t in (0 : ℝ)..T,
            ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * (-L) : ℝ) : ℂ) * Complex.I))‖
      ≤ 4 / (T * L ^ (2 : ℕ)) := by
  rw [integral_fejer_symm_real L hL hT, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejer_transform_nonneg L hT)]
  exact fejer_transform_le_inv L hL hT

/-- **The symmetric pairing is capped by the interval length.** -/
theorem norm_integral_fejer_symm_le_len (L : ℝ) (hL : L ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖(∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
        + (∫ t in (0 : ℝ)..T,
            ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * (-L) : ℝ) : ℂ) * Complex.I))‖
      ≤ T := by
  rw [integral_fejer_symm_real L hL hT, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejer_transform_nonneg L hT)]
  exact fejer_transform_le_len L hL hT

end RHTower.Sieve
