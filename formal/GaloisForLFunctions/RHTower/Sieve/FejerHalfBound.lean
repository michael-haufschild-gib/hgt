import GaloisForLFunctions.RHTower.Sieve.FejerPairing

/-!
# Bounding the half-interval Fejér transform

`‖∫_0^T (1 - t/T) e^{itL} dt‖ ≤ |L|^{-1} + 2/(TL²)`.

Both terms of the closed form `i/L - (e^{iTL} - 1)/(TL²)` are bounded separately: the first has
modulus exactly `|L|^{-1}`, the second at most `2/(TL²)`.

The `|L|^{-1}` term is the one that disappears on symmetrising — it is odd — so the *symmetric*
transform enjoys the pure `|L|^{-2}` decay of `FejerBounds.lean`.  On a half interval it survives,
and this is the honest bound there.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- **The half-interval Fejér transform is small at large frequencies.** -/
theorem norm_integral_fejerHalf_le (L : ℝ) (hL : L ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)‖
      ≤ 1 / |L| + 2 / (T * L ^ 2) := by
  have hLpos : (0 : ℝ) < |L| := abs_pos.mpr hL
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  rw [integral_fejerHalf L hL hT]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖Complex.I / (L : ℂ)‖ = 1 / |L| := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(Complex.exp (((T * L : ℝ) : ℂ) * Complex.I) - 1) / ((T : ℂ) * (L : ℂ) ^ 2)‖
      ≤ 2 / (T * L ^ 2) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    have hden : ‖((L : ℂ)) ^ 2‖ = L ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hden]
    have hnum : ‖Complex.exp (((T * L : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [Complex.norm_exp_ofReal_mul_I, norm_one]
      norm_num
    have hpos : (0 : ℝ) < T * L ^ 2 := by positivity
    gcongr
  rw [h1]
  linarith [h2]

end RHTower.Sieve
