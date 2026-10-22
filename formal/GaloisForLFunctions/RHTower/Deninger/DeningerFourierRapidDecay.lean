import GaloisForLFunctions.RHTower.Deninger.DeningerFourierDecay

/-!
# Rapid decay of the Fourier coefficients of a smooth periodic function

The coefficient of the derivative being `2πin/T` times the coefficient, the modulus of a
coefficient is exactly `T/(2π|n|)` times that of the coefficient of the derivative.  Iterating
along a sequence of successive derivatives gives one factor `T/(2π|n|)` for each derivative, and
bounding the last one by its supremum over a period gives decay faster than any power of `1/|n|`.

* `deningerFourierCoeff_norm_eq_of_deriv` : the exact one-step relation of moduli.
* `deningerFourierCoeff_iterate_norm` : the `k`-fold relation.
* `deningerFourierCoeff_rapid_decay` : **decay of order `k` for a function with `k` derivatives.**
-/

namespace RHTower

open Complex

section RapidDecay

/-- **The exact one-step relation between the moduli of the coefficients of a function and of its
derivative.** -/
theorem deningerFourierCoeff_norm_eq_of_deriv {T : ℝ} (hT : 0 < T) {f f' : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (hper : f T = f 0)
    {n : ℤ} (hn : n ≠ 0) :
    ‖deningerFourierCoeff T f n‖
      = T / (2 * Real.pi * |(n : ℝ)|) * ‖deningerFourierCoeff T f' n‖ := by
  have hcoeff := deningerFourierCoeff_deriv hT.ne' hderiv hf' hper n
  have habs : 0 < |(n : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hn
  have hnorm : ‖(2 * Real.pi * Complex.I * n / T : ℂ)‖ = 2 * Real.pi * |(n : ℝ)| / T := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    congr 1
    simp [abs_of_pos Real.pi_pos, Complex.norm_intCast, mul_assoc]
  have hrel : ‖deningerFourierCoeff T f' n‖
      = 2 * Real.pi * |(n : ℝ)| / T * ‖deningerFourierCoeff T f n‖ := by
    rw [hcoeff, norm_mul, hnorm]
  rw [hrel]
  field_simp

/-- **The `k`-fold relation** between the modulus of a coefficient and that of the coefficient of
the `k`-th derivative. -/
theorem deningerFourierCoeff_iterate_norm {T : ℝ} (hT : 0 < T) (f : ℕ → ℝ → ℂ)
    (hderiv : ∀ k x, HasDerivAt (f k) (f (k + 1) x) x) (hcont : ∀ k, Continuous (f k))
    (hper : ∀ k, f k T = f k 0) {n : ℤ} (hn : n ≠ 0) (k : ℕ) :
    ‖deningerFourierCoeff T (f 0) n‖
      = (T / (2 * Real.pi * |(n : ℝ)|)) ^ k * ‖deningerFourierCoeff T (f k) n‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : ‖deningerFourierCoeff T (f k) n‖
          = T / (2 * Real.pi * |(n : ℝ)|) * ‖deningerFourierCoeff T (f (k + 1)) n‖ :=
        deningerFourierCoeff_norm_eq_of_deriv hT (hderiv k) (hcont (k + 1)) (hper k) hn
      rw [ih, hstep]
      ring

/-- **Decay of order `k`**: a periodic function with `k` successive derivatives has coefficients
bounded by `(T/(2π|n|))^k` times a bound for the `k`-th derivative. -/
theorem deningerFourierCoeff_rapid_decay {T : ℝ} (hT : 0 < T) (f : ℕ → ℝ → ℂ)
    (hderiv : ∀ k x, HasDerivAt (f k) (f (k + 1) x) x) (hcont : ∀ k, Continuous (f k))
    (hper : ∀ k, f k T = f k 0) {n : ℤ} (hn : n ≠ 0) (k : ℕ) {M : ℝ}
    (hM : ∀ x ∈ Set.uIoc (0 : ℝ) T, ‖f k x‖ ≤ M) :
    ‖deningerFourierCoeff T (f 0) n‖ ≤ (T / (2 * Real.pi * |(n : ℝ)|)) ^ k * M := by
  rw [deningerFourierCoeff_iterate_norm hT f hderiv hcont hper hn k]
  have habs : 0 < |(n : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hn
  have hpow : (0 : ℝ) ≤ (T / (2 * Real.pi * |(n : ℝ)|)) ^ k := by
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  exact mul_le_mul_of_nonneg_left (deningerFourierCoeff_norm_le hT hM n) hpow

end RapidDecay

end RHTower
