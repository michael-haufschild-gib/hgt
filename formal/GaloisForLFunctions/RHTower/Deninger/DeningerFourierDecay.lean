import GaloisForLFunctions.RHTower.Deninger.DeningerFourierCoeffDeriv

/-!
# Decay of the Fourier coefficients of a differentiable periodic function

The Fourier kernel has modulus one, so a Fourier coefficient is bounded by the supremum of the
function over one period.  Combined with the coefficient of the derivative, a periodic function
with bounded derivative has coefficients decaying like `1/|n|`, and iterating the argument gives
one power of `1/|n|` for every derivative.

* `deningerFourierKernel_norm` : the kernel has modulus one.
* `deningerFourierCoeff_norm_le` : a coefficient is bounded by the supremum over a period.
* `deningerFourierCoeff_norm_le_of_deriv` : **one power of decay per derivative.**
-/

namespace RHTower

open Complex MeasureTheory

section FourierDecay

theorem deningerFourierKernel_norm (T : ℝ) (n : ℤ) (x : ℝ) :
    ‖deningerFourierKernel T n x‖ = 1 := by
  rw [deningerFourierKernel]
  have harg : -(2 * Real.pi * Complex.I * n * x) / T
      = (-(2 * Real.pi * n * x / T) : ℝ) * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.norm_exp_ofReal_mul_I]

/-- **A Fourier coefficient is bounded by the supremum of the function over one period.** -/
theorem deningerFourierCoeff_norm_le {T : ℝ} (hT : 0 < T) {g : ℝ → ℂ} {M : ℝ}
    (hM : ∀ x ∈ Set.uIoc (0 : ℝ) T, ‖g x‖ ≤ M) (n : ℤ) :
    ‖deningerFourierCoeff T g n‖ ≤ M := by
  have hMnonneg : 0 ≤ M := by
    have hmem : (T / 2) ∈ Set.uIoc (0 : ℝ) T := by
      rw [Set.uIoc_of_le hT.le]
      constructor <;> [linarith; linarith]
    exact le_trans (norm_nonneg _) (hM _ hmem)
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) T,
      ‖deningerFourierKernel T n x * g x‖ ≤ M := by
    intro x hx
    rw [norm_mul, deningerFourierKernel_norm, one_mul]
    exact hM x hx
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [deningerFourierCoeff, norm_mul]
  have hTnorm : ‖(1 / T : ℂ)‖ = 1 / T := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  rw [hTnorm]
  have hfinal : ‖∫ x in (0 : ℝ)..T, deningerFourierKernel T n x * g x‖ ≤ M * T := by
    refine le_trans hint (le_of_eq ?_)
    rw [sub_zero, abs_of_pos hT]
  calc 1 / T * ‖∫ x in (0 : ℝ)..T, deningerFourierKernel T n x * g x‖
      ≤ 1 / T * (M * T) := by
        exact mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = M := by field_simp

/-- **One power of decay per derivative**: the coefficients of a periodic function with bounded
derivative decay like `1/|n|`. -/
theorem deningerFourierCoeff_norm_le_of_deriv {T : ℝ} (hT : 0 < T) {f f' : ℝ → ℂ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (hper : f T = f 0)
    {n : ℤ} (hn : n ≠ 0) {M : ℝ} (hM : ∀ x ∈ Set.uIoc (0 : ℝ) T, ‖f' x‖ ≤ M) :
    ‖deningerFourierCoeff T f n‖ ≤ T / (2 * Real.pi * |(n : ℝ)|) * M := by
  have hcoeff := deningerFourierCoeff_deriv hT.ne' hderiv hf' hper n
  have hne : (2 * Real.pi * Complex.I * n) / T ≠ 0 := by
    have h1 : (2 : ℂ) * Real.pi * Complex.I * n ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hn
    exact div_ne_zero h1 (by exact_mod_cast hT.ne')
  have hval : deningerFourierCoeff T f n
      = (T / (2 * Real.pi * Complex.I * n)) * deningerFourierCoeff T f' n := by
    rw [hcoeff]
    field_simp
    rw [mul_div_assoc, div_self (by exact_mod_cast hT.ne' : (T : ℂ) ≠ 0), mul_one]
  rw [hval, norm_mul]
  have hnorm : ‖(T / (2 * Real.pi * Complex.I * n) : ℂ)‖ = T / (2 * Real.pi * |(n : ℝ)|) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    congr 1
    simp [abs_of_pos Real.pi_pos, Complex.norm_intCast, mul_assoc]
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left (deningerFourierCoeff_norm_le hT hM n) ?_
  have hpi : 0 < Real.pi := Real.pi_pos
  have habs : 0 < |(n : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hn
  positivity

end FourierDecay

end RHTower
