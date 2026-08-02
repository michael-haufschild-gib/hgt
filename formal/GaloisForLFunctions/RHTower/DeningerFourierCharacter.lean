import GaloisForLFunctions.RHTower.DeningerSmoothCoeffInjective

/-!
# The characters of a period and the orthogonality relations

The character `exp (2πinx/T)` is smooth and periodic of period `T`, and the integral of a
nonconstant character over a period vanishes, because the character is the derivative of a
multiple of itself and takes the same value at both ends.  So the Fourier coefficients of a
character are the Kronecker delta.

The characters are therefore the basis vectors for which a smooth periodic function is the sum of
its coefficients.

* `deningerCharacter`, `_mem` : the characters as smooth periodic functions.
* `deningerCharacter_integral` : the integral of a nonconstant character over a period vanishes.
* `deningerFourierCoeff_character` : **the coefficients of a character are the Kronecker delta.**
-/

namespace RHTower

open Complex

section Character

variable {T : ℝ}

/-- The character `exp (2πinx/T)` of period `T`. -/
noncomputable def deningerCharacter (T : ℝ) (n : ℤ) : ℝ → ℂ :=
  deningerFourierKernel T (-n)

theorem deningerCharacter_apply (n : ℤ) (x : ℝ) :
    deningerCharacter T n x = Complex.exp (2 * Real.pi * Complex.I * n * x / T) := by
  rw [deningerCharacter, deningerFourierKernel]
  congr 1
  push_cast
  ring

theorem deningerCharacter_hasDerivAt (n : ℤ) (x : ℝ) :
    HasDerivAt (deningerCharacter T n)
      (2 * Real.pi * Complex.I * n / T * deningerCharacter T n x) x := by
  have h := deningerFourierKernel_hasDerivAt T (-n) x
  rw [deningerCharacter]
  convert h using 2
  push_cast
  ring

theorem deningerCharacter_periodic (hT : T ≠ 0) (n : ℤ) :
    deningerCharacter T n T = deningerCharacter T n 0 :=
  deningerFourierKernel_periodic T hT (-n)

/-- **The integral of a nonconstant character over a period vanishes.** -/
theorem deningerCharacter_integral (hT : T ≠ 0) {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..T, deningerCharacter T k x = 0 := by
  have hne : (2 * Real.pi * Complex.I * k / T : ℂ) ≠ 0 := by
    have h1 : (2 : ℂ) * Real.pi * Complex.I * k ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hk
    exact div_ne_zero h1 (by exact_mod_cast hT)
  set c : ℂ := (2 * Real.pi * Complex.I * k / T)⁻¹ with hc
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun y => c * deningerCharacter T k y) (deningerCharacter T k x) x := by
    intro x _
    have h := (deningerCharacter_hasDerivAt (T := T) k x).const_mul c
    refine h.congr_deriv ?_
    have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT
    rw [hc]
    field_simp
  have hcont : IntervalIntegrable (deningerCharacter T k) MeasureTheory.volume 0 T := by
    refine Continuous.intervalIntegrable ?_ _ _
    have hfun : deningerCharacter T k
        = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * k * x / T) :=
      funext (deningerCharacter_apply k)
    rw [hfun]
    refine Continuous.cexp ?_
    fun_prop
  have hfun := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [hfun, deningerCharacter_periodic hT k, sub_self]

/-- **The Fourier coefficients of a character are the Kronecker delta.** -/
theorem deningerFourierCoeff_character (hT : 0 < T) (n m : ℤ) :
    deningerFourierCoeff T (deningerCharacter T n) m = if m = n then 1 else 0 := by
  have hkernel : ∀ x : ℝ, deningerFourierKernel T m x * deningerCharacter T n x
      = deningerCharacter T (n - m) x := by
    intro x
    rw [deningerFourierKernel, deningerCharacter_apply, deningerCharacter_apply,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [deningerFourierCoeff, intervalIntegral.integral_congr fun x _ => hkernel x]
  by_cases hmn : m = n
  · subst hmn
    have hzero : ∀ x : ℝ, deningerCharacter T (m - m) x = 1 := by
      intro x
      rw [deningerCharacter_apply]
      simp
    have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    rw [intervalIntegral.integral_congr fun x _ => hzero x, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, mul_one, if_pos rfl]
    field_simp
  · have hk : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
    rw [deningerCharacter_integral hT.ne' hk, if_neg hmn, mul_zero]

end Character

end RHTower
