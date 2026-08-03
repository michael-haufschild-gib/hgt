import GaloisForLFunctions.RHTower.Sieve.DirichletPairing

/-!
# The symmetric phase integral

`∫_{-T}^{T} e^{itL} dt = 2 sin(TL)/L` for `L ≠ 0`, and `2T` for `L = 0`.

Paired with a Dirichlet polynomial through `integral_dirPoly_mul`, this is the Dirichlet kernel:
`∫_{-T}^{T} F(t) dt = ∑_n a_n · 2 sin(T log n)/log n`, and after twisting by `x^{-it}` the
frequencies become `log(n/x)`, so the kernel concentrates on `n ≈ x` with width `e^{1/T}`.  Its
modulus is at most `min(2T, 2/|L|)`, which is what makes the far frequencies negligible.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- The difference of conjugate phases. -/
theorem exp_phase_sub_neg (θ : ℝ) :
    Complex.exp (((θ : ℝ) : ℂ) * Complex.I) - Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
      = 2 * Complex.sin ((θ : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The symmetric phase integral at the trivial frequency. -/
theorem integral_exp_phase_symm_zero (T : ℝ) :
    (∫ t in (-T)..T, Complex.exp (((t * (0 : ℝ) : ℝ) : ℂ) * Complex.I)) = ((2 * T : ℝ) : ℂ) := by
  have hone : ∀ t : ℝ, Complex.exp (((t * (0 : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
    intro t
    norm_num
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℂ)) (fun t _ => hone t)]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  ring

/-- **The symmetric phase integral is the Dirichlet kernel.** -/
theorem integral_exp_phase_symm (L : ℝ) (hL : L ≠ 0) (T : ℝ) :
    (∫ t in (-T)..T, Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      = 2 * ((Real.sin (T * L) : ℝ) : ℂ) / (L : ℂ) := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hne : ((L : ℂ) * Complex.I) ≠ 0 := mul_ne_zero hL' Complex.I_ne_zero
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (((s * L : ℝ) : ℂ) * Complex.I) / ((L : ℂ) * Complex.I))
      (Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)) t := by
    intro t
    have hd := (hasDerivAt_exp_phase L t).div_const ((L : ℂ) * Complex.I)
    have hval : Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * ((L : ℂ) * Complex.I)
        / ((L : ℂ) * Complex.I) = Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) := by
      field_simp
    rw [hval] at hd
    exact hd
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -T) (b := T)
    (fun t _ => hderiv t) (intervalIntegrable_exp_phase L (-T) T)
  rw [hFTC]
  have hsub : Complex.exp (((T * L : ℝ) : ℂ) * Complex.I) / ((L : ℂ) * Complex.I)
      - Complex.exp ((((-T) * L : ℝ) : ℂ) * Complex.I) / ((L : ℂ) * Complex.I)
      = (Complex.exp ((((T * L : ℝ)) : ℂ) * Complex.I)
          - Complex.exp (((-(T * L) : ℝ) : ℂ) * Complex.I)) / ((L : ℂ) * Complex.I) := by
    rw [← sub_div]
    congr 3
    push_cast
    ring
  rw [hsub, exp_phase_sub_neg (T * L), ← Complex.ofReal_sin]
  field_simp

end RHTower.Sieve
