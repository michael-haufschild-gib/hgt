import GaloisForLFunctions.RHTower.Sieve.DirichletGallagher

/-!
# Integrals of a pure phase

`∫_0^T e^{itL} dt` is `T` when `L = 0` and `(e^{iTL} - 1)/(iL)` otherwise, of modulus at most
`2/|L|`.

These are the cross-term integrals of `∫_0^T |F|²` for a Dirichlet polynomial: the diagonal terms
have `L = 0` and contribute `T ∑_n |a_n|²`, while the off-diagonal terms carry `L = log m - log n`
and are bounded by `2/|log(m/n)|`.  Extracting the diagonal from the mean square is exactly this
dichotomy.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- The phase is interval-integrable. -/
theorem intervalIntegrable_exp_phase (L : ℝ) (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ => Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      volume A B := by
  refine Continuous.intervalIntegrable ?_ A B
  fun_prop

/-- The phase at the trivial frequency. -/
theorem integral_exp_phase_zero (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Complex.exp (((t * (0 : ℝ) : ℝ) : ℂ) * Complex.I)) = (T : ℂ) := by
  have hone : ∀ t : ℝ, Complex.exp (((t * (0 : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
    intro t
    norm_num
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℂ)) (fun t _ => hone t)]
  simp

/-- **The phase integral at a nonzero frequency.** -/
theorem integral_exp_phase (L : ℝ) (hL : L ≠ 0) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      = (Complex.exp (((T * L : ℝ) : ℂ) * Complex.I) - 1) / ((L : ℂ) * Complex.I) := by
  have hne : ((L : ℂ) * Complex.I) ≠ 0 := by
    have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
    exact mul_ne_zero hL' Complex.I_ne_zero
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => Complex.exp (((s * L : ℝ) : ℂ) * Complex.I) / ((L : ℂ) * Complex.I))
      (Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)) t := by
    intro t
    have hd := (hasDerivAt_exp_phase L t).div_const ((L : ℂ) * Complex.I)
    have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
    have hval : Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) * ((L : ℂ) * Complex.I)
        / ((L : ℂ) * Complex.I) = Complex.exp (((t * L : ℝ) : ℂ) * Complex.I) := by
      field_simp
    rw [hval] at hd
    exact hd
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := T)
    (fun t _ => hderiv t) (intervalIntegrable_exp_phase L 0 T)
  rw [hFTC]
  have hzero : Complex.exp ((((0 : ℝ) * L : ℝ) : ℂ) * Complex.I) = 1 := by
    norm_num
  rw [hzero, sub_div]

/-- **The phase integral is small at a nonzero frequency.** -/
theorem norm_integral_exp_phase_le (L : ℝ) (hL : L ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / |L| := by
  rw [integral_exp_phase L hL T, norm_div, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs]
  have hnum : ‖Complex.exp (((T * L : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [Complex.norm_exp_ofReal_mul_I, norm_one]
    norm_num
  have hpos : (0 : ℝ) < |L| := abs_pos.mpr hL
  gcongr

end RHTower.Sieve
