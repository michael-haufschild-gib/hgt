import GaloisForLFunctions.RHTower.Sieve.DirichletMVT

/-!
# The energy of the derivative coefficients

Differentiating a Dirichlet polynomial multiplies the `n`-th coefficient by `i log n`, so

`∑_{n < N} |i log n · a_n|² ≤ (log N)² ∑_{n < N} |a_n|²`,

the largest frequency being `log N`.  Combined with the mean value theorem this bounds
`∫_0^T |F'|²`, which is the second integral appearing in Gallagher's reduction for Dirichlet
polynomials.
-/

namespace RHTower.Sieve

open Finset

/-- The modulus of a derivative coefficient. -/
theorem norm_dirDerivCoeff (N : ℕ) (a : Fin N → ℂ) (n : Fin N) :
    ‖dirDerivCoeff N a n‖ = Real.log (((n : ℕ) : ℝ) + 1) * ‖a n‖ := by
  have hlog : (0 : ℝ) ≤ Real.log (((n : ℕ) : ℝ) + 1) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := by positivity
    linarith
  rw [dirDerivCoeff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg hlog]

/-- **The derivative coefficients carry at most `(log N)²` times the energy.** -/
theorem sum_normSq_dirDerivCoeff_le (N : ℕ) (a : Fin N → ℂ) :
    ∑ n : Fin N, ‖dirDerivCoeff N a n‖ ^ 2
      ≤ (Real.log N) ^ 2 * ∑ n : Fin N, ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hpos : (0 : ℝ) < ((n : ℕ) : ℝ) + 1 := by positivity
  have hle : ((n : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
    have := n.isLt
    exact_mod_cast this
  have hlog : (0 : ℝ) ≤ Real.log (((n : ℕ) : ℝ) + 1) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := by positivity
    linarith
  have hmono : Real.log (((n : ℕ) : ℝ) + 1) ≤ Real.log N := Real.log_le_log hpos hle
  rw [norm_dirDerivCoeff, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact pow_le_pow_left₀ hlog hmono 2

end RHTower.Sieve
