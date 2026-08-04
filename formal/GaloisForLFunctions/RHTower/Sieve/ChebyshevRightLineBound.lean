import GaloisForLFunctions.RHTower.Sieve.ChebyshevSmoothVsSharp

/-!
# The Chebyshev integrand on the Perron line

Right of the abscissa the Dirichlet series converges absolutely and its coefficients are
nonnegative, so the integrand is bounded by its own value at the real point:

    ‖(-ζ'/ζ)(d + iy)‖ ≤ ∑ₙ Λ(n)·n^{-d}     for all `y`.

This is the uniform bound the truncation error needs on the right line — the analogue of
`norm_LSeries_moebius_le_uniform`, and cheaper, because positivity of `Λ` makes the triangle
inequality sharp at `y = 0`.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

/-- The norm of a von Mangoldt term on a vertical line. -/
theorem norm_vonMangoldt_term {d y : ℝ} (n : ℕ) :
    ‖((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-((d : ℂ) + (y : ℝ) * Complex.I))‖
      = (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vonMangoldt_nonneg (n := n)),
      Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp

/-- **The Chebyshev integrand is bounded on the Perron line.** -/
theorem norm_neg_logDeriv_le_line {d y : ℝ} (hd : 1 < d) :
    ‖-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
        / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d) := by
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  have heq := tsum_vonMangoldt_cpow_eq (s := (d : ℂ) + (y : ℝ) * Complex.I) (by rw [hre]; exact hd)
  have hsummable : Summable fun n : ℕ =>
      ‖((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-((d : ℂ) + (y : ℝ) * Complex.I))‖ := by
    refine (summable_vonMangoldt_rpow hd).congr fun n => ?_
    rw [norm_vonMangoldt_term]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (vonMangoldt_nonneg (n := n))]
  rw [← heq]
  refine le_trans (norm_tsum_le_tsum_norm hsummable) (le_of_eq ?_)
  exact tsum_congr fun n => norm_vonMangoldt_term n

/-- The bounding series is nonnegative. -/
theorem tsum_vonMangoldt_rpow_nonneg {d : ℝ} :
    0 ≤ ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d) := by
  refine tsum_nonneg fun n => ?_
  have h1 : (0 : ℝ) ≤ (vonMangoldt n : ℝ) := vonMangoldt_nonneg
  have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-d) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  positivity

end RHTower.Sieve
