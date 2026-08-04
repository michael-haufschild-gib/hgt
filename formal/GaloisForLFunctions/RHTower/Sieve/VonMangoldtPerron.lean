import GaloisForLFunctions.RHTower.Sieve.PerronSummable
import GaloisForLFunctions.RHTower.Sieve.MoebiusPerron
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The smoothed Perron formula for the von Mangoldt function

Mathlib proves `LSeriesSummable ↗Λ s` for `re s > 1`, and summability of a complex series over `ℕ`
is absolute, so the hypothesis of `tsum_mul_smoothWeight_eq_integral_summable` holds for `Λ`.  The
smoothed Chebyshev sum is therefore a vertical integral of `-ζ'/ζ` against the cutoff's transform.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- Absolute summability of the terms, from `LSeriesSummable`. -/
theorem summable_norm_mul_rpow_of_LSeriesSummable {a : ℕ → ℂ} {σ : ℝ} (hσ : 0 < σ)
    (h : LSeriesSummable a (σ : ℂ)) :
    Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-σ) := by
  have habs : Summable fun n : ℕ => ‖LSeries.term a (σ : ℂ) n‖ := summable_norm_iff.2 h
  refine habs.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero, norm_zero, Nat.cast_zero,
      Real.zero_rpow (by linarith : -σ ≠ 0), mul_zero]
  · rw [LSeries.term_of_ne_zero (by omega), norm_div,
      Complex.norm_natCast_cpow_of_pos hn]
    have hre : ((σ : ℂ)).re = σ := by simp
    rw [hre, Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv]

/-- The von Mangoldt coefficients are absolutely summable on every line right of the abscissa. -/
theorem summable_vonMangoldt_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖((vonMangoldt n : ℝ) : ℂ)‖ * (n : ℝ) ^ (-σ) := by
  refine summable_norm_mul_rpow_of_LSeriesSummable (by linarith) ?_
  refine LSeriesSummable_vonMangoldt ?_
  simpa using hσ

/-- **The smoothed Chebyshev sum as a vertical integral.** -/
theorem tsum_vonMangoldt_smoothWeight_eq_integral {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {σ : ℝ} (hσ : 1 < σ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (∑' n : ℕ,
          ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * Complex.I))) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I) :=
  tsum_mul_smoothWeight_eq_integral_summable (by simp) hN hH hσ (summable_vonMangoldt_rpow hσ)

/-- **The Perron integrand is the negated logarithmic derivative.**  On `re s > 1` the von Mangoldt
Dirichlet series is `-ζ'/ζ`. -/
theorem tsum_vonMangoldt_cpow_eq {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-s))
      = -(deriv riemannZeta s) / riemannZeta s := by
  rw [tsum_cpow_neg_eq_LSeries (by simp) s]
  exact LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

end RHTower.Sieve
