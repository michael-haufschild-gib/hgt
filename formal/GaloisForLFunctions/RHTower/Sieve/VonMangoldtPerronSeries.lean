import Mathlib
import GaloisForLFunctions.RHTower.Sieve.PerronInfiniteSeries

/-!
# The von Mangoldt Dirichlet series in Perron form

The Perron formula for an infinite series is stated with the factor `n^{-s}`; the `LSeries` of
mathlib uses `f n / n^s`.  They agree termwise away from `n = 0`, where both vanish, so the
von Mangoldt series is `−ζ'/ζ` in the form the Perron formula consumes.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

noncomputable section

theorem tsum_vonMangoldt_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * ((n : ℂ) ^ (-s)) = -deriv riemannZeta s / riemannZeta s := by
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]

/-- The Perron summability hypothesis for the von Mangoldt coefficients. -/
theorem summable_vonMangoldt_perron {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖((Λ n : ℝ) : ℂ)‖ * (x / n) ^ σ) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simpa using hσ)).norm
  have heq : (fun n : ℕ => ‖((Λ n : ℝ) : ℂ)‖ * (x / n) ^ σ)
      = fun n : ℕ => x ^ σ * ‖LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) (σ : ℂ) n‖ := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [LSeries.term_zero, norm_zero, mul_zero]
      have hz : (x / ((0 : ℕ) : ℝ)) = 0 := by simp
      rw [hz, Real.zero_rpow (by linarith : σ ≠ 0), mul_zero]
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero (by omega), norm_div,
        Complex.norm_natCast_cpow_of_pos hn]
      have hre : ((σ : ℂ)).re = σ := by simp
      rw [hre, Real.div_rpow hx.le hn0.le]
      have hnpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn0 σ
      field_simp
  rw [heq]
  exact h.mul_left _

end

end RHTower.Sieve
