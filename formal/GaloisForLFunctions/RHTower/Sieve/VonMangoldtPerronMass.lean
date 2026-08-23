import GaloisForLFunctions.RHTower.Sieve.ChebyshevMasterInequality
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSeriesBound

/-!
# The Perron error for the von Mangoldt coefficients

The Dirichlet mass `∑ Λ(n)(x/n)^σ` factors as `x^σ` times the real von Mangoldt series, which the
corpus bounds by `8/(σ−1)²`; the near part costs only `log 2x` per term because `Λ(n) ≤ log n`.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

noncomputable section

/-- The Dirichlet mass of the von Mangoldt coefficients factors. -/
theorem tsum_vonMangoldt_mass_le {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    ∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ * (x / n) ^ σ ≤ x ^ σ * (8 / (σ - 1) ^ 2) := by
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  have heq : (fun n : ℕ => ‖((Λ n : ℝ) : ℂ)‖ * (x / n) ^ σ)
      = fun n : ℕ => x ^ σ * ((Λ n : ℝ) * ((n : ℝ) ^ (-σ))) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz : (x / ((0 : ℕ) : ℝ)) = 0 := by simp
      rw [hz, Real.zero_rpow (by linarith : σ ≠ 0)]
      simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
        Real.div_rpow hx.le hn0.le, Real.rpow_neg hn0.le]
      field_simp
  rw [heq, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_vonMangoldt_rpow_neg_le hσ hσ2) hxσ.le

/-- The von Mangoldt coefficients are logarithmically bounded on the near window. -/
theorem vonMangoldt_le_log_window {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : (n : ℝ) ≤ 2 * x) :
    ‖((Λ n : ℝ) : ℂ)‖ ≤ Real.log (2 * x) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  refine le_trans vonMangoldt_le_log ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
    exact Real.log_nonneg (by linarith)
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
    exact Real.log_le_log (by linarith) hn

end

end RHTower.Sieve
