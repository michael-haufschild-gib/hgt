import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition
/-!
# The trivial size of a finitely supported Dirichlet series

Every phase has modulus one, so on the line `Re s = σ` a finitely supported series is bounded by the `ℓ¹` mass
of its damped coefficients:

`‖L(a, σ+iy)‖ ≤ ∑_{n ∈ s} ‖a_n‖ n^{−σ}`,

uniformly in `y`.  For a product of three series — two finitely supported, one merely bounded — this gives the
constant that the tail of a truncated vertical integral consumes: the tail is charged to the trivial size of the
integrand times the kernel's decay, and no mean square enters there.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- **The trivial size of a finitely supported Dirichlet series on a vertical line.**  The `ℓ¹` mass of the
damped coefficients: every phase has modulus one. -/
theorem norm_LSeries_le_sum_of_support {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ y : ℝ) :
    ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ≤ ∑ n ∈ s, ‖a n‖ * (n : ℝ) ^ (-σ) := by
  classical
  rw [LSeries_eq_sum_term_of_support hsupp]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : n ≠ 0 := fun h => hs0 (h ▸ hn)
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  rw [LSeries.term_def, if_neg hn0, div_eq_mul_inv, ← Complex.cpow_neg,
    natCast_cpow_neg_eq hn1 σ y, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hnpos.le _)]
  have hphase : ‖Complex.exp (((2 * Real.pi * ((-y / (2 * Real.pi)) * Real.log n) : ℝ) : ℂ) * I)‖
      = 1 := by
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [hphase, mul_one]

/-- The `ℓ¹` mass of the damped coefficients is nonnegative. -/
theorem sum_norm_mul_rpow_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) :
    0 ≤ ∑ n ∈ s, ‖a n‖ * (n : ℝ) ^ (-σ) :=
  Finset.sum_nonneg fun n _ => by positivity

/-- **The trivial size of the product of three series.**  Two finitely supported factors by their `ℓ¹` mass,
one bounded factor by its bound: the constant the tail of a truncated vertical integral consumes. -/
theorem norm_LSeries_mul_three_le {a b f : ℕ → ℂ} {sa sb : Finset ℕ} {Mf σ : ℝ}
    (hsa0 : 0 ∉ sa) (hsuppa : ∀ n : ℕ, a n ≠ 0 → n ∈ sa)
    (hsb0 : 0 ∉ sb) (hsuppb : ∀ n : ℕ, b n ≠ 0 → n ∈ sb)
    (hMf : ∀ y : ℝ, ‖LSeries f ((σ : ℂ) + (y : ℝ) * I)‖ ≤ Mf) (y : ℝ) :
    ‖LSeries a ((σ : ℂ) + (y : ℝ) * I) * LSeries b ((σ : ℂ) + (y : ℝ) * I)
        * LSeries f ((σ : ℂ) + (y : ℝ) * I)‖
      ≤ (∑ n ∈ sa, ‖a n‖ * (n : ℝ) ^ (-σ)) * (∑ n ∈ sb, ‖b n‖ * (n : ℝ) ^ (-σ)) * Mf := by
  rw [norm_mul, norm_mul]
  refine mul_le_mul (mul_le_mul (norm_LSeries_le_sum_of_support hsa0 hsuppa σ y)
    (norm_LSeries_le_sum_of_support hsb0 hsuppb σ y) (norm_nonneg _)
    (sum_norm_mul_rpow_nonneg a sa σ)) (hMf y) (norm_nonneg _) ?_
  exact mul_nonneg (sum_norm_mul_rpow_nonneg a sa σ) (sum_norm_mul_rpow_nonneg b sb σ)

end RHTower.Sieve
end
