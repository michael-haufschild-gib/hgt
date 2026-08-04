import GaloisForLFunctions.RHTower.Sieve.ChebyshevSaving
import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound

/-!
# The Dirichlet series at the right abscissa

The truncation error carries the value of the von Mangoldt series at the right abscissa.  The corpus
bounds it by `8/(d-1)²`, so at `d = 1 + w` it is `8/w²` — a power of `log x`, harmless against the
truncation height.

Only the form differs from the corpus statement: the contour argument writes `Λ(n)·n^{-d}` and the
series bound writes `Λ(n)/n^d`.  They agree termwise, including at `n = 0` where both vanish.
-/

namespace RHTower.Sieve

open ArithmeticFunction

/-- **The von Mangoldt series at the right abscissa.** -/
theorem tsum_vonMangoldt_rpow_neg_le {d : ℝ} (h1 : 1 < d) (h2 : d ≤ 2) :
    ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d) ≤ 8 / (d - 1) ^ 2 := by
  have hcongr : ∀ n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)
      = (vonMangoldt n : ℝ) / (n : ℝ) ^ d := by
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  rw [tsum_congr hcongr]
  exact RHTower.tsum_vonMangoldt_div_rpow_le h1 h2

end RHTower.Sieve
