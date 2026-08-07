import GaloisForLFunctions.RHTower.Sieve.HalaszFullSeriesSum
import Mathlib.NumberTheory.LSeries.Basic

/-!
# The Euler bound in the `LSeries` language

The corpus's trivial size bound for a bounded multiplicative Dirichlet series is stated for the sum of the
twisted summands `f(n)n^{-s}`.  Away from `s = 0` that sum is `LSeries f s` — the two differ only in the
term `n = 0`, where `LSeries` inserts `0` and the twisted summand carries `0^{-s} = 0`.  So

`‖L(f, s)‖ ≤ (1 + 1/(σ − 1))·e^{7/2}`,   `σ = Re s > 1`,

for every `f` with `f(1) = 1`, `‖f‖ ≤ 1` and multiplicativity on coprime arguments.  This is the pointwise
factor of the three-factor Cauchy–Schwarz split, in the form the Perron identity produces.
-/

noncomputable section
namespace RHTower.Sieve
open Complex

/-- The Dirichlet series is the sum of the twisted summands away from `s = 0`. -/
theorem LSeries_eq_tsum_twistedSummand {f : ℕ → ℂ} {s : ℂ} (hs : s ≠ 0) :
    LSeries f s = ∑' n : ℕ, twistedSummand f s n := by
  rw [LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_def, if_pos rfl, twistedSummand, Nat.cast_zero,
      Complex.zero_cpow (neg_ne_zero.2 hs), mul_zero]
  · rw [LSeries.term_def, if_neg hn, twistedSummand, Complex.cpow_neg, div_eq_mul_inv]

/-- **The Euler bound for a bounded multiplicative Dirichlet series.**  The corpus's trivial size bound,
in the `LSeries` language: for `‖f‖ ≤ 1` multiplicative on coprimes,

`‖L(f, s)‖ ≤ (1 + 1/(σ − 1))·e^{7/2}`,   `σ = Re s > 1`. -/
theorem norm_LSeries_le_trivial {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ (1 + 1 / (s.re - 1)) * Real.exp (7 / 2) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  rw [LSeries_eq_tsum_twistedSummand hs0]
  exact norm_tsum_twistedSummand_le_trivial hf1 hmul hbdd hs

/-- The Euler bound on a vertical line, with the frequency displayed. -/
theorem norm_LSeries_line_le_trivial {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    ‖LSeries f ((σ : ℂ) + (y : ℝ) * I)‖ ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by
  have hre : ((σ : ℂ) + (y : ℝ) * I).re = σ := by simp
  have h := norm_LSeries_le_trivial hf1 hmul hbdd (s := (σ : ℂ) + (y : ℝ) * I) (by rw [hre]; exact hσ)
  rwa [hre] at h

end RHTower.Sieve
end
