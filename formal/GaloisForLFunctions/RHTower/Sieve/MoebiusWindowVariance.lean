import GaloisForLFunctions.RHTower.Sieve.WindowAutocorrelation
import GaloisForLFunctions.RHTower.Sieve.MoebiusEulerDamping

/-!
# The short-interval variance of μ is carried by the squarefree numbers

`‖μ(n)‖² = 1` exactly on the squarefree integers and `0` elsewhere, so the diagonal of the variance
identity counts squarefree numbers rather than all integers:

`∑_{x < X} ‖∑_{x < n ≤ x+L} μ(n)‖² ≤ L² · #{n < X+L+1 : n squarefree}`.

Against the trivial bound `L²·R` this is a saving by the squarefree density `6/π²`
(`RHTower.Sieve.squarefreeDensity_eq`), and it is the *only* saving available without a correlation
estimate: the kernel is exact, and the off-diagonal terms are bounded here only by their support.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- `‖μ(n)‖²` is the squarefree indicator. -/
theorem normSq_moebiusC_eq_indicator (n : ℕ) :
    ‖moebiusC n‖ ^ 2 = if Squarefree n then 1 else 0 := by
  classical
  by_cases hsf : Squarefree n
  · rw [if_pos hsf]
    have hne : moebius n ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    rcases moebius_ne_zero_iff_eq_or.mp hne with h | h <;>
      · rw [moebiusC, h]
        norm_num
  · rw [if_neg hsf]
    have hz : moebius n = 0 := by
      by_contra hne
      exact hsf (moebius_ne_zero_iff_squarefree.mp hne)
    rw [moebiusC, hz]
    norm_num

/-- The squared mass of μ over a range is the squarefree count. -/
theorem sum_normSq_moebiusC_eq_card (R : ℕ) :
    ∑ n ∈ Finset.range R, ‖moebiusC n‖ ^ 2
      = (((Finset.range R).filter (fun n => Squarefree n)).card : ℝ) := by
  classical
  rw [Finset.sum_congr rfl fun n _ => normSq_moebiusC_eq_indicator n, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The short-interval variance of μ is carried by the squarefree numbers.** -/
theorem sum_normSq_window_moebius_le (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), moebiusC n‖ ^ 2
      ≤ (L : ℝ) ^ 2
        * (((Finset.range (X + L + 1)).filter (fun n => Squarefree n)).card : ℝ) := by
  have h := sum_normSq_window_le moebiusC X L
  rwa [sum_normSq_moebiusC_eq_card] at h

end RHTower.Sieve
