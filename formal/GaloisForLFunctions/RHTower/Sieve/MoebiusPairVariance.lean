import GaloisForLFunctions.RHTower.Sieve.MoebiusWindowVariance

/-!
# The variance of μ against squarefree pair counts

Since `‖μ(n)‖` is the squarefree indicator, the autocorrelation form of the short-interval variance
reads, for `μ` and with `R = X + L + 1`,

`∑_{x < X} ‖∑_{x < n ≤ x+L} μ(n)‖² ≤ L·Q(R) + 2 ∑_{h=1}^{R-1} (L-h) · P_h(R)`,

where `Q(R) = #{n < R : n squarefree}` and `P_h(R) = #{n < R-h : n and n+h both squarefree}`.

This is the sharpest form the elementary theory reaches.  The triangular weight `L - h` restricts the
sum to shifts `h < L`, the diagonal is the squarefree count, and each off-diagonal term is bounded by
the *size of its support* — no cancellation between `μ(n)` and `μ(n+h)` is used anywhere.  Supplying
that cancellation is the correlation input the whole reduction is waiting on.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- `‖μ(n)‖` is the squarefree indicator. -/
theorem norm_moebiusC_eq_indicator (n : ℕ) :
    ‖moebiusC n‖ = if Squarefree n then 1 else 0 := by
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

/-- The shifted mass of μ is the squarefree pair count. -/
theorem sum_norm_moebiusC_shift_eq_card (R h : ℕ) :
    ∑ n ∈ Finset.range R, ‖moebiusC n‖ * ‖moebiusC (n + h)‖
      = (((Finset.range R).filter (fun n => Squarefree n ∧ Squarefree (n + h))).card : ℝ) := by
  classical
  have hterm : ∀ n ∈ Finset.range R, ‖moebiusC n‖ * ‖moebiusC (n + h)‖
      = if Squarefree n ∧ Squarefree (n + h) then 1 else 0 := by
    intro n _
    rw [norm_moebiusC_eq_indicator, norm_moebiusC_eq_indicator]
    by_cases h1 : Squarefree n
    · by_cases h2 : Squarefree (n + h)
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, mul_one]
      · rw [if_pos h1, if_neg h2, mul_zero, if_neg (fun hc => h2 hc.2)]
    · rw [if_neg h1, zero_mul, if_neg (fun hc => h1 hc.1)]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The variance of μ against squarefree pair counts.** -/
theorem sum_normSq_window_moebius_le_pairs (X L : ℕ) :
    ∑ x ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc x (x + L), moebiusC n‖ ^ (2 : ℕ)
      ≤ (L : ℝ) * (((Finset.range (X + L + 1)).filter (fun n => Squarefree n)).card : ℝ)
        + 2 * ∑ h ∈ Finset.Ico 1 (X + L + 1), ((L - h : ℕ) : ℝ)
            * (((Finset.range (X + L + 1 - h)).filter
                (fun n => Squarefree n ∧ Squarefree (n + h))).card : ℝ) := by
  have h := sum_normSq_window_le_autocorrelation moebiusC X L
  rw [sum_normSq_moebiusC_eq_card] at h
  refine le_trans h (le_of_eq ?_)
  congr 1
  refine congrArg (fun s => 2 * s) (Finset.sum_congr rfl fun k _ => ?_)
  rw [sum_norm_moebiusC_shift_eq_card]

end RHTower.Sieve
