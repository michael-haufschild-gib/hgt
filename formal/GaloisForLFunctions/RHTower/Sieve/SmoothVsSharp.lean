import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothLittleO

/-!
# The smoothed sum against the sharp sum

The cutoff is `1` below `N` and `0` above `N + H`, so the smoothed Möbius sum and the sharp sum
`∑_{n ≤ N} μ(n)` differ only over the transition window, where the summand is at most `1` in modulus.
The window contains at most `H + 1` integers, so

    ‖ ∑ₙ μ(n)·w(n) - ∑_{n ≤ N} μ(n) ‖ ≤ H + 1.

This is the only step that compares the two sums, and it is entirely elementary — no analysis enters.
-/

namespace RHTower.Sieve

open Complex GaloisForLFunctions.HTGeometry

/-- **The smoothed and sharp sums of a unimodular sequence differ by at most the window length.** -/
theorem norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    ‖(∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n‖
      ≤ H + 1 := by
  set f : ℕ → ℂ := fun n => a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ) with hfdef
  have hmu : ∀ n : ℕ, ‖a n‖ ≤ 1 := ha
  have hfle : ∀ n : ℕ, ‖f n‖ ≤ 1 := by
    intro n
    simp only [hfdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothWeight_nonneg N H _)]
    have h1 := hmu n
    have h2 := smoothWeight_le_one N H (n : ℝ)
    have h3 : (0 : ℝ) ≤ smoothWeight N H (n : ℝ) := smoothWeight_nonneg N H _
    nlinarith [norm_nonneg (a n)]
  -- the sum is supported below `⌊N+H⌋₊ + 1`
  have hzero : ∀ n : ℕ, n ∉ Finset.range (⌊N + H⌋₊ + 1) → f n = 0 := by
    intro n hn
    have hlt : ⌊N + H⌋₊ < n := by
      simpa [Finset.mem_range, Nat.lt_succ_iff] using hn
    have hge : N + H ≤ (n : ℝ) := by
      have h := Nat.lt_floor_add_one (N + H)
      have hcast : ((⌊N + H⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
      linarith
    simp only [hfdef]
    rw [smoothWeight_eq_zero hH hge]
    simp
  have hsum : (∑' n : ℕ, f n) = ∑ n ∈ Finset.range (⌊N + H⌋₊ + 1), f n := tsum_eq_sum hzero
  -- the two ranges are nested
  have hNH : ⌊N⌋₊ ≤ ⌊N + H⌋₊ := Nat.floor_le_floor (by linarith)
  have hAB : ⌊N⌋₊ + 1 ≤ ⌊N + H⌋₊ + 1 := by omega
  have hsplit : (∑ n ∈ Finset.Ico 0 (⌊N⌋₊ + 1), f n)
      + (∑ n ∈ Finset.Ico (⌊N⌋₊ + 1) (⌊N + H⌋₊ + 1), f n)
      = ∑ n ∈ Finset.Ico 0 (⌊N + H⌋₊ + 1), f n :=
    Finset.sum_Ico_consecutive f (Nat.zero_le _) hAB
  -- on the lower range the cutoff is one
  have hone : ∑ n ∈ Finset.Ico 0 (⌊N⌋₊ + 1), f n
      = ∑ n ∈ Finset.Ico 0 (⌊N⌋₊ + 1), a n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnle : n ≤ ⌊N⌋₊ := by
      simpa [Finset.mem_Ico, Nat.lt_succ_iff] using hn
    have hcast : (n : ℝ) ≤ N := by
      have h1 : ((n : ℕ) : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnle
      have h2 : ((⌊N⌋₊ : ℕ) : ℝ) ≤ N := Nat.floor_le hN.le
      linarith
    simp only [hfdef]
    rw [smoothWeight_eq_one hH hcast]
    simp
  -- the difference is the window sum
  have hdiff : (∑' n : ℕ, f n)
      - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n
      = ∑ n ∈ Finset.Ico (⌊N⌋₊ + 1) (⌊N + H⌋₊ + 1), f n := by
    rw [hsum, Finset.range_eq_Ico, Finset.range_eq_Ico, ← hsplit, hone]
    ring
  rw [hdiff]
  -- the window contains at most `H + 1` integers
  have hcard : ((⌊N + H⌋₊ + 1 - (⌊N⌋₊ + 1) : ℕ) : ℝ) ≤ H + 1 := by
    have hub : ((⌊N + H⌋₊ : ℕ) : ℝ) ≤ N + H := Nat.floor_le (by linarith)
    have hlb : N - 1 < ((⌊N⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one N
      linarith
    have hle : (⌊N + H⌋₊ + 1 - (⌊N⌋₊ + 1) : ℕ) ≤ ⌊N + H⌋₊ - ⌊N⌋₊ := by omega
    have hcast : ((⌊N + H⌋₊ - ⌊N⌋₊ : ℕ) : ℝ) ≤ ((⌊N + H⌋₊ : ℕ) : ℝ) - ((⌊N⌋₊ : ℕ) : ℝ) := by
      rcases le_or_gt (⌊N⌋₊) (⌊N + H⌋₊) with h | h
      · rw [Nat.cast_sub h]
      · omega
    have hcast2 : ((⌊N + H⌋₊ + 1 - (⌊N⌋₊ + 1) : ℕ) : ℝ) ≤ ((⌊N + H⌋₊ - ⌊N⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hle
    linarith
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 (fun n _ => hfle n)) ?_
  rw [Nat.card_Ico, nsmul_eq_mul, mul_one]
  exact hcard

/-- **The smoothed and sharp Möbius sums differ by at most the window length.** -/
theorem norm_tsum_smoothWeight_sub_sum_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖
      ≤ H + 1 := by
  refine norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one ?_ hN hH
  intro n
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

end RHTower.Sieve
