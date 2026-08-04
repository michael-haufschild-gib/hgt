import GaloisForLFunctions.RHTower.Sieve.CutoffMass
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtPerron

/-!
# The smoothed Chebyshev sum against the sharp one

The cutoff is `1` below `N` and `0` above `N + H`, so the smoothed and sharp Chebyshev sums differ
only over the transition window.  Unlike the Möbius case the summand is not bounded by `1` there but
by `Λ(n) ≤ log n ≤ log(N+H)`, so the comparison costs `(H+1)·log(N+H)` rather than `H+1`.

That extra logarithm is the only difference between the two routes' comparison steps, and it is
absorbed by taking the smoothing width smaller by a factor of a logarithm.
-/

namespace RHTower.Sieve

open Complex Finset ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The smoothed and sharp Chebyshev sums differ by at most the window mass.** -/
theorem norm_tsum_vonMangoldt_smoothWeight_sub_sum_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hNH1 : 1 ≤ N + H) :
    ‖(∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)‖
      ≤ (H + 1) * Real.log (N + H) := by
  set f : ℕ → ℂ := fun n =>
    ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ) with hfdef
  have hlog0 : (0 : ℝ) ≤ Real.log (N + H) := Real.log_nonneg hNH1
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
  have hNHle : ⌊N⌋₊ ≤ ⌊N + H⌋₊ := Nat.floor_le_floor (by linarith)
  have hAB : ⌊N⌋₊ + 1 ≤ ⌊N + H⌋₊ + 1 := by omega
  have hsplit : (∑ n ∈ Finset.Ico 0 (⌊N⌋₊ + 1), f n)
      + (∑ n ∈ Finset.Ico (⌊N⌋₊ + 1) (⌊N + H⌋₊ + 1), f n)
      = ∑ n ∈ Finset.Ico 0 (⌊N + H⌋₊ + 1), f n :=
    Finset.sum_Ico_consecutive f (Nat.zero_le _) hAB
  have hone : ∑ n ∈ Finset.Ico 0 (⌊N⌋₊ + 1), f n
      = ∑ n ∈ Finset.Ico 0 (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ) := by
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
  have hdiff : (∑' n : ℕ, f n)
      - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)
      = ∑ n ∈ Finset.Ico (⌊N⌋₊ + 1) (⌊N + H⌋₊ + 1), f n := by
    rw [hsum, Finset.range_eq_Ico, Finset.range_eq_Ico, ← hsplit, hone]
    ring
  rw [hdiff]
  -- each term of the window is at most `log (N+H)`
  have hterm : ∀ n ∈ Finset.Ico (⌊N⌋₊ + 1) (⌊N + H⌋₊ + 1), ‖f n‖ ≤ Real.log (N + H) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hnle : (n : ℝ) ≤ N + H := by
      have h1 : n ≤ ⌊N + H⌋₊ := by omega
      have h2 : ((n : ℕ) : ℝ) ≤ ((⌊N + H⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      have h3 : ((⌊N + H⌋₊ : ℕ) : ℝ) ≤ N + H := Nat.floor_le (by linarith)
      linarith
    have hΛ : (vonMangoldt n : ℝ) ≤ Real.log (N + H) := by
      refine le_trans vonMangoldt_le_log ?_
      refine Real.log_le_log ?_ hnle
      have : (1 : ℕ) ≤ n := by omega
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    have hΛ0 : (0 : ℝ) ≤ (vonMangoldt n : ℝ) := vonMangoldt_nonneg
    simp only [hfdef]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hΛ0, abs_of_nonneg (smoothWeight_nonneg N H _)]
    have hw := smoothWeight_le_one N H (n : ℝ)
    have hw0 := smoothWeight_nonneg N H (n : ℝ)
    nlinarith [hΛ, hΛ0, hw, hw0]
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
  refine le_trans (Finset.sum_le_card_nsmul _ _ (Real.log (N + H)) hterm) ?_
  rw [Nat.card_Ico, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard hlog0

end RHTower.Sieve
