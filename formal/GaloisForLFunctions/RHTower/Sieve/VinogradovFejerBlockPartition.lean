import GaloisForLFunctions.RHTower.Sieve.VinogradovSeparatedBlock

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Partition the nonnegative difference range into consecutive
half-denominator blocks.  Each block is separated by the rational
approximation, while the quotient count retains the essential `G / q`
gain. -/
theorem sum_finiteFejerKernel_range_le_blockCost
    {H q a G : ℕ} (hH : H ≠ 0) (hq : 0 < q)
    {α : ℝ} (hcop : Nat.Coprime a q)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ Finset.range (G + 1),
      finiteFejerKernel H (α * (n : ℝ))) ≤
      ((G / ((q + 1) / 2) + 1 : ℕ) : ℝ) *
        vinogradovSeparatedBlockCost H q := by
  classical
  let L : ℕ := (q + 1) / 2
  let B : ℕ := G / L + 1
  have hL : 0 < L := by
    dsimp [L]
    omega
  have hmaps : ∀ n ∈ Finset.range (G + 1), n / L ∈ Finset.range B := by
    intro n hn
    rw [Finset.mem_range] at hn ⊢
    have hnG : n ≤ G := by omega
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hnG)
  have hgroup :
      (∑ r ∈ Finset.range B,
        ∑ n ∈ (Finset.range (G + 1)).filter (fun n => n / L = r),
          finiteFejerKernel H (α * (n : ℝ))) =
        ∑ n ∈ Finset.range (G + 1),
          finiteFejerKernel H (α * (n : ℝ)) :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  rw [← hgroup]
  calc
    (∑ r ∈ Finset.range B,
        ∑ n ∈ (Finset.range (G + 1)).filter (fun n => n / L = r),
          finiteFejerKernel H (α * (n : ℝ))) ≤
        ∑ _r ∈ Finset.range B, vinogradovSeparatedBlockCost H q := by
      apply Finset.sum_le_sum
      intro r _
      apply sum_finiteFejerKernel_halfBlock_le hH hq hcop happrox
      intro n hn m hm
      rw [Finset.mem_filter] at hn hm
      have hquot : n / L = m / L := hn.2.trans hm.2.symm
      have hnmod : n % L < L := Nat.mod_lt n hL
      have hmmod : m % L < L := Nat.mod_lt m hL
      have hnrep : n = L * (n / L) + n % L := (Nat.div_add_mod n L).symm
      have hmrep : m = L * (m / L) + m % L := (Nat.div_add_mod m L).symm
      have hncast : (n : ℝ) =
          (L : ℝ) * ((n / L : ℕ) : ℝ) + ((n % L : ℕ) : ℝ) := by
        exact_mod_cast hnrep
      have hmcast : (m : ℝ) =
          (L : ℝ) * ((m / L : ℕ) : ℝ) + ((m % L : ℕ) : ℝ) := by
        exact_mod_cast hmrep
      have hdiff :
          ((n : ℝ) - (m : ℝ)) =
            ((n % L : ℕ) : ℝ) - (m % L : ℕ) := by
        rw [hncast, hmcast, hquot]
        ring
      rw [hdiff]
      have hnmodle : ((n % L : ℕ) : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : n % L ≤ L - 1)
      have hmmodle : ((m % L : ℕ) : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : m % L ≤ L - 1)
      have hnmod0 : (0 : ℝ) ≤ ((n % L : ℕ) : ℝ) := by positivity
      have hmmod0 : (0 : ℝ) ≤ ((m % L : ℕ) : ℝ) := by positivity
      have hmodabs :
          |((n % L : ℕ) : ℝ) - (m % L : ℕ)| ≤ ((L - 1 : ℕ) : ℝ) := by
        rw [abs_le]
        constructor <;> linarith
      have htwice : 2 * (L - 1) ≤ q := by
        dsimp [L]
        omega
      have hhalf : ((L - 1 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
        have htwiceR : (2 : ℝ) * (L - 1 : ℕ) ≤ q := by
          exact_mod_cast htwice
        linarith
      exact hmodabs.trans hhalf
    _ = (B : ℝ) * vinogradovSeparatedBlockCost H q := by
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
    _ = ((G / ((q + 1) / 2) + 1 : ℕ) : ℝ) *
        vinogradovSeparatedBlockCost H q := by rfl

end

end RHTower.Sieve
