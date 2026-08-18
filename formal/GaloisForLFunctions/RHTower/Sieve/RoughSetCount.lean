import GaloisForLFunctions.RHTower.Sieve.RoughSetShiftBound

/-!
# The discarded set itself

At shift zero the pair sieve degenerates to the one-dimensional sieve: every prime divides `0`, so
the local class count is one everywhere and the Euler factor is `p/(p−1)` rather than its square.
The bounding sum is then at least `exp(mertensS h − mertensS P₁)/2`, and the count of the discarded
set is `≍ Y·log P₁/log h` — the classical sieve bound, obtained from the same machine.

This is the `d = 0` term of the fibre second moment, excluded from `Sieve/RoughShiftSum`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- At shift zero every local class count is one. -/
theorem pairClassCount_zero (p : ℕ) : pairClassCount 0 p = 1 := by
  rw [pairClassCount, if_pos (dvd_zero p)]

/-- **At shift zero the bounding sum is the one-dimensional Mertens product.** -/
theorem selbergBoundingSum_ge_mertens_zero (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (k : ℕ)
    {z : ℝ} (hz : 1 ≤ z) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount 0 p / ((p : ℝ) - pairClassCount 0 p))
        + Real.log 2 ≤ (k : ℝ)) :
    (1 / 2) * Real.exp (mertensS h - mertensS P₁)
      ≤ SelbergSieve.selbergBoundingSum (roughPairSieve Y hP₁ h 0 hz) := by
  classical
  refine le_trans ?_ (selbergBoundingSum_roughPairSieve_ge Y hP₁ 0 k hz hh1 hlev hk)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans (prod_rangePrimes_ge P₁ h hP₁h) (le_of_eq ?_)
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : 3 ≤ p := by omega
    exact_mod_cast this
  rw [pairClassCount_zero]
  have hne : ((p : ℝ) - 1) ≠ 0 := by linarith
  field_simp
  ring

/-- **The discarded set is small.**  The classical sieve bound, from the pair sieve at shift
zero. -/
theorem card_roughSet_le (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (k : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount 0 p / ((p : ℝ) - pairClassCount 0 p))
        + Real.log 2 ≤ (k : ℝ)) :
    (((roughSet P₁ h ⌊Y⌋₊).card : ℕ) : ℝ)
      ≤ Y / ((1 / 2) * Real.exp (mertensS h - mertensS P₁))
        + ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  set s : SelbergSieve := roughPairSieve Y hP₁ h 0 hz with hs
  set L : ℝ := (1 / 2) * Real.exp (mertensS h - mertensS P₁) with hL
  have hL0 : (0 : ℝ) < L := by
    rw [hL]
    have : (0 : ℝ) < Real.exp (mertensS h - mertensS P₁) := Real.exp_pos _
    linarith
  have hSge : L ≤ SelbergSieve.selbergBoundingSum s :=
    selbergBoundingSum_ge_mertens_zero Y hP₁ k hz hh1 hP₁h hlev hk
  have hSpos : 0 < SelbergSieve.selbergBoundingSum s := SelbergSieve.selbergBoundingSum_pos s
  have hbase := SelbergSieve.selberg_bound_simple s
  rw [siftedSum_roughPairSieve Y hP₁ h 0 hz] at hbase
  simp only [cardDistinctFactors_eq] at hbase
  have hset : (Finset.Icc 1 ⌊Y⌋₊).filter
      (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
        ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + 0))
      = roughSet P₁ h ⌊Y⌋₊ := by
    rw [roughSet]
    refine Finset.filter_congr fun m _ => ?_
    constructor
    · rintro ⟨h1, -⟩
      exact h1
    · intro h1
      refine ⟨h1, ?_⟩
      intro p hp
      rw [Nat.add_zero]
      exact h1 p hp
  rw [hset] at hbase
  refine hbase.trans (add_le_add ?_ ?_)
  · show Y / SelbergSieve.selbergBoundingSum s ≤ Y / L
    rw [div_le_div_iff₀ hSpos hL0]
    nlinarith [hSge, hY, hL0]
  · refine Finset.sum_le_sum fun e he => ?_
    rw [Nat.mem_divisors] at he
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact absurd (zero_dvd_iff.1 he.1) he.2
      · exact hpos
    have hsummand := selberg_summand_le Y hP₁ h 0 hz hY he1 he.1
    show (if ((e : ℕ) : ℝ) ≤ z then (3 : ℝ) ^ e.primeFactors.card
        * |BoundingSieve.rem (s := s.toBoundingSieve) e| else 0)
      ≤ (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)
    split_ifs with hle
    · exact hsummand
    · exact le_rfl

end

end RHTower.Sieve
