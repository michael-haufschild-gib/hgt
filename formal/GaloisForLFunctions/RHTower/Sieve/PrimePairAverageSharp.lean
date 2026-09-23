import GaloisForLFunctions.RHTower.Sieve.RoughPairSieveSharp
import GaloisForLFunctions.RHTower.Sieve.PrimePairAverage
import GaloisForLFunctions.RHTower.Sieve.MarkerPairBudget

/-!
# Shifted prime pairs on average, with the full two-logarithm saving

The whole chain of `Sieve/RoughPairSieveBound` → `Sieve/RoughPairCount` → `Sieve/PrimePairCount` →
`Sieve/PrimePairAverage` is unchanged except for the bounding-sum estimate.  Replacing the
prime-factor-count truncation by Rankin's size truncation lets the sifting bound be a fixed root of
the level, so the saving is `(log h)²` with `log h ≍ log(level)`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The bounding sum of the pair sieve in Mertens terms, at a fixed level ratio.** -/
theorem selbergBoundingSum_ge_mertens_sharp (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (d : ℕ)
    {z : ℝ} (hz : 1 ≤ z) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    (1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ)
        * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)))
      ≤ SelbergSieve.selbergBoundingSum (roughPairSieve Y hP₁ h d hz) := by
  classical
  have hp3 : ∀ p ∈ rangePrimes P₁ h, 3 ≤ p := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    omega
  have hC0 : (0 : ℝ) ≤ ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d),
      (((p : ℝ) - 1) / (p : ℝ)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by
      have := hp3 p (Finset.mem_filter.1 hp).1
      exact_mod_cast this
    exact div_nonneg (by linarith) (by linarith)
  have hmert := prod_rangePrimes_ge P₁ h hP₁h
  have hexp0 : (0 : ℝ) < Real.exp (mertensS h - mertensS P₁) := Real.exp_pos _
  have hsq : Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ)
      ≤ (∏ p ∈ rangePrimes P₁ h, ((p : ℝ) / ((p : ℝ) - 1))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hexp0.le hmert 2
  have heuler := prod_pairFactor_ge d hp3
  have hstep : Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ)
        * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))
      ≤ ∏ p ∈ rangePrimes P₁ h,
          (pairClassCount d p / ((p : ℝ) - pairClassCount d p) + 1) := by
    refine le_trans (mul_le_mul_of_nonneg_right hsq hC0) heuler
  refine le_trans (mul_le_mul_of_nonneg_left hstep (by norm_num)) ?_
  exact selbergBoundingSum_roughPairSieve_ge_sharp Y hP₁ d hz hh2 hlev hlog

/-- **The shifted rough pair count, at a fixed level ratio.** -/
theorem card_roughPair_le_sharp (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (d : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    ((((Finset.Icc 1 ⌊Y⌋₊).filter
          (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
            ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d))).card : ℕ) : ℝ)
      ≤ Y / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ)
            * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))))
        + ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  set s : SelbergSieve := roughPairSieve Y hP₁ h d hz with hs
  set C : ℝ := ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)) with hC
  have hp3 : ∀ p ∈ rangePrimes P₁ h, (3 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hC0 : (0 : ℝ) < C := by
    rw [hC]
    refine Finset.prod_pos fun p hp => ?_
    have h3 := hp3 p (Finset.mem_filter.1 hp).1
    have hnum : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hden : (0 : ℝ) < (p : ℝ) := by linarith
    positivity
  set L : ℝ := (1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ) * C) with hL
  have hL0 : (0 : ℝ) < L := by
    rw [hL]
    have : (0 : ℝ) < Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ) := by positivity
    positivity
  have hSge : L ≤ SelbergSieve.selbergBoundingSum s :=
    selbergBoundingSum_ge_mertens_sharp Y hP₁ d hz hh2 hP₁h hlev hlog
  have hSpos : 0 < SelbergSieve.selbergBoundingSum s := SelbergSieve.selbergBoundingSum_pos s
  have hbase := SelbergSieve.selberg_bound_simple s
  rw [siftedSum_roughPairSieve Y hP₁ h d hz] at hbase
  simp only [cardDistinctFactors_eq] at hbase
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
    have hsummand := selberg_summand_le Y hP₁ h d hz hY he1 he.1
    show (if ((e : ℕ) : ℝ) ≤ z then (3 : ℝ) ^ e.primeFactors.card
        * |BoundingSieve.rem (s := s.toBoundingSieve) e| else 0)
      ≤ (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)
    split_ifs with hle
    · exact hsummand
    · exact le_rfl

/-- **The two-dimensional sieve for prime pairs, at a fixed level ratio.** -/
theorem card_primePair_le_sharp (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (d : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    ((((Finset.Icc 1 ⌊Y⌋₊).filter
          (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ)
      ≤ Y / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ)
            * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))))
        + ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  refine le_trans ?_ (card_roughPair_le_sharp Y hP₁ d hz hY hh2 hP₁h hlev hlog)
  exact_mod_cast Nat.cast_le.2 (Finset.card_le_card (primePair_subset_roughPair Y P₁ h d))

/-- **Prime pairs averaged over the shift, at a fixed level ratio.** -/
theorem sum_card_primePair_le_sharp (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (K : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((Finset.Icc 1 ⌊Y⌋₊).filter
            (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ)
      ≤ 2 * Real.exp 1 * (K : ℝ) * Y / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
        + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  set E : ℝ := Real.exp (mertensS h - mertensS P₁) with hE
  set R : ℝ := ∑ e ∈ (rangePrimorial P₁ h).divisors,
      (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) with hR
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hp3 : ∀ p ∈ rangePrimes P₁ h, (3 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hC0 : ∀ d : ℕ, (0 : ℝ)
      < ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)) := by
    intro d
    refine Finset.prod_pos fun p hp => ?_
    have h3 := hp3 p (Finset.mem_filter.1 hp).1
    have hnum : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hden : (0 : ℝ) < (p : ℝ) := by linarith
    positivity
  have hterm : ∀ d : ℕ,
      ((((Finset.Icc 1 ⌊Y⌋₊).filter
            (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ)
        ≤ (2 * Y / E ^ (2 : ℕ))
            * (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
          + R := by
    intro d
    refine le_trans (card_primePair_le_sharp Y hP₁ d hz hY hh2 hP₁h hlev hlog) ?_
    have hCd := hC0 d
    have hinv : (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
        = (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [inv_div]
    refine add_le_add ?_ le_rfl
    rw [hinv]
    have hval : Y / ((1 / 2) * (E ^ (2 : ℕ)
          * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))))
        = (2 * Y / E ^ (2 : ℕ))
          * (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d),
              (((p : ℝ) - 1) / (p : ℝ)))⁻¹ := by
      field_simp
    rw [hval]
  refine le_trans (Finset.sum_le_sum fun d _ => hterm d) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hK : ((K + 1 - 1 : ℕ) : ℝ) = (K : ℝ) := by
    congr 1
  rw [hK]
  refine add_le_add ?_ le_rfl
  rw [← Finset.mul_sum]
  have hbound : ∑ d ∈ Finset.Icc 1 K,
      (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ Real.exp 1 * (K : ℝ) := sum_inv_shiftCorrection_le hP₁ h K
  have hcoef : (0 : ℝ) ≤ 2 * Y / E ^ (2 : ℕ) := by positivity
  calc (2 * Y / E ^ (2 : ℕ)) * ∑ d ∈ Finset.Icc 1 K,
        (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ (2 * Y / E ^ (2 : ℕ)) * (Real.exp 1 * (K : ℝ)) := mul_le_mul_of_nonneg_left hbound hcoef
    _ = 2 * Real.exp 1 * (K : ℝ) * Y / E ^ (2 : ℕ) := by ring

/-- **The shifted-pair budget of a marker block, at a fixed level ratio.** -/
theorem sum_card_shift_bigPrimeSet_le_sieve_sharp {M₀ b : ℕ} {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ}
    (K : ℕ) {z : ℝ} (hz : 1 ≤ z) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h) (hhM : h ≤ M₀)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet M₀ b).filter
          (fun p => p + d ∈ bigPrimeSet M₀ b)).card : ℕ) : ℝ)
      ≤ 2 * Real.exp 1 * (K : ℝ) * (b : ℝ) / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
        + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  have hfloor : ⌊((b : ℕ) : ℝ)⌋₊ = b := Nat.floor_natCast _
  have hsieve := sum_card_primePair_le_sharp ((b : ℕ) : ℝ) hP₁ K hz (Nat.cast_nonneg b) hh2
    hP₁h hlev hlog
  rw [hfloor] at hsieve
  exact le_trans (sum_card_shift_bigPrimeSet_le hhM K) hsieve

end

end RHTower.Sieve
