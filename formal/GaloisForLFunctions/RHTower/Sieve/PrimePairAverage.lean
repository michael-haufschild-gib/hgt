import GaloisForLFunctions.RHTower.Sieve.PrimePairShiftSum

/-!
# Prime pairs averaged over the shift

Summing the two-dimensional sieve bound of `Sieve/PrimePairCount` over the shifts `1 ≤ d ≤ K` and
inserting the average of the singular series (`Sieve/PrimePairShiftSum`) gives the estimate the
large-prime mean square consumes: the number of pairs of primes above the sifting range with
difference at most `K` is

```text
≤ 2e · K · Y / exp(mertensS h − mertensS P₁)²  +  K · (sieve remainder) ,
```

and `exp(mertensS h − mertensS P₁) ≍ log h / log P₁`, so the main term carries the two saved
logarithms.  Everything is explicit and uniform in `K`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The shift-uniform form of the level budget: the pair class count never exceeds two. -/
theorem pairClass_div_le (d : ℕ) {p : ℕ} (hp : (3 : ℝ) ≤ (p : ℝ)) :
    pairClassCount d p / ((p : ℝ) - pairClassCount d p) ≤ 2 / ((p : ℝ) - 2) := by
  rw [pairClassCount]
  split_ifs with hdvd
  · have h1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_le_div_iff₀ h2 h1]
    linarith
  · exact le_of_eq rfl

/-- The uniform level budget dominates every shift's budget. -/
theorem pairBudget_le {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) :
    (∑ p ∈ rangePrimes P₁ h, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
      ≤ ∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2) := by
  refine Finset.sum_le_sum fun p hp => ?_
  refine pairClass_div_le d ?_
  rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
  have : 3 ≤ p := by omega
  exact_mod_cast this

/-- **Prime pairs averaged over the shift.** -/
theorem sum_card_primePair_le (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (K k : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1 * (∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2)) + Real.log 2 ≤ (k : ℝ)) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((Finset.Icc 1 ⌊Y⌋₊).filter
            (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ)
      ≤ 2 * Real.exp 1 * (K : ℝ) * Y / (Real.exp (mertensS h - mertensS P₁)) ^ 2
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
  -- each shift, from the two-dimensional sieve
  have hterm : ∀ d : ℕ,
      ((((Finset.Icc 1 ⌊Y⌋₊).filter
            (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ)
        ≤ (2 * Y / E ^ 2)
            * (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
          + R := by
    intro d
    have hkd : Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ) := by
      have := pairBudget_le hP₁ h d
      have hpos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
      nlinarith [this, hpos]
    refine le_trans (card_primePair_le Y hP₁ d k hz hY hh1 hP₁h hlev hkd) ?_
    have hCd := hC0 d
    have hinv : (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
        = (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have h3 := hp3 p (Finset.mem_filter.1 hp).1
      rw [inv_div]
    rw [hinv]
    have hmain : Y / ((1 / 2) * (E ^ 2
          * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))))
        = (2 * Y / E ^ 2)
          * (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d),
              (((p : ℝ) - 1) / (p : ℝ)))⁻¹ := by
      field_simp
    rw [hmain]
  refine le_trans (Finset.sum_le_sum fun d _ => hterm d) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul]
  have hcard : ((K + 1 - 1 : ℕ) : ℝ) = (K : ℝ) := by
    congr 1
  rw [hcard]
  have hkey := sum_inv_shiftCorrection_le hP₁ h K
  have hcoef : (0 : ℝ) ≤ 2 * Y / E ^ 2 := by positivity
  have hstep : (2 * Y / E ^ 2)
      * ∑ d ∈ Finset.Icc 1 K,
          (∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), ((p : ℝ) / ((p : ℝ) - 1)))
      ≤ (2 * Y / E ^ 2) * (Real.exp 1 * (K : ℝ)) :=
    mul_le_mul_of_nonneg_left hkey hcoef
  have hfin : (2 * Y / E ^ 2) * (Real.exp 1 * (K : ℝ))
      = 2 * Real.exp 1 * (K : ℝ) * Y / E ^ 2 := by
    field_simp
  linarith [hstep, hfin.le, hfin.ge]

end

end RHTower.Sieve
