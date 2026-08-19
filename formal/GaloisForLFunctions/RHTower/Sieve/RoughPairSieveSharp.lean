import GaloisForLFunctions.RHTower.Sieve.RankinPairCondition

/-!
# The bounding sum of the pair sieve, with the full two-logarithm saving

Truncating the Euler product by the *number* of prime factors forces the sieve level to exceed the
sifting bound raised to a power comparable to `log log`, and costs a factor `(log log)²` in the
saving.  Truncating by the *size* of the divisor — Rankin's device at the exponent `1/log h` — needs
only `level ≥ h^{18}`, so the sifting bound may be a fixed power of the level and the saving is the
full `(log h)²`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The real value of the divisor named by a set of primes. -/
theorem natProdR_eq_cast (t : Finset ℕ) : natProdR t = ((∏ p ∈ t, p : ℕ) : ℝ) := by
  rw [natProdR, Nat.cast_prod]

/-- **The bounding sum of the pair sieve keeps half its Euler product, at a fixed level ratio.** -/
theorem selbergBoundingSum_roughPairSieve_ge_sharp (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ}
    (d : ℕ) {z : ℝ} (hz : 1 ≤ z) (hh2 : 2 ≤ h)
    (hlev : ((h : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    (1 / 2) * ∏ p ∈ rangePrimes P₁ h,
        (pairClassCount d p / ((p : ℝ) - pairClassCount d p) + 1)
      ≤ SelbergSieve.selbergBoundingSum (roughPairSieve Y hP₁ h d hz) := by
  classical
  set s : Finset ℕ := rangePrimes P₁ h with hs
  set a : ℕ → ℝ := fun p => pairClassCount d p / ((p : ℝ) - pairClassCount d p) with ha
  set D : ℝ := ((h : ℝ)) ^ (18 : ℝ) with hD
  have hh1R : (1 : ℝ) < (h : ℝ) := by exact_mod_cast hh2
  have hlogh : (0 : ℝ) < Real.log h := Real.log_pos hh1R
  have hD0 : (0 : ℝ) < D := Real.rpow_pos_of_pos (by linarith) _
  have hprime : ∀ p ∈ s, p.Prime := fun p hp => rangePrimes_prime hp
  have hp3 : ∀ p ∈ s, (3 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rw [hs, rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have ha0 : ∀ p ∈ s, 0 ≤ a p := by
    intro p hp
    have h3 := hp3 p hp
    have hc : pairClassCount d p ≤ 2 ∧ 0 ≤ pairClassCount d p := by
      rw [pairClassCount]; constructor <;> split_ifs <;> norm_num
    rw [ha]
    exact div_nonneg hc.2 (by linarith [hc.1])
  have hp1 : ∀ p ∈ s, 1 ≤ p := fun p hp => (hprime p hp).one_lt.le
  have hcond := rankin_pairSieve_condition (P₁ := P₁) (h := h) hP₁ hh2 hlog d
  refine le_trans (sum_powerset_prod_le_ge ha0 hp1 (α := 1 / Real.log h) (D := D)
    (by positivity) hD0 hcond) ?_
  -- reindex the truncated powerset sum back into the bounding sum
  have hinj : Set.InjOn (fun t => ∏ p ∈ t, p)
      ((s.powerset.filter (fun t => natProdR t ≤ D) : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro t ht u hu hEq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at ht hu
    have h1 : (∏ p ∈ t, p).primeFactors = t :=
      Nat.primeFactors_prod fun p hp => hprime p (ht.1 hp)
    have h2 : (∏ p ∈ u, p).primeFactors = u :=
      Nat.primeFactors_prod fun p hp => hprime p (hu.1 hp)
    rw [← h1, ← h2]
    exact congrArg Nat.primeFactors hEq
  set G : ℕ → ℝ := fun l =>
    if (l : ℝ) ^ 2 ≤ z then
      SelbergSieve.selbergTerms (roughPairSieve Y hP₁ h d hz).toBoundingSieve l else 0 with hG
  have hterm : ∀ t ∈ s.powerset.filter (fun t => natProdR t ≤ D),
      (∏ p ∈ t, a p) = G (∏ p ∈ t, p) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    have hdvd : (∏ p ∈ t, p) ∣ rangePrimorial P₁ h := by
      rw [rangePrimorial, ← hs]
      exact Finset.prod_dvd_prod_of_subset _ _ _ ht.1
    have h0 : (∏ p ∈ t, p) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      exact (hprime p (ht.1 hp)).ne_zero
    have hsize : (((∏ p ∈ t, p : ℕ)) : ℝ) ^ 2 ≤ z := by
      have hle : (((∏ p ∈ t, p : ℕ)) : ℝ) ≤ Real.sqrt z := by
        rw [← natProdR_eq_cast]
        exact le_trans ht.2 hlev
      have hnn : (0 : ℝ) ≤ (((∏ p ∈ t, p : ℕ)) : ℝ) := Nat.cast_nonneg _
      have hsq : (((∏ p ∈ t, p : ℕ)) : ℝ) ^ 2 ≤ (Real.sqrt z) ^ 2 :=
        pow_le_pow_left₀ hnn hle 2
      rwa [Real.sq_sqrt (by linarith : (0:ℝ) ≤ z)] at hsq
    rw [hG]
    simp only
    rw [if_pos hsize, selbergTerms_roughPairSieve Y hP₁ h d hz hdvd h0,
      Nat.primeFactors_prod fun p hp => hprime p (ht.1 hp)]
  show _ ≤ ∑ l ∈ (rangePrimorial P₁ h).divisors, G l
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro l hl
    rw [Finset.mem_image] at hl
    obtain ⟨t, ht, rfl⟩ := hl
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    refine Nat.mem_divisors.2 ⟨?_, ?_⟩
    · rw [rangePrimorial, ← hs]
      exact Finset.prod_dvd_prod_of_subset _ _ _ ht.1
    · refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      exact (hprime p hp).ne_zero
  · intro l hl _
    rw [Nat.mem_divisors] at hl
    have hl0 : l ≠ 0 := by
      intro hc
      exact hl.2 (by rw [hc] at hl; exact zero_dvd_iff.1 hl.1)
    rw [hG]
    simp only
    split_ifs
    · exact selbergTerms_roughPairSieve_nonneg Y hP₁ h d hz hl.1 hl0
    · exact le_rfl

end

end RHTower.Sieve
