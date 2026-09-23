import GaloisForLFunctions.RHTower.Sieve.Section4Block

/-!
# The measure of a block's exceptional set (Lemma 2.5)

The exceptional set of exposé §4 is the set of frequencies at which a short prime polynomial fails
to cancel.  Lemma 2.5 bounds its measure by raising the polynomial to a free power `k`: the `k`-fold
convolution of a prime-supported coefficient has `ℓ²`-norm at most `k^k` times the `k`-th power of
the coefficient energy, so Chebyshev against the mean value theorem gives

```text
   V^{2k}·|E|  ≤  2·(T + 4·N^k(1 + log N^k))·k^k·(#B)^k .
```

Choosing `k ≈ log T / log N` makes `N^k ≍ T`, which is what makes the bound useful.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The energy of a prime block's coefficient family is its cardinality. -/
theorem sum_normSq_finCoeff_le_card {B : Finset ℕ} {NA : ℕ} :
    (∑ n : Fin NA, ‖finCoeff B moebiusCoeff NA n‖ ^ (2 : ℕ)) ≤ (B.card : ℝ) := by
  classical
  have hterm : ∀ n : Fin NA, ‖finCoeff B moebiusCoeff NA n‖ ^ (2 : ℕ)
      ≤ (if ((n : ℕ) + 1) ∈ B then (1 : ℝ) else 0) := by
    intro n
    rw [finCoeff, restrictCoeff]
    by_cases h : ((n : ℕ) + 1) ∈ B
    · rw [if_pos h, if_pos h]
      have := norm_moebiusCoeff_le_one ((n : ℕ) + 1)
      nlinarith [norm_nonneg (moebiusCoeff ((n : ℕ) + 1))]
    · rw [if_neg h, if_neg h]
      simp
  refine (Finset.sum_le_sum fun n _ => hterm n).trans ?_
  rw [Finset.sum_boole]
  have hcard : ((Finset.univ.filter (fun n : Fin NA => ((n : ℕ) + 1) ∈ B)).card : ℕ) ≤ B.card := by
    refine Finset.card_le_card_of_injOn (fun n : Fin NA => (n : ℕ) + 1) ?_ ?_
    · intro n hn
      exact (Finset.mem_filter.1 hn).2
    · intro x _ y _ hxy
      have h : (x : ℕ) + 1 = (y : ℕ) + 1 := hxy
      exact Fin.ext (by omega)
  exact_mod_cast hcard

/-- The coefficient family of a prime block is prime-supported. -/
theorem finCoeff_prime_support {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {NA : ℕ} :
    ∀ n : Fin NA, finCoeff B moebiusCoeff NA n ≠ 0 → Nat.Prime ((n : ℕ) + 1) := by
  intro n hn
  rw [finCoeff, restrictCoeff] at hn
  by_cases h : ((n : ℕ) + 1) ∈ B
  · exact hB _ h
  · rw [if_neg h] at hn
    exact absurd rfl hn

/-- **Lemma 2.5 for one prime block.**  The measure of the exceptional set, at a free power. -/
theorem volume_blockExceptional_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {NA k : ℕ}
    (hk : 1 ≤ k) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V) :
    volume.real (blockExceptional B moebiusCoeff NA T V)
      ≤ 2 * ((T + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * ((k : ℝ) ^ k * (B.card : ℝ) ^ k)) / V ^ (2 * k) := by
  classical
  have hbase := volume_largeValues_pow_symm_le_of_prime_support k NA hk
    (finCoeff B moebiusCoeff NA) (finCoeff_prime_support hB) hT hV.le
  have hset : {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly NA (finCoeff B moebiusCoeff NA) t‖}
      = blockExceptional B moebiusCoeff NA T V := rfl
  rw [hset] at hbase
  have hVk : (0 : ℝ) < V ^ (2 * k) := by positivity
  rw [le_div_iff₀ hVk]
  refine le_trans (le_of_eq (by ring)) (hbase.trans ?_)
  have hfac : (0 : ℝ) ≤ T + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)) := by
    have hlog : (0 : ℝ) ≤ Real.log ((NA ^ k : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hc : (0 : ℝ) ≤ ((NA ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hT, hlog, hc]
  have henergy : (∑ n : Fin NA, ‖finCoeff B moebiusCoeff NA n‖ ^ (2 : ℕ)) ^ k ≤ (B.card : ℝ) ^ k := by
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => by positivity)
      sum_normSq_finCoeff_le_card k
  have hkk : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
  have hstep : (k : ℝ) ^ k * (∑ n : Fin NA, ‖finCoeff B moebiusCoeff NA n‖ ^ (2 : ℕ)) ^ k
      ≤ (k : ℝ) ^ k * (B.card : ℝ) ^ k := mul_le_mul_of_nonneg_left henergy hkk
  nlinarith [hstep, hfac]

end

end RHTower.Sieve
