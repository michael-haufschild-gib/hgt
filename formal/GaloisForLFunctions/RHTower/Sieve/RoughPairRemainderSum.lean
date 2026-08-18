import GaloisForLFunctions.RHTower.Sieve.RoughPairSieveRemainder

/-!
# The remainder sum of the shifted-pair sieve

The Selberg bound pays `∑_{e ≤ y, e ∣ P} 3^{ω(e)}|R e|`.  With `|R e| ≤ 2·#roots(e) ≤ 2^{ω(e)+1}`
the summand is at most `2·6^{ω(e)}`, and since every prime of the modulus exceeds `P₁`, a divisor
`e ≤ y` has at most `log y / log P₁` prime factors.  So `6^{ω(e)} ≤ y^{log 6/log P₁}`, which is
`y^{o(1)}` in the range where the argument is applied: no divisor-sum estimate is needed at all.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The root count is at most `2^ω`.** -/
theorem rootCount_le_two_pow {e : ℕ} (hsq : Squarefree e) (d : ℕ) :
    ((quadraticCongruenceRootCountTotal e (d : ℤ) : ℕ) : ℝ) ≤ 2 ^ e.primeFactors.card := by
  rw [rootCountTotal_eq_pairClassCount_prod hsq d]
  calc ∏ p ∈ e.primeFactors, pairClassCount d p
      ≤ ∏ _p ∈ e.primeFactors, (2 : ℝ) := by
        refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
        · rw [pairClassCount]; split_ifs <;> norm_num
        · rw [pairClassCount]; split_ifs <;> norm_num
    _ = 2 ^ e.primeFactors.card := by rw [Finset.prod_const]

/-- **A divisor of the modulus has few prime factors.**  Every prime of the modulus exceeds `P₁`,
and their product is the divisor itself. -/
theorem card_primeFactors_le_log {P₁ h : ℕ} (hP₁ : 2 ≤ P₁) {e : ℕ}
    (hdvd : e ∣ rangePrimorial P₁ h) {N : ℕ} (heN : e ≤ N) :
    ((e.primeFactors.card : ℕ) : ℝ) ≤ Real.log N / Real.log P₁ := by
  classical
  have hP₁R : (2 : ℝ) ≤ (P₁ : ℝ) := by exact_mod_cast hP₁
  have hP₁1 : (1 : ℝ) < (P₁ : ℝ) := by linarith
  have hlogP : 0 < Real.log (P₁ : ℝ) := Real.log_pos hP₁1
  have hsq : Squarefree e := Squarefree.squarefree_of_dvd hdvd (rangePrimorial_squarefree P₁ h)
  have hge : ∀ p ∈ e.primeFactors, P₁ ≤ p := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpP : p ∣ rangePrimorial P₁ h := (Nat.dvd_of_mem_primeFactors hp).trans hdvd
    have hmem : p ∈ rangePrimes P₁ h :=
      mem_of_prime_dvd_prod (fun q hq => rangePrimes_prime hq) hprime hpP
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hmem
    omega
  have hprod : ∏ p ∈ e.primeFactors, p = e := Nat.prod_primeFactors_of_squarefree hsq
  have hpow : P₁ ^ e.primeFactors.card ≤ e := by
    calc P₁ ^ e.primeFactors.card = ∏ _p ∈ e.primeFactors, P₁ := by
          rw [Finset.prod_const]
      _ ≤ ∏ p ∈ e.primeFactors, p := Finset.prod_le_prod' hge
      _ = e := hprod
  have hpowR : ((P₁ : ℝ)) ^ e.primeFactors.card ≤ (N : ℝ) := by
    have h1 : ((P₁ ^ e.primeFactors.card : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
      exact_mod_cast le_trans hpow heN
    calc ((P₁ : ℝ)) ^ e.primeFactors.card = ((P₁ ^ e.primeFactors.card : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ (N : ℝ) := h1
  have hlog : ((e.primeFactors.card : ℕ) : ℝ) * Real.log (P₁ : ℝ) ≤ Real.log (N : ℝ) := by
    have hpos : (0 : ℝ) < ((P₁ : ℝ)) ^ e.primeFactors.card := by positivity
    have := Real.log_le_log hpos hpowR
    rwa [Real.log_pow] at this
  rw [le_div_iff₀ hlogP]
  exact hlog

/-- **The Selberg summand of the pair sieve.** -/
theorem selberg_summand_le (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) {z : ℝ} (hz : 1 ≤ z)
    (hY : 0 ≤ Y) {e : ℕ} (he : 1 ≤ e) (hdvd : e ∣ rangePrimorial P₁ h) :
    (3 : ℝ) ^ e.primeFactors.card
        * |BoundingSieve.rem (s := (roughPairSieve Y hP₁ h d hz).toBoundingSieve) e|
      ≤ 2 * 6 ^ e.primeFactors.card := by
  have hsq : Squarefree e := Squarefree.squarefree_of_dvd hdvd (rangePrimorial_squarefree P₁ h)
  have hrem := abs_rem_roughPairSieve_le Y hP₁ h d hz hY (by omega : 0 < e) hsq
  have hroot := rootCount_le_two_pow hsq d
  have h3 : (0 : ℝ) < 3 ^ e.primeFactors.card := by positivity
  calc (3 : ℝ) ^ e.primeFactors.card
        * |BoundingSieve.rem (s := (roughPairSieve Y hP₁ h d hz).toBoundingSieve) e|
      ≤ 3 ^ e.primeFactors.card
        * (2 * ((quadraticCongruenceRootCountTotal e (d : ℤ) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hrem h3.le
    _ ≤ 3 ^ e.primeFactors.card * (2 * 2 ^ e.primeFactors.card) := by
        refine mul_le_mul_of_nonneg_left ?_ h3.le
        linarith [hroot]
    _ = 2 * 6 ^ e.primeFactors.card := by
        rw [show (6 : ℝ) = 3 * 2 by norm_num, mul_pow]
        ring

end

end RHTower.Sieve
