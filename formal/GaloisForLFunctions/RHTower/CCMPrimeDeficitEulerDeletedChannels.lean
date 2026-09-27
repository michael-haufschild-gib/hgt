import GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerForceOrthogonality

/-!
# Exact prime-power channels of the deleted Euler force

A nonzero deleted force has exactly one prime dividing the Euler modulus.
Along that prime's tower, its coefficient is the rough renewal coefficient
at the coprime base, multiplied by the logarithm of the prime. The result
separates arithmetic coefficients; delayed time profiles can still interact.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem ccmEulerDeletedPrime_ne_zero_iff (P n : ℕ) :
    ccmEulerDeletedPrime P n ≠ 0 ↔ IsPrimePow n ∧ ¬n.Coprime P := by
  rw [ccmEulerDeletedPrime_apply]
  by_cases hn : n.Coprime P
  · simp [hn]
  · simp [hn, ArithmeticFunction.vonMangoldt_ne_zero_iff]

private theorem deleted_prime_power {P b : ℕ} (hb : ccmEulerDeletedPrime P b ≠ 0) :
    ∃ p k : ℕ, p.Prime ∧ p ∣ P ∧ 0 < k ∧ p ^ k = b := by
  obtain ⟨hpow, hcop⟩ := (ccmEulerDeletedPrime_ne_zero_iff P b).mp hb
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff b).mp hpow
  refine ⟨p, k, hp, ?_, hk, rfl⟩
  by_contra hdiv
  exact hcop ((hp.coprime_iff_not_dvd.mpr hdiv).pow_left k)

private theorem deleted_channel_unique {P p k n a b : ℕ}
    (hp : p.Prime) (hpP : p ∣ P) (hn : n.Coprime P) (hn0 : n ≠ 0)
    (ha : a.Coprime P) (hb : ccmEulerDeletedPrime P b ≠ 0)
    (hab : a * b = p ^ k * n) : a = n ∧ b = p ^ k := by
  obtain ⟨q, j, hq, hqP, hj, rfl⟩ := deleted_prime_power hb
  have hqd : q ∣ p ^ k * n := hab ▸ dvd_mul_of_dvd_right (dvd_pow_self q hj.ne') a
  have hqp : q = p := by
    rcases hq.dvd_mul.mp hqd with hqk | hqn
    · exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqk)
    · exact False.elim (hq.ne_one (Nat.eq_one_of_dvd_coprimes hn hqn hqP))
  subst q
  have han : a ∣ n := ((ha.coprime_dvd_right hpP).pow_right k).dvd_mul_left.mp
    (hab ▸ dvd_mul_right a (p ^ j))
  have hna : n ∣ a := ((hn.coprime_dvd_right hpP).pow_right j).dvd_mul_right.mp
    (hab ▸ dvd_mul_left n (p ^ k))
  have heq : a = n := Nat.dvd_antisymm han hna
  refine ⟨heq, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0)
  simpa only [heq, mul_comm] using hab

/-- Every deleted prime tower is an exact scalar copy of the coprime base. -/
theorem ccmEulerRenewal_deletedForce_prime_pow_mul {P p n k : ℕ}
    (hp : p.Prime) (hpP : p ∣ P) (hn : n.Coprime P) (hk : 0 < k) :
    (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) (p ^ k * n) =
      Real.log p * ccmEulerRenewalKernel P n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hpk : ¬(p ^ k).Coprime P := by
    intro h
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes h (dvd_pow_self p hk.ne') hpP)
  rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_eq_single (n, p ^ k)]
  · rw [ccmEulerDeletedPrime_apply, if_neg hpk,
      ArithmeticFunction.vonMangoldt_apply_pow hk.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact mul_comm _ _
  · intro ab hab hne
    by_cases ha : ab.1.Coprime P
    · by_cases hb : ccmEulerDeletedPrime P ab.2 = 0
      · rw [hb, mul_zero]
      · obtain ⟨haeq, hbeq⟩ := deleted_channel_unique hp hpP hn hn0 ha hb
          (Nat.mem_divisorsAntidiagonal.mp hab).1
        exact False.elim (hne (Prod.ext haeq hbeq))
    · rw [ccmEulerRenewalKernel_of_not_coprime ha, zero_mul]
  · intro hnot
    exact False.elim (hnot (Nat.mem_divisorsAntidiagonal.mpr
      ⟨mul_comm _ _, mul_ne_zero (pow_ne_zero _ hp.ne_zero) hn0⟩))

/-- Two distinct deleted primes cannot occur in a nonzero force coefficient. -/
theorem ccmEulerRenewal_deletedForce_eq_zero_of_two_primes {P p q N : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpP : p ∣ P) (hqP : q ∣ P)
    (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p ≠ q) :
    (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) N = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases ha : ab.1.Coprime P
  · by_cases hb : ccmEulerDeletedPrime P ab.2 = 0
    · rw [hb, mul_zero]
    · obtain ⟨r, j, hr, _hrP, hj, hrj⟩ := deleted_prime_power hb
      have hdiv : ∀ s : ℕ, s.Prime → s ∣ P → s ∣ N → s = r := by
        intro s hs hsP hsN
        have hsab : s ∣ ab.1 * ab.2 := (Nat.mem_divisorsAntidiagonal.mp hab).1 ▸ hsN
        rcases hs.dvd_mul.mp hsab with hsa | hsb
        · exact False.elim (hs.ne_one (Nat.eq_one_of_dvd_coprimes ha hsa hsP))
        · rw [← hrj] at hsb
          exact (Nat.prime_dvd_prime_iff_eq hs hr).mp (hs.dvd_of_dvd_pow hsb)
      exact False.elim (hpq ((hdiv p hp hpP hpN).trans (hdiv q hq hqP hqN).symm))
  · rw [ccmEulerRenewalKernel_of_not_coprime ha, zero_mul]

/-- At most one divisor pair contributes to any deleted-force coefficient. -/
theorem ccmEulerRenewal_deletedForce_term_unique (P N : ℕ)
    {ab cd : ℕ × ℕ} (hab : ab ∈ N.divisorsAntidiagonal)
    (hcd : cd ∈ N.divisorsAntidiagonal)
    (hab0 : ccmEulerRenewalKernel P ab.1 * ccmEulerDeletedPrime P ab.2 ≠ 0)
    (hcd0 : ccmEulerRenewalKernel P cd.1 * ccmEulerDeletedPrime P cd.2 ≠ 0) :
    ab = cd := by
  have ha : ab.1.Coprime P := by
    by_contra h
    exact hab0 (by rw [ccmEulerRenewalKernel_of_not_coprime h, zero_mul])
  have hc : cd.1.Coprime P := by
    by_contra h
    exact hcd0 (by rw [ccmEulerRenewalKernel_of_not_coprime h, zero_mul])
  obtain ⟨p, k, hp, hpP, _hk, hpk⟩ := deleted_prime_power (right_ne_zero_of_mul hab0)
  have ha0 : ab.1 ≠ 0 :=
    (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hab)).ne'
  have hprod : cd.1 * cd.2 = p ^ k * ab.1 := by
    rw [hpk, mul_comm ab.2 ab.1, (Nat.mem_divisorsAntidiagonal.mp hab).1]
    exact (Nat.mem_divisorsAntidiagonal.mp hcd).1
  obtain ⟨hca, hdb⟩ := deleted_channel_unique hp hpP ha ha0 hc
    (right_ne_zero_of_mul hcd0) hprod
  exact (Prod.ext hca (hdb.trans hpk)).symm

/-- Squaring the deleted convolution creates no arithmetic cross terms. -/
theorem ccmEulerRenewal_deletedForce_sq (P N : ℕ) :
    (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) N ^ 2 =
      ∑ ab ∈ N.divisorsAntidiagonal,
        ccmEulerRenewalKernel P ab.1 ^ 2 * ccmEulerDeletedPrime P ab.2 ^ 2 := by
  rw [ArithmeticFunction.mul_apply, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [Finset.sum_eq_single ab]
  · ring
  · intro cd hcd hne
    by_cases hab0 : ccmEulerRenewalKernel P ab.1 * ccmEulerDeletedPrime P ab.2 = 0
    · rw [hab0, zero_mul]
    by_cases hcd0 : ccmEulerRenewalKernel P cd.1 * ccmEulerDeletedPrime P cd.2 = 0
    · rw [hcd0, mul_zero]
    exact False.elim (hne (ccmEulerRenewal_deletedForce_term_unique P N hcd hab hcd0 hab0))
  · exact fun h => False.elim (h hab)

/-- Pointwise squaring commutes with this particular Dirichlet convolution. -/
theorem ccmEulerRenewal_deletedForce_pmul (P : ℕ) :
    ArithmeticFunction.pmul (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P)
        (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P) =
      ArithmeticFunction.pmul (ccmEulerRenewalKernel P) (ccmEulerRenewalKernel P) *
        ArithmeticFunction.pmul (ccmEulerDeletedPrime P) (ccmEulerDeletedPrime P) := by
  ext N
  simpa only [ArithmeticFunction.pmul_apply, ArithmeticFunction.mul_apply, pow_two] using
    ccmEulerRenewal_deletedForce_sq P N

end RHTower
