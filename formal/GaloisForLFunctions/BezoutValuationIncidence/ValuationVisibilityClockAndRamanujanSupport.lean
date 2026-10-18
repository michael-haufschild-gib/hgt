import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient

/-!
# The exact valuation clock of a translated arithmetic mode

Mode `q` survives compression of translation by `h` exactly when
`q / rad(q)` divides `h`. Its prime exponents are `v_p(q)-1`, with natural
subtraction. This distinguishes eventual recovery from the squarefree
information retained by one-step prediction.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- The positive recovery clock of each positive mode; zero at mode zero. -/
def lagVisibilityClock (q : ℕ) : ℕ := q / ∏ p ∈ q.primeFactors, p

private theorem prime_radical_factorization (q p : ℕ) :
    (∏ r ∈ q.primeFactors, r).factorization p = if p ∈ q.primeFactors then 1 else 0 := by
  rw [Nat.factorization_prod_apply (fun r hr => (Nat.mem_primeFactors.mp hr).1.ne_zero)]
  calc
    _ = ∑ r ∈ q.primeFactors, if r = p then 1 else 0 := by
      apply sum_congr rfl
      intro r hr
      simp [(Nat.mem_primeFactors.mp hr).1.factorization, Finsupp.single_apply]
    _ = _ := by simp

/-- Each prime valuation of the visibility clock is the original valuation minus one. -/
theorem lagVisibilityClock_factorization (q p : ℕ) :
    (lagVisibilityClock q).factorization p = q.factorization p - 1 := by
  rw [lagVisibilityClock, Nat.factorization_div (Nat.prod_primeFactors_dvd q),
    Finsupp.tsub_apply, prime_radical_factorization]
  by_cases hp : p ∈ q.primeFactors
  · rw [if_pos hp]
  · have hz : q.factorization p = 0 := by
      simpa only [Nat.factorization_eq_zero_iff, Nat.mem_primeFactors,
        not_and_or, not_ne_iff] using hp
    simp [hp, hz]

/-- A visibility clock vanishes only at the excluded zero mode. -/
theorem lagVisibilityClock_eq_zero_iff (q : ℕ) : lagVisibilityClock q = 0 ↔ q = 0 := by
  constructor
  · intro hz
    by_contra hq
    have hrad : 0 < ∏ p ∈ q.primeFactors, p :=
      prod_pos fun p hp => (Nat.mem_primeFactors.mp hp).1.pos
    have hc : 0 < lagVisibilityClock q :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)) hrad
    omega
  · rintro rfl
    simp [lagVisibilityClock]

/-- Squarefreeness of the exact quotient is the divisibility law of the visibility clock. -/
theorem squarefree_lag_quotient_iff (q h : ℕ) :
    Squarefree (q / Nat.gcd q h) ↔ q ≠ 0 ∧ lagVisibilityClock q ∣ h := by
  by_cases hq : q = 0
  · simp [hq]
  rw [and_iff_right hq]
  by_cases hh : h = 0
  · simp [hh, Nat.div_self (Nat.pos_of_ne_zero hq)]
  have hg : 0 < Nat.gcd q h := Nat.gcd_pos_of_pos_left h (Nat.pos_of_ne_zero hq)
  have ht : q / Nat.gcd q h ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.gcd_dvd_left q h)) hg).ne'
  have hD : lagVisibilityClock q ≠ 0 := fun hz => hq ((lagVisibilityClock_eq_zero_iff q).mp hz)
  rw [Nat.squarefree_iff_factorization_le_one ht, ← Nat.factorization_le_iff_dvd hD hh]
  change (∀ p, (q / Nat.gcd q h).factorization p ≤ 1) ↔
    ∀ p, (lagVisibilityClock q).factorization p ≤ h.factorization p
  simp only [Nat.factorization_div (Nat.gcd_dvd_left q h), Nat.factorization_gcd hq hh,
    Finsupp.tsub_apply, Finsupp.inf_apply, lagVisibilityClock_factorization]
  constructor <;> intro h p <;> have := h p <;> omega

/-- Exact arithmetic visibility of every mode at every natural lag. -/
theorem sieveLagMultiplier_ne_zero_iff (q h : ℕ) :
    sieveLagMultiplier q h ≠ 0 ↔ q ≠ 0 ∧ lagVisibilityClock q ∣ h := by
  rw [sieveLagMultiplier_eq_moebius_totient_quotient]
  by_cases hq : q = 0
  · simp [hq, moebiusReal]
  have hg : 0 < Nat.gcd q h := Nat.gcd_pos_of_pos_left h (Nat.pos_of_ne_zero hq)
  have ht : 0 < q / Nat.gcd q h :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.gcd_dvd_left q h)) hg
  have hφ : ((q / Nat.gcd q h).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr ht).ne'
  rw [div_ne_zero_iff, and_iff_left hφ]
  have hmu : moebiusReal (q / Nat.gcd q h) ≠ 0 ↔ Squarefree (q / Nat.gcd q h) := by
    simpa only [moebiusReal, ne_eq, Int.cast_eq_zero] using
      (moebius_ne_zero_iff_squarefree (n := q / Nat.gcd q h))
  exact hmu.trans (squarefree_lag_quotient_iff q h)

/-- The unnormalized observation coefficient has exactly the same visibility schedule. -/
theorem ramanujanLagCoefficient_ne_zero_iff (q h : ℕ) :
    ramanujanLagCoefficient q h ≠ 0 ↔ q ≠ 0 ∧ lagVisibilityClock q ∣ h := by
  constructor
  · intro hR
    apply (sieveLagMultiplier_ne_zero_iff q h).mp
    intro hz
    exact hR (by rw [ramanujanLagCoefficient_eq_totient_mul, hz, mul_zero])
  · intro hv
    have hφ : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hv.1)).ne'
    rw [ramanujanLagCoefficient_eq_totient_mul]
    exact mul_ne_zero hφ ((sieveLagMultiplier_ne_zero_iff q h).mpr hv)

/-- A positive mode first becomes visible at precisely its own visibility clock. -/
theorem sieveLagMultiplier_first_positive_lag (q T : ℕ) :
    (∃ h ∈ Icc 1 T, sieveLagMultiplier q h ≠ 0) ↔
      q ≠ 0 ∧ lagVisibilityClock q ≤ T := by
  constructor
  · rintro ⟨h, hh, hv⟩
    obtain ⟨hq, hD⟩ := (sieveLagMultiplier_ne_zero_iff q h).mp hv
    exact ⟨hq, (Nat.le_of_dvd (mem_Icc.mp hh).1 hD).trans (mem_Icc.mp hh).2⟩
  · rintro ⟨hq, hT⟩
    have hD : 0 < lagVisibilityClock q := Nat.pos_of_ne_zero
      (fun hz => hq ((lagVisibilityClock_eq_zero_iff q).mp hz))
    exact ⟨lagVisibilityClock q, mem_Icc.mpr ⟨hD, hT⟩,
      (sieveLagMultiplier_ne_zero_iff q _).mpr ⟨hq, dvd_rfl⟩⟩

/-- The first positive visible lag of a prime-power mode `p^(a+1)` is `p^a`. -/
theorem lagVisibilityClock_prime_power (p a : ℕ) (hp : p.Prime) :
    lagVisibilityClock (p ^ (a + 1)) = p ^ a := by
  rw [lagVisibilityClock, Nat.primeFactors_pow p (by omega : a + 1 ≠ 0),
    hp.primeFactors, prod_singleton, pow_succ]
  exact Nat.mul_div_cancel _ hp.pos

end
end GaloisForLFunctions.BezoutValuationIncidence
