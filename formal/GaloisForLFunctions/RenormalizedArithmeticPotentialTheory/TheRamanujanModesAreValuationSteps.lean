import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheValuationTowerIsExactlySolvable
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeClockWaveletTensorAndPhaseRecovery
import GaloisForLFunctions.BezoutValuationIncidence.NonMarkovianLagOperatorAlgebraAndPrimePowerRevival

/-!
# Ramanujan coefficients on valuation ladders

The prime-power lag multiplier is exactly the valuation step of the local
matched prime operator. Factors coprime to the modulus leave the lag unchanged.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open BezoutValuationIncidence ArithmeticFunction

/-- Coprime multiplication of the lag fixes the unnormalized Ramanujan coefficient. -/
theorem ramanujanCoefficient_mul_lag_of_coprime {m n t : ℕ} (ht : m.Coprime t) :
    ramanujanLagCoefficient m (n * t) = ramanujanLagCoefficient m n := by
  rw [ramanujanLagCoefficient_eq_totient_mul, ramanujanLagCoefficient_eq_totient_mul,
    TransHorizonIncidenceMechanics.sieveLagMultiplier_mul_lag_of_coprime ht]

/-- At positive lags, the normalized prime-power coefficient is the valuation step. -/
theorem sieveLagMultiplier_prime_pow_eq_valuationStep {p k n : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hn : n ≠ 0) :
    sieveLagMultiplier (p ^ k) n = valuationStep p k (n.factorization p) := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  rw [sieveLagMultiplier_prime_pow_trichotomy p a n hp]
  simp only [hp.pow_dvd_iff_le_factorization hn, valuationStep]
  by_cases hhigh : a + 1 ≤ n.factorization p
  · rw [if_pos hhigh, if_pos hhigh]
  · rw [if_neg hhigh, if_neg hhigh]
    by_cases heq : a ≤ n.factorization p
    · have hv : n.factorization p + 1 = a + 1 := by omega
      rw [if_pos heq, if_pos hv]
      ring
    · have hv : n.factorization p + 1 ≠ a + 1 := by omega
      rw [if_neg heq, if_neg hv]

/-- The unnormalized prime-power mode is its totient times the local eigenstep. -/
theorem ramanujanCoefficient_prime_pow_eq_valuationStep {p k n : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hn : n ≠ 0) :
    ramanujanLagCoefficient (p ^ k) n =
      ((p ^ k).totient : ℝ) * valuationStep p k (n.factorization p) := by
  rw [ramanujanLagCoefficient_eq_totient_mul,
    sieveLagMultiplier_prime_pow_eq_valuationStep hp hk hn]

/-- Splitting off one prime-power conductor separates its valuation step from the
transverse Ramanujan factor. -/
theorem ramanujanCoefficient_prime_power_mul_eq {p k r n : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hpr : p.Coprime r) (hn : n ≠ 0) :
    ramanujanLagCoefficient (p ^ k * r) n =
      ((p ^ k).totient : ℝ) * valuationStep p k (n.factorization p) *
        ramanujanLagCoefficient r n := by
  rw [BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime (hpr.pow_left k),
    ramanujanCoefficient_prime_pow_eq_valuationStep hp hk hn]

/-- A prime-power jump changes at most one of two coprime conductor factors. -/
theorem ramanujanCoefficient_prime_shift_cross {a b : ℕ} (hab : a.Coprime b)
    (n t : ℕ) :
    (ramanujanLagCoefficient a (n * t) - ramanujanLagCoefficient a n) *
      (ramanujanLagCoefficient b (n * t) - ramanujanLagCoefficient b n) * Λ t = 0 := by
  by_cases hΛ : Λ t = 0
  · rw [hΛ, mul_zero]
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  by_cases hpa : p ∣ a
  · have hpb : ¬p ∣ b := by
      intro hpb
      have hd := Nat.dvd_gcd hpa hpb
      rw [hab.gcd_eq_one] at hd
      have hle := Nat.le_of_dvd (by omega : 0 < 1) hd
      exact (not_le_of_gt hp.one_lt) hle
    have hbp : b.Coprime p := (hp.coprime_iff_not_dvd.mpr hpb).symm
    rw [ramanujanCoefficient_mul_lag_of_coprime (hbp.pow_right k), sub_self, mul_zero, zero_mul]
  · have hap : a.Coprime p := (hp.coprime_iff_not_dvd.mpr hpa).symm
    rw [ramanujanCoefficient_mul_lag_of_coprime (hap.pow_right k), sub_self, zero_mul, zero_mul]

/-- The von Mangoldt upward correction obeys an exact product rule across coprime conductors. -/
theorem ramanujanCoefficient_up_difference_mul {a b : ℕ} (hab : a.Coprime b)
    (n t : ℕ) :
    (ramanujanLagCoefficient (a * b) (n * t) - ramanujanLagCoefficient (a * b) n) * Λ t =
      ramanujanLagCoefficient b n *
        ((ramanujanLagCoefficient a (n * t) - ramanujanLagCoefficient a n) * Λ t) +
      ramanujanLagCoefficient a n *
        ((ramanujanLagCoefficient b (n * t) - ramanujanLagCoefficient b n) * Λ t) := by
  rw [BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime hab,
    BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime hab]
  linear_combination ramanujanCoefficient_prime_shift_cross hab n t

/-- The same product rule holds down the divisor row, with coefficients at the original row. -/
theorem ramanujanCoefficient_down_difference_mul {a b n t : ℕ}
    (hab : a.Coprime b) (htn : t ∣ n) :
    (ramanujanLagCoefficient (a * b) (n / t) - ramanujanLagCoefficient (a * b) n) * Λ t =
      ramanujanLagCoefficient b n *
        ((ramanujanLagCoefficient a (n / t) - ramanujanLagCoefficient a n) * Λ t) +
      ramanujanLagCoefficient a n *
        ((ramanujanLagCoefficient b (n / t) - ramanujanLagCoefficient b n) * Λ t) := by
  have h := ramanujanCoefficient_prime_shift_cross hab (n / t) t
  rw [Nat.div_mul_cancel htn] at h
  rw [BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime hab,
    BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime hab]
  linear_combination h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
