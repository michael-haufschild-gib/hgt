import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalCoefficient

/-!
# Log-differentiated critical Barban--Vehov coefficient

The critical coefficient of `(zeta + lambda zeta')` times the linear mollifier is evaluated as
the Barban--Vehov coefficient plus its first divisor-log moment.
-/

open Finset Complex

noncomputable section

namespace RHTower.Sieve

/-- First divisor-log moment of the Barban--Vehov weight. -/
def barbanVehovLogMomentCoeff (M k : ℕ) : ℝ :=
  ∑ q ∈ k.divisors, barbanVehovWeight M q * Real.log q

/-- Literal positive-natural coefficient of the unsmoothed critical detector
`zeta + lambda zeta'` multiplied by the linear mollifier. -/
def levinsonLinearMollifiedCriticalDetectorCoeff (lam : ℝ) (M k : ℕ) : ℂ :=
  ∑ q ∈ k.divisors,
    ((((1 : ℝ) / Real.sqrt ((((k / q : ℕ) : ℝ))) : ℝ) *
        (1 - lam * Real.log (((k / q : ℕ) : ℝ))) : ℝ) : ℂ) *
      levinsonLinearMollifierCoeff M q

/-- Logarithm of the complementary divisor. -/
theorem log_natDiv_eq_sub_log_of_dvd {k q : ℕ}
    (hk : 0 < k) (hqk : q ∣ k) :
    Real.log (((k / q : ℕ) : ℝ)) = Real.log k - Real.log q := by
  have hq : 0 < q := Nat.pos_of_dvd_of_pos hqk hk
  have hquot : 0 < k / q := Nat.div_pos (Nat.le_of_dvd hk hqk) hq
  have hmul : q * (k / q) = k := Nat.mul_div_cancel' hqk
  have hlog := Real.log_mul
    (show (q : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hq))
    (show ((k / q : ℕ) : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hquot))
  rw [show (q : ℝ) * ((k / q : ℕ) : ℝ) = (k : ℝ) by
    exact_mod_cast hmul] at hlog
  linarith

/-- Exact Barban--Vehov plus divisor-log-moment formula for the differentiated coefficient. -/
theorem levinsonLinearMollifiedCriticalDetectorCoeff_eq
    {lam : ℝ} {M k : ℕ} (hk : 0 < k) :
    levinsonLinearMollifiedCriticalDetectorCoeff lam M k =
      (((((1 - lam * Real.log k) * barbanVehovCoeff M k +
            lam * barbanVehovLogMomentCoeff M k) / Real.log M : ℝ) *
          ((1 : ℝ) / Real.sqrt k) : ℝ) : ℂ) := by
  rw [levinsonLinearMollifiedCriticalDetectorCoeff, barbanVehovCoeff,
    barbanVehovLogMomentCoeff]
  simp_rw [levinsonLinearMollifierCoeff]
  norm_cast
  calc
    ∑ q ∈ k.divisors,
        (1 / Real.sqrt (((k / q : ℕ) : ℝ)) *
            (1 - lam * Real.log (((k / q : ℕ) : ℝ)))) *
          (barbanVehovWeight M q / Real.log M * (1 / Real.sqrt q)) =
        ∑ q ∈ k.divisors,
          (((1 - lam * Real.log k) * barbanVehovWeight M q +
              lam * (barbanVehovWeight M q * Real.log q)) / Real.log M) *
            (1 / Real.sqrt k) := by
      apply Finset.sum_congr rfl
      intro q hqmem
      have hqk : q ∣ k := Nat.dvd_of_mem_divisors hqmem
      rw [log_natDiv_eq_sub_log_of_dvd hk hqk]
      calc
        1 / Real.sqrt (((k / q : ℕ) : ℝ)) *
              (1 - lam * (Real.log k - Real.log q)) *
            (barbanVehovWeight M q / Real.log M * (1 / Real.sqrt q)) =
            (((1 - lam * Real.log k) * barbanVehovWeight M q +
                lam * (barbanVehovWeight M q * Real.log q)) / Real.log M) *
              ((1 / Real.sqrt (((k / q : ℕ) : ℝ))) *
                (1 / Real.sqrt q)) := by ring
        _ = (((1 - lam * Real.log k) * barbanVehovWeight M q +
                lam * (barbanVehovWeight M q * Real.log q)) / Real.log M) *
              (1 / Real.sqrt k) := by
          rw [one_div_sqrt_div_mul_one_div_sqrt_of_dvd hk hqk]
    _ = (((1 - lam * Real.log k) *
            (∑ q ∈ k.divisors, barbanVehovWeight M q) +
          lam * (∑ q ∈ k.divisors,
            barbanVehovWeight M q * Real.log q)) / Real.log M) *
          (1 / Real.sqrt k) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.sum_div, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]

/-- The value-only specialization recovers the critical Barban--Vehov coefficient. -/
@[simp] theorem levinsonLinearMollifiedCriticalDetectorCoeff_zero
    (M k : ℕ) :
    levinsonLinearMollifiedCriticalDetectorCoeff 0 M k =
      levinsonLinearMollifiedCriticalCoeff M k := by
  rw [levinsonLinearMollifiedCriticalDetectorCoeff,
    levinsonLinearMollifiedCriticalCoeff]
  apply Finset.sum_congr rfl
  intro q hq
  simp

end RHTower.Sieve
