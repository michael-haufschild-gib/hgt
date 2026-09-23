import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifier
import GaloisForLFunctions.RHTower.Sieve.HarmonicWeightedGrahamMeanSquare

/-!
# Critical zeta head times the linear Levinson mollifier

The literal product coefficient collapses to the Barban--Vehov divisor coefficient divided by
`log M * sqrt k`.  The harmonic Graham theorem therefore supplies its finite coefficient energy.
-/

open Finset Complex

noncomputable section

namespace RHTower.Sieve

/-- The reciprocal square-root factors on complementary divisors multiply to `k⁻¹⁄²`. -/
theorem one_div_sqrt_div_mul_one_div_sqrt_of_dvd {k d : ℕ}
    (hk : 0 < k) (hdvd : d ∣ k) :
    ((1 : ℝ) / Real.sqrt (((k / d : ℕ) : ℝ))) *
        ((1 : ℝ) / Real.sqrt d) =
      (1 : ℝ) / Real.sqrt k := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hk
  have hq : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hk hdvd) hd
  have hsqrt : Real.sqrt (((k / d : ℕ) : ℝ)) * Real.sqrt d = Real.sqrt k := by
    rw [mul_comm, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ d)]
    congr 1
    norm_cast
    exact Nat.mul_div_cancel' hdvd
  have hsd : Real.sqrt (d : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hd))
  have hsq : Real.sqrt ((k / d : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hq))
  have hsk : Real.sqrt (k : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hk))
  field_simp
  nlinarith

/-- Positive-natural coefficient of the critical zeta Dirichlet head multiplied by the
linear Levinson mollifier. -/
def levinsonLinearMollifiedCriticalCoeff (M k : ℕ) : ℂ :=
  ∑ d ∈ k.divisors,
    (((1 : ℝ) / Real.sqrt (((k / d : ℕ) : ℝ)) : ℝ) : ℂ) *
      levinsonLinearMollifierCoeff M d

/-- The product coefficient is the normalized Barban--Vehov divisor coefficient. -/
theorem levinsonLinearMollifiedCriticalCoeff_eq_barbanVehov
    {M k : ℕ} (hk : 0 < k) :
    levinsonLinearMollifiedCriticalCoeff M k =
      (((barbanVehovCoeff M k / Real.log M : ℝ) *
          ((1 : ℝ) / Real.sqrt k) : ℝ) : ℂ) := by
  rw [levinsonLinearMollifiedCriticalCoeff, barbanVehovCoeff]
  simp_rw [levinsonLinearMollifierCoeff]
  norm_cast
  calc
    ∑ d ∈ k.divisors,
        1 / Real.sqrt (((k / d : ℕ) : ℝ)) *
          (barbanVehovWeight M d / Real.log M * (1 / Real.sqrt d)) =
        ∑ d ∈ k.divisors,
          (barbanVehovWeight M d / Real.log M) * (1 / Real.sqrt k) := by
      apply Finset.sum_congr rfl
      intro d hdmem
      have hdvd : d ∣ k := Nat.dvd_of_mem_divisors hdmem
      calc
        1 / Real.sqrt (((k / d : ℕ) : ℝ)) *
            (barbanVehovWeight M d / Real.log M * (1 / Real.sqrt d)) =
            (barbanVehovWeight M d / Real.log M) *
              ((1 / Real.sqrt (((k / d : ℕ) : ℝ))) * (1 / Real.sqrt d)) := by ring
        _ = (barbanVehovWeight M d / Real.log M) * (1 / Real.sqrt k) := by
          rw [one_div_sqrt_div_mul_one_div_sqrt_of_dvd hk hdvd]
    _ = (∑ m ∈ k.divisors, barbanVehovWeight M m) / Real.log M *
          (1 / Real.sqrt k) := by
      rw [← Finset.sum_mul, Finset.sum_div]

/-- Exact square energy of one critical mollified product coefficient. -/
theorem norm_levinsonLinearMollifiedCriticalCoeff_sq
    {M k : ℕ} (hM : 1 < M) (hk : 0 < k) :
    ‖levinsonLinearMollifiedCriticalCoeff M k‖ ^ (2 : ℕ) =
      (barbanVehovCoeff M k) ^ (2 : ℕ) / (k : ℝ) / (Real.log M) ^ (2 : ℕ) := by
  rw [levinsonLinearMollifiedCriticalCoeff_eq_barbanVehov hk,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div]
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [abs_of_pos hlog, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / Real.sqrt k)]
  have hsqrt : (Real.sqrt (k : ℝ)) ^ (2 : ℕ) = k := Real.sq_sqrt hkR.le
  have hinvsqrt : ((1 : ℝ) / Real.sqrt k) ^ (2 : ℕ) = 1 / (k : ℝ) := by
    field_simp
    nlinarith
  rw [mul_pow, div_pow, sq_abs, hinvsqrt]
  ring

/-- Exact finite coefficient energy in harmonic Barban--Vehov form. -/
theorem sum_norm_levinsonLinearMollifiedCriticalCoeff_sq
    {M N : ℕ} (hM : 1 < M) :
    ∑ k ∈ Finset.Icc 1 N, ‖levinsonLinearMollifiedCriticalCoeff M k‖ ^ (2 : ℕ) =
      (∑ k ∈ Finset.Icc 1 N, (barbanVehovCoeff M k) ^ (2 : ℕ) / (k : ℝ)) /
        (Real.log M) ^ (2 : ℕ) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_levinsonLinearMollifiedCriticalCoeff_sq hM (Finset.mem_Icc.mp hk).1]

/-- Explicit harmonic-Graham upper bound for the literal critical zeta head times the
linear Levinson mollifier. -/
theorem sum_norm_levinsonLinearMollifiedCriticalCoeff_sq_le
    {M N : ℕ} (hM : 1 < M) (hMN : M ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, ‖levinsonLinearMollifiedCriticalCoeff M k‖ ^ (2 : ℕ) ≤
      ((1 + Real.log N) *
          (4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log M)) +
        (1 + 2 * Real.log M) * ((M : ℝ) * Real.log M) ^ (2 : ℕ)) /
          (Real.log M) ^ (2 : ℕ) := by
  rw [sum_norm_levinsonLinearMollifiedCriticalCoeff_sq hM]
  exact div_le_div_of_nonneg_right
    (sum_harmonic_sq_barbanVehovCoeff_le (Nat.le_of_lt hM) hMN) (sq_nonneg _)

end RHTower.Sieve
