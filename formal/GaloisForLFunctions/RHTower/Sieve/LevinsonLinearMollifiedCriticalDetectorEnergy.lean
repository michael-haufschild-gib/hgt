import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorCoefficient

/-!
# Energy of the differentiated critical Barban--Vehov coefficient

The exact coefficient for `(zeta + lambda zeta')` times the linear mollifier is real.  Squaring its
norm gives the literal harmonic energy of the Barban--Vehov coefficient and its first divisor-log
moment, with every normalization retained.
-/

noncomputable section

namespace RHTower.Sieve

open Complex

/-- Exact square energy of one log-differentiated critical mollified coefficient. -/
theorem norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq
    {lam : ℝ} {M k : ℕ} (hM : 1 < M) (hk : 0 < k) :
    ‖levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ) =
      ((1 - lam * Real.log k) * barbanVehovCoeff M k +
          lam * barbanVehovLogMomentCoeff M k) ^ (2 : ℕ) /
        (k : ℝ) / (Real.log M) ^ (2 : ℕ) := by
  rw [levinsonLinearMollifiedCriticalDetectorCoeff_eq hk,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div]
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [abs_of_pos hlog,
    abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / Real.sqrt k)]
  have hsqrt : (Real.sqrt (k : ℝ)) ^ (2 : ℕ) = k := Real.sq_sqrt hkR.le
  have hinvsqrt : ((1 : ℝ) / Real.sqrt k) ^ (2 : ℕ) = 1 / (k : ℝ) := by
    field_simp
    nlinarith
  rw [mul_pow, div_pow, sq_abs, hinvsqrt]
  ring

/-- Exact finite energy of the log-differentiated critical detector in arithmetic form. -/
theorem sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq
    (lam : ℝ) {M N : ℕ} (hM : 1 < M) :
    ∑ k ∈ Finset.Icc 1 N,
        ‖levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ) =
      (∑ k ∈ Finset.Icc 1 N,
          ((1 - lam * Real.log k) * barbanVehovCoeff M k +
            lam * barbanVehovLogMomentCoeff M k) ^ (2 : ℕ) / (k : ℝ)) /
        (Real.log M) ^ (2 : ℕ) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq hM
    (Finset.mem_Icc.mp hk).1]

end RHTower.Sieve
