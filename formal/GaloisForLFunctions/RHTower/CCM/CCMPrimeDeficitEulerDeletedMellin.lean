import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerFactorialEnergy

/-!
# Transfer of deleted-force energy to critical Mellin profiles

The arithmetic energy budget bounds the actual finite Dirichlet polynomial
on the critical line, averaged over frequency. The estimate records the
carrier-length cost explicitly. It does not supply pointwise control of
the signed Chebyshev remainder or discard its exponential source term.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace RHTower

def ccmEulerDeletedCriticalSeq (P N n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 1 N then
    ((ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n : ℂ) *
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
  else 0

private theorem criticalSeq_support {P N n : ℕ} (h : ccmEulerDeletedCriticalSeq P N n ≠ 0) :
    n ∈ Finset.Icc 1 N := by
  by_contra hn
  simp [ccmEulerDeletedCriticalSeq, hn] at h

private theorem criticalSeq_norm_sq (P N n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
    ‖ccmEulerDeletedCriticalSeq P N n‖ ^ 2 =
      (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [ccmEulerDeletedCriticalSeq, if_pos hn, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hpow : ‖(((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = 1 / (n : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg _ _),
      ← Real.rpow_natCast, ← Real.rpow_mul hnR.le,
      show (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    exact inv_eq_one_div _
    all_goals positivity
  rw [hpow]
  ring

def ccmEulerDeletedCriticalPolynomial (P N : ℕ) (t : ℝ) : ℂ :=
  LSeries (ccmEulerDeletedCriticalSeq P N) ((t : ℂ) * Complex.I)

/-- The profile uses the actual deleted force at `1/2 + it`. -/
theorem ccmEulerDeletedCriticalPolynomial_eq_sum (P N : ℕ) (t : ℝ) :
    ccmEulerDeletedCriticalPolynomial P N t =
      ∑ n ∈ Finset.Icc 1 N,
        ((ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n : ℂ) *
          (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [ccmEulerDeletedCriticalPolynomial,
    Sieve.LSeries_eq_sum_term_of_support (fun n h => criticalSeq_support h)]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := (show 0 < n from (Finset.mem_Icc.mp hn).1).ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [LSeries.term_def, if_neg hn0, ccmEulerDeletedCriticalSeq, if_pos hn]
  have hpoint : -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      (((-(1 : ℝ) / 2 : ℝ) : ℂ)) + (-((t : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [hpoint, Complex.cpow_add _ _ hnC]
  have hamp : (n : ℂ) ^ (((-(1 : ℝ) / 2 : ℝ) : ℂ)) =
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow hnR.le (-(1 : ℝ) / 2)).symm
  rw [hamp, Complex.cpow_neg]
  ring

/-- The carrier length and frequency interval have separate, explicit costs. -/
theorem integral_ccmEulerDeletedCriticalPolynomial_le_energy (P N : ℕ)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖ccmEulerDeletedCriticalPolynomial P N t‖ ^ 2) ≤
      (5 * Real.pi * Real.exp 1 * N + (5 * Real.pi / 2) * T) *
        ∑ n ∈ Finset.Icc 1 N,
          (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n ^ 2 / n := by
  let E := ∑ n ∈ Finset.Icc 1 N,
    (ccmEulerRenewalKernel P * ccmEulerDeletedPrime P : ArithmeticFunction ℝ) n ^ 2 / n
  have hplain : (∑ n ∈ Finset.Icc 1 N, ‖ccmEulerDeletedCriticalSeq P N n‖ ^ 2) = E :=
    Finset.sum_congr rfl fun n hn => criticalSeq_norm_sq P N n hn
  have hweighted : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖ccmEulerDeletedCriticalSeq P N n‖ ^ 2) ≤
      (N : ℝ) * E := by
    rw [← hplain, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (sq_nonneg _)
  have hbase := Sieve.integral_Icc_normSq_LSeries_le_general_affine
    (a := ccmEulerDeletedCriticalSeq P N) (s := Finset.Icc 1 N)
    (by simp) (fun _n hn => criticalSeq_support hn) 0 hT
  simp only [Sieve.generalMeanSquareConst, Sieve.generalMeanSquareRate, neg_zero,
    Real.rpow_zero, Complex.ofReal_one, mul_one, Complex.ofReal_zero, zero_add] at hbase
  rw [hplain] at hbase
  have hconst := mul_le_mul_of_nonneg_left hweighted
    (show 0 ≤ 5 * Real.pi * Real.exp 1 by positivity)
  change (∫ t in Set.Icc (-T) T, ‖ccmEulerDeletedCriticalPolynomial P N t‖ ^ 2) ≤
    (5 * Real.pi * Real.exp 1 * N + (5 * Real.pi / 2) * T) * E
  dsimp only [ccmEulerDeletedCriticalPolynomial]
  linarith only [hbase, hconst]

/-- Critical Mellin mean square with the finite deleted-prime budget. -/
theorem integral_ccmEulerDeletedCriticalPolynomial_le (P N : ℕ)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖ccmEulerDeletedCriticalPolynomial (P + 1) N t‖ ^ 2) ≤
      (5 * Real.pi * Real.exp 1 * N + (5 * Real.pi / 2) * T) *
        (ccmEulerDeletedEnergyBudget (P + 1) * (1 + Real.log N) ^ 4) := by
  exact (integral_ccmEulerDeletedCriticalPolynomial_le_energy (P + 1) N hT).trans
    (mul_le_mul_of_nonneg_left (ccmEulerRenewal_deletedForce_critical_energy_le P N)
      (by positivity))

/-- At frequency height at least the carrier length, energy per unit height is logarithmic. -/
theorem integral_ccmEulerDeletedCriticalPolynomial_le_of_length_le (P N : ℕ)
    {T : ℝ} (hT : 1 ≤ T) (hNT : (N : ℝ) ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖ccmEulerDeletedCriticalPolynomial (P + 1) N t‖ ^ 2) ≤
      (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2) * T *
        (ccmEulerDeletedEnergyBudget (P + 1) * (1 + Real.log N) ^ 4) := by
  apply (integral_ccmEulerDeletedCriticalPolynomial_le P N hT).trans
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (ccmEulerDeletedEnergyBudget_nonneg _) (by positivity))
  nlinarith only [mul_le_mul_of_nonneg_left hNT
    (show 0 ≤ 5 * Real.pi * Real.exp 1 by positivity)]

end RHTower
