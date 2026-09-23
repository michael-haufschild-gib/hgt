import GaloisForLFunctions.RHTower.XiHeatCassiniWoldLowerHalfShiftConnectionKernel
import GaloisForLFunctions.RHTower.XiHeatCassiniLogMeshDefectPrimeGapEquivalence
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHalfDensityTraceReduction

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Additive prime gap normalized by its left endpoint. -/
def xiHeatCassiniOrderedPrimeRelativeGap (N : ℕ) : ℝ :=
  xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype N : ℝ)

/-- First-order mismatch between the Wold mass atom and normalized prime spacing. -/
def xiHeatCassiniWoldFirstOrderGapFluctuation (N : ℕ) : ℝ :=
  woldCoeff 1 (nthPrimeSubtype (N + 1)) -
    xiHeatCassiniOrderedPrimeRelativeGap N

/-- Universal prime-density discrepancy left after removing Wold's trace-class Euler depletion. -/
def xiHeatCassiniPrimeDensityGapFluctuation (N : ℕ) : ℝ :=
  xiMassPrimeHarmonicRealCoefficient (nthPrimeSubtype (N + 1)) -
    xiHeatCassiniOrderedPrimeRelativeGap N

/-- Second-order error made when normalized additive spacing is replaced by log spacing. -/
def xiHeatCassiniPrimeLogQuadratureError (N : ℕ) : ℝ :=
  xiHeatCassiniOrderedPrimeRelativeGap N -
    xiHeatCassiniOrderedPrimeLogGap N

theorem xiHeatCassiniOrderedPrimeRelativeGap_nonneg (N : ℕ) :
    0 ≤ xiHeatCassiniOrderedPrimeRelativeGap N := by
  unfold xiHeatCassiniOrderedPrimeRelativeGap
  exact div_nonneg (xiHeatCassiniOrderedPrimeGap_nonneg N)
    (nthPrimeSubtype_pos N).le

theorem xiHeatCassiniOrderedPrimeLogGap_eq_log_one_add_relativeGap (N : ℕ) :
    xiHeatCassiniOrderedPrimeLogGap N =
      Real.log (1 + xiHeatCassiniOrderedPrimeRelativeGap N) := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  change Real.log q - Real.log p = Real.log (1 + (q - p) / p)
  calc
    Real.log q - Real.log p = Real.log (q / p) := by
      rw [Real.log_div hq.ne' hp.ne']
    _ = Real.log (1 + (q - p) / p) := by
      congr 1
      field_simp [hp.ne']
      ring

theorem xiHeatCassiniPrimeLogQuadratureError_nonneg (N : ℕ) :
    0 ≤ xiHeatCassiniPrimeLogQuadratureError N := by
  unfold xiHeatCassiniPrimeLogQuadratureError
    xiHeatCassiniOrderedPrimeRelativeGap
  exact sub_nonneg.mpr
    (xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N)

/-- Logarithmic reparametrization costs at most half the normalized gap square. -/
theorem xiHeatCassiniPrimeLogQuadratureError_le_half_sq (N : ℕ) :
    xiHeatCassiniPrimeLogQuadratureError N ≤
      xiHeatCassiniOrderedPrimeRelativeGap N ^ (2 : ℕ) / 2 := by
  let x : ℝ := xiHeatCassiniOrderedPrimeRelativeGap N
  have hx : 0 ≤ x := xiHeatCassiniOrderedPrimeRelativeGap_nonneg N
  have hden : 0 < x + 2 := by linarith
  have hlog : 2 * x / (x + 2) ≤ Real.log (1 + x) :=
    Real.le_log_one_add_of_nonneg hx
  have halgebra : x - x ^ (2 : ℕ) / 2 ≤ 2 * x / (x + 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg x]
  change xiHeatCassiniOrderedPrimeRelativeGap N -
      xiHeatCassiniOrderedPrimeLogGap N ≤
    xiHeatCassiniOrderedPrimeRelativeGap N ^ (2 : ℕ) / 2
  rw [xiHeatCassiniOrderedPrimeLogGap_eq_log_one_add_relativeGap]
  change x - Real.log (1 + x) ≤ x ^ (2 : ℕ) / 2
  linarith

/-- Exact local split: Wold residual variation is first-order spacing fluctuation plus
the nonnegative second-order log-quadrature error. -/
theorem xiHeatCassiniOrderedWoldResidualIncrement_eq_firstOrder_add_quadrature
    (N : ℕ) :
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N =
      xiHeatCassiniWoldFirstOrderGapFluctuation N +
        xiHeatCassiniPrimeLogQuadratureError N := by
  rw [xiHeatCassiniOrderedWoldResidualLogDiscrepancy_succ_sub]
  unfold xiHeatCassiniWoldFirstOrderGapFluctuation
    xiHeatCassiniPrimeLogQuadratureError
    xiHeatCassiniOrderedPrimeLogGap
  ring

/-- Wold's first-order fluctuation is the universal prime-density fluctuation minus the positive
Euler depletion correction. -/
theorem xiHeatCassiniWoldFirstOrderGapFluctuation_eq_density_sub_eulerCorrection
    (N : ℕ) :
    xiHeatCassiniWoldFirstOrderGapFluctuation N =
      xiHeatCassiniPrimeDensityGapFluctuation N -
        xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) := by
  unfold xiHeatCassiniWoldFirstOrderGapFluctuation
    xiHeatCassiniPrimeDensityGapFluctuation
    xiHeatCassiniWoldEulerTraceCorrection
  ring

/-- Exact irreducible split: residual variation is universal prime-density discrepancy, minus a
trace-class Euler correction, plus critical-energy-controlled log quadrature error. -/
theorem xiHeatCassiniOrderedWoldResidualIncrement_eq_density_sub_euler_add_quadrature
    (N : ℕ) :
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N =
      xiHeatCassiniPrimeDensityGapFluctuation N -
          xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) +
        xiHeatCassiniPrimeLogQuadratureError N := by
  rw [xiHeatCassiniOrderedWoldResidualIncrement_eq_firstOrder_add_quadrature,
    xiHeatCassiniWoldFirstOrderGapFluctuation_eq_density_sub_eulerCorrection]

/-- Critical prime-gap energy absorbs the entire second-order quadrature error at
the Route-T half-density wall. -/
theorem two_mul_primeLogQuadratureError_mul_sqrt_le_criticalEnergy (N : ℕ) :
    2 * (xiHeatCassiniPrimeLogQuadratureError N *
        Real.sqrt (nthPrimeSubtype N : ℝ)) ≤
      xiHeatCassiniPrimeGapCriticalEnergy N := by
  have hsqrt : 0 ≤ Real.sqrt (nthPrimeSubtype N : ℝ) := Real.sqrt_nonneg _
  have h := mul_le_mul_of_nonneg_right
    (xiHeatCassiniPrimeLogQuadratureError_le_half_sq N) hsqrt
  unfold xiHeatCassiniOrderedPrimeRelativeGap at h
  unfold xiHeatCassiniPrimeGapCriticalEnergy
  nlinarith

/-- Premise-free finite-prefix domination of all second-order residual error by
critical prime-gap energy. -/
theorem sum_two_mul_primeLogQuadratureError_mul_sqrt_le_criticalEnergy
    (M : ℕ) :
    (∑ N ∈ Finset.range M,
        2 * (xiHeatCassiniPrimeLogQuadratureError N *
          Real.sqrt (nthPrimeSubtype N : ℝ))) ≤
      ∑ N ∈ Finset.range M, xiHeatCassiniPrimeGapCriticalEnergy N := by
  apply Finset.sum_le_sum
  intro N hN
  exact two_mul_primeLogQuadratureError_mul_sqrt_le_criticalEnergy N

/-- The half-density restored Euler correction is unconditionally trace class as a scalar prime
family, before pairing it with any test profile. -/
theorem summable_xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient :
    Summable xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient := by
  have hmajor : Summable (fun p : Nat.Primes =>
      3 * xiMassPrimeSquareEulerWeight (1 / 4) p) :=
    (summable_xiMassPrimeSquareEulerWeight (by norm_num)).mul_left 3
  exact hmajor.of_nonneg_of_le
    xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_nonneg
    xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_le

/-- Reindexing by successor primes and moving the half-density from the successor to the left
endpoint preserves trace-class summability of Euler depletion. -/
theorem summable_xiHeatCassiniWoldEulerTraceCorrection_succ_mul_leftSqrt :
    Summable (fun N : ℕ =>
      xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) *
        Real.sqrt (nthPrimeSubtype N : ℝ)) := by
  have hinj : Function.Injective (fun N : ℕ => nthPrimeSubtype (N + 1)) := by
    intro M N hMN
    have hval : (nthPrimeSubtype (M + 1) : ℕ) =
        (nthPrimeSubtype (N + 1) : ℕ) := congrArg Subtype.val hMN
    have hindex : M + 1 = N + 1 :=
      nthPrimeSubtype_strictMono.injective hval
    omega
  have hsum : Summable (fun N : ℕ =>
      xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient
        (nthPrimeSubtype (N + 1))) :=
    summable_xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient.comp_injective hinj
  apply hsum.of_nonneg_of_le
  · intro N
    exact mul_nonneg
      (xiHeatCassiniWoldEulerTraceCorrection_nonneg (nthPrimeSubtype (N + 1)))
      (Real.sqrt_nonneg _)
  · intro N
    rw [xiHeatCassiniWoldHalfDensityTraceCorrectionCoefficient_eq]
    have hpmono : (nthPrimeSubtype N : ℝ) ≤
        (nthPrimeSubtype (N + 1) : ℝ) := by
      exact_mod_cast nthPrimeSubtype_strictMono.monotone (Nat.le_succ N)
    have hsqrt := Real.sqrt_le_sqrt hpmono
    nlinarith [xiHeatCassiniWoldEulerTraceCorrection_nonneg
      (nthPrimeSubtype (N + 1))]

end

end RHTower
