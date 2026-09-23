import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualFirstOrderGapFluctuation
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Chebyshev prime-number-theorem error sampled at the `N`th ordered prime. -/
def xiHeatCassiniOrderedChebyshevError (N : ℕ) : ℝ :=
  Chebyshev.theta (nthPrimeSubtype N : ℝ) - (nthPrimeSubtype N : ℝ)

/-- Consecutive Chebyshev-error jump normalized at its right prime endpoint. -/
def xiHeatCassiniNormalizedChebyshevErrorIncrement (N : ℕ) : ℝ :=
  (xiHeatCassiniOrderedChebyshevError (N + 1) -
      xiHeatCassiniOrderedChebyshevError N) /
    (nthPrimeSubtype (N + 1) : ℝ)

/-- Positive backward logarithmic-cell depletion between normalized additive and log spacing. -/
def xiHeatCassiniPrimeBackwardLogDepletion (N : ℕ) : ℝ :=
  xiHeatCassiniOrderedPrimeLogGap N -
    xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype (N + 1) : ℝ)

/-- No prime other than the right endpoint lies in one consecutive ordered-prime shell. -/
theorem filter_prime_Ioc_consecutive_nthPrime (N : ℕ) :
    (Finset.Ioc (nthPrimeSubtype N : ℕ) (nthPrimeSubtype (N + 1) : ℕ)).filter
        Nat.Prime =
      {(nthPrimeSubtype (N + 1) : ℕ)} := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hpr, hrq⟩, hrprime⟩
    let m : ℕ := nthPrimeEquiv.symm ⟨r, hrprime⟩
    have hmval : (nthPrimeSubtype m : ℕ) = r := by
      change ((nthPrimeEquiv m : Nat.Primes) : ℕ) = r
      rw [show nthPrimeEquiv m = (⟨r, hrprime⟩ : Nat.Primes) by simp [m]]
    have hNm : N < m := by
      by_contra hnot
      have hmN : m ≤ N := Nat.le_of_not_gt hnot
      have hmono := nthPrimeSubtype_strictMono.monotone hmN
      change (nthPrimeSubtype m : ℕ) ≤ (nthPrimeSubtype N : ℕ) at hmono
      rw [hmval] at hmono
      omega
    have hmN1 : m ≤ N + 1 := by
      by_contra hnot
      have hN1m : N + 1 < m := Nat.lt_of_not_ge hnot
      have hmono := nthPrimeSubtype_strictMono hN1m
      change (nthPrimeSubtype (N + 1) : ℕ) < (nthPrimeSubtype m : ℕ) at hmono
      rw [hmval] at hmono
      omega
    have : m = N + 1 := by omega
    rw [← hmval, this]
  · intro hr
    subst r
    exact ⟨
      ⟨nthPrimeSubtype_strictMono (Nat.lt_succ_self N), le_rfl⟩,
      (nthPrimeSubtype (N + 1)).2⟩

/-- Chebyshev's theta function jumps by exactly the right-endpoint log across consecutive primes. -/
theorem chebyshevTheta_nthPrime_succ_sub (N : ℕ) :
    Chebyshev.theta (nthPrimeSubtype (N + 1) : ℝ) -
        Chebyshev.theta (nthPrimeSubtype N : ℝ) =
      Real.log (nthPrimeSubtype (N + 1) : ℝ) := by
  have hfloor : ⌊(nthPrimeSubtype N : ℝ)⌋₊ ≤
      ⌊(nthPrimeSubtype (N + 1) : ℝ)⌋₊ := by
    norm_num
    exact nthPrimeSubtype_strictMono.monotone (Nat.le_succ N)
  rw [chebyshevTheta_sub_eq_shellSum hfloor]
  norm_num
  rw [filter_prime_Ioc_consecutive_nthPrime]
  simp

/-- Universal density discrepancy is one normalized PNT-error jump minus the exact quadratic
endpoint-transport cost. -/
theorem xiHeatCassiniPrimeDensityGapFluctuation_eq_chebyshevIncrement_sub_gapSq
    (N : ℕ) :
    xiHeatCassiniPrimeDensityGapFluctuation N =
      xiHeatCassiniNormalizedChebyshevErrorIncrement N -
        xiHeatCassiniOrderedPrimeGap N ^ (2 : ℕ) /
          ((nthPrimeSubtype N : ℝ) * (nthPrimeSubtype (N + 1) : ℝ)) := by
  have hp : (nthPrimeSubtype N : ℝ) ≠ 0 := (nthPrimeSubtype_pos N).ne'
  have hq : (nthPrimeSubtype (N + 1) : ℝ) ≠ 0 :=
    (nthPrimeSubtype_pos (N + 1)).ne'
  have htheta := chebyshevTheta_nthPrime_succ_sub N
  have hthetaEq :
      Chebyshev.theta (nthPrimeSubtype (N + 1) : ℝ) =
        Chebyshev.theta (nthPrimeSubtype N : ℝ) +
          Real.log (nthPrimeSubtype (N + 1) : ℝ) := by
    linarith
  rw [xiHeatCassiniPrimeDensityGapFluctuation,
    xiHeatCassiniNormalizedChebyshevErrorIncrement,
    xiHeatCassiniOrderedChebyshevError,
    xiHeatCassiniOrderedChebyshevError,
    hthetaEq]
  unfold xiMassPrimeHarmonicRealCoefficient
    xiHeatCassiniOrderedPrimeRelativeGap xiHeatCassiniOrderedPrimeGap
  field_simp [hp, hq]
  ring

/-- Backward log depletion is nonnegative: logarithmic cell length dominates right-normalized
additive spacing. -/
theorem xiHeatCassiniPrimeBackwardLogDepletion_nonneg (N : ℕ) :
    0 ≤ xiHeatCassiniPrimeBackwardLogDepletion N := by
  let x : ℝ := xiHeatCassiniOrderedPrimeRelativeGap N
  have hx : 0 ≤ x := xiHeatCassiniOrderedPrimeRelativeGap_nonneg N
  have hden : 0 < 1 + x := by linarith
  have hlog : x / (1 + x) ≤ Real.log (1 + x) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
    rw [Real.log_inv] at h
    have hne : 1 + x ≠ 0 := hden.ne'
    field_simp [hne] at h ⊢
    nlinarith
  rw [xiHeatCassiniPrimeBackwardLogDepletion,
    xiHeatCassiniOrderedPrimeLogGap_eq_log_one_add_relativeGap]
  have hp : (nthPrimeSubtype N : ℝ) ≠ 0 := (nthPrimeSubtype_pos N).ne'
  have hq : (nthPrimeSubtype (N + 1) : ℝ) ≠ 0 :=
    (nthPrimeSubtype_pos (N + 1)).ne'
  have hratio :
      xiHeatCassiniOrderedPrimeGap N / (nthPrimeSubtype (N + 1) : ℝ) =
        x / (1 + x) := by
    dsimp only [x]
    unfold xiHeatCassiniOrderedPrimeRelativeGap xiHeatCassiniOrderedPrimeGap
    field_simp [hp, hq]
    ring
  rw [hratio]
  exact sub_nonneg.mpr hlog

/-- Backward logarithmic depletion is bounded by normalized gap square and hence belongs to the
same critical-energy budget as log quadrature. -/
theorem xiHeatCassiniPrimeBackwardLogDepletion_le_relativeGap_sq (N : ℕ) :
    xiHeatCassiniPrimeBackwardLogDepletion N ≤
      xiHeatCassiniOrderedPrimeRelativeGap N ^ (2 : ℕ) := by
  have hlog := xiHeatCassiniOrderedPrimeLogGap_le_gap_div_prime N
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  let d : ℝ := xiHeatCassiniOrderedPrimeGap N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  have hpq : p ≤ q := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_strictMono.monotone (Nat.le_succ N)
  have htransport : d / p - d / q = d ^ (2 : ℕ) / (p * q) := by
    have hd : d = q - p := rfl
    rw [hd]
    field_simp [hp.ne', hq.ne']
  have hdenom : d ^ (2 : ℕ) / (p * q) ≤ d ^ (2 : ℕ) / (p * p) := by
    exact div_le_div_of_nonneg_left (sq_nonneg d) (mul_pos hp hp)
      (mul_le_mul_of_nonneg_left hpq hp.le)
  have hrelative : d ^ (2 : ℕ) / (p * p) =
      xiHeatCassiniOrderedPrimeRelativeGap N ^ (2 : ℕ) := by
    change d ^ (2 : ℕ) / (p * p) = (d / p) ^ (2 : ℕ)
    field_simp [hp.ne']
  calc
    xiHeatCassiniPrimeBackwardLogDepletion N =
        xiHeatCassiniOrderedPrimeLogGap N - d / q := rfl
    _ ≤ d / p - d / q := sub_le_sub_right hlog _
    _ = d ^ (2 : ℕ) / (p * q) := htransport
    _ ≤ d ^ (2 : ℕ) / (p * p) := hdenom
    _ = xiHeatCassiniOrderedPrimeRelativeGap N ^ (2 : ℕ) := hrelative

/-- Critical prime-gap energy absorbs the whole backward endpoint depletion at half density. -/
theorem primeBackwardLogDepletion_mul_sqrt_le_criticalEnergy (N : ℕ) :
    xiHeatCassiniPrimeBackwardLogDepletion N *
        Real.sqrt (nthPrimeSubtype N : ℝ) ≤
      xiHeatCassiniPrimeGapCriticalEnergy N := by
  have hsqrt : 0 ≤ Real.sqrt (nthPrimeSubtype N : ℝ) := Real.sqrt_nonneg _
  have h := mul_le_mul_of_nonneg_right
    (xiHeatCassiniPrimeBackwardLogDepletion_le_relativeGap_sq N) hsqrt
  unfold xiHeatCassiniOrderedPrimeRelativeGap at h
  unfold xiHeatCassiniPrimeGapCriticalEnergy
  nlinarith

/-- Finite-prefix form of critical-energy absorption for backward endpoint depletion. -/
theorem sum_primeBackwardLogDepletion_mul_sqrt_le_criticalEnergy (M : ℕ) :
    (∑ N ∈ Finset.range M,
        xiHeatCassiniPrimeBackwardLogDepletion N *
          Real.sqrt (nthPrimeSubtype N : ℝ)) ≤
      ∑ N ∈ Finset.range M, xiHeatCassiniPrimeGapCriticalEnergy N := by
  apply Finset.sum_le_sum
  intro N hN
  exact primeBackwardLogDepletion_mul_sqrt_le_criticalEnergy N

/-- The two quadratic endpoint corrections combine exactly into backward log depletion. -/
theorem xiHeatCassiniPrimeLogQuadratureError_sub_gapSq_eq_neg_backwardDepletion
    (N : ℕ) :
    xiHeatCassiniPrimeLogQuadratureError N -
        xiHeatCassiniOrderedPrimeGap N ^ (2 : ℕ) /
          ((nthPrimeSubtype N : ℝ) * (nthPrimeSubtype (N + 1) : ℝ)) =
      -xiHeatCassiniPrimeBackwardLogDepletion N := by
  have hp : (nthPrimeSubtype N : ℝ) ≠ 0 := (nthPrimeSubtype_pos N).ne'
  have hq : (nthPrimeSubtype (N + 1) : ℝ) ≠ 0 :=
    (nthPrimeSubtype_pos (N + 1)).ne'
  unfold xiHeatCassiniPrimeLogQuadratureError
    xiHeatCassiniOrderedPrimeRelativeGap
    xiHeatCassiniPrimeBackwardLogDepletion
    xiHeatCassiniOrderedPrimeGap
  field_simp [hp, hq]
  ring

/-- Exact PNT-error normal form for Route T. Residual variation is the normalized consecutive
Chebyshev-error jump minus two nonnegative depletions: Euler trace loss and backward log-cell loss. -/
theorem xiHeatCassiniOrderedWoldResidualIncrement_eq_chebyshevIncrement_sub_depletions
    (N : ℕ) :
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N =
      xiHeatCassiniNormalizedChebyshevErrorIncrement N -
        xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) -
          xiHeatCassiniPrimeBackwardLogDepletion N := by
  rw [xiHeatCassiniOrderedWoldResidualIncrement_eq_density_sub_euler_add_quadrature,
    xiHeatCassiniPrimeDensityGapFluctuation_eq_chebyshevIncrement_sub_gapSq]
  have hcombine :=
    xiHeatCassiniPrimeLogQuadratureError_sub_gapSq_eq_neg_backwardDepletion N
  calc
    (xiHeatCassiniNormalizedChebyshevErrorIncrement N -
          xiHeatCassiniOrderedPrimeGap N ^ (2 : ℕ) /
            ((nthPrimeSubtype N : ℝ) * (nthPrimeSubtype (N + 1) : ℝ))) -
        xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) +
          xiHeatCassiniPrimeLogQuadratureError N =
        xiHeatCassiniNormalizedChebyshevErrorIncrement N -
          xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) +
            (xiHeatCassiniPrimeLogQuadratureError N -
              xiHeatCassiniOrderedPrimeGap N ^ (2 : ℕ) /
                ((nthPrimeSubtype N : ℝ) *
                  (nthPrimeSubtype (N + 1) : ℝ))) := by ring
    _ = xiHeatCassiniNormalizedChebyshevErrorIncrement N -
          xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) -
            xiHeatCassiniPrimeBackwardLogDepletion N := by rw [hcombine]; ring

/-- One-sided orientation law: Route-T residual variation never exceeds the normalized local
Chebyshev-error jump. -/
theorem xiHeatCassiniOrderedWoldResidualIncrement_le_chebyshevIncrement (N : ℕ) :
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ≤
      xiHeatCassiniNormalizedChebyshevErrorIncrement N := by
  rw [xiHeatCassiniOrderedWoldResidualIncrement_eq_chebyshevIncrement_sub_depletions]
  have hEuler :=
    xiHeatCassiniWoldEulerTraceCorrection_nonneg (nthPrimeSubtype (N + 1))
  have hBackward := xiHeatCassiniPrimeBackwardLogDepletion_nonneg N
  linarith

/-- Exact finite conservation law. Every Route-T residual prefix is a Chebyshev-error increment
prefix depleted by Euler trace and backward log-cell masses. -/
theorem xiHeatCassiniOrderedWoldResidual_sub_zero_eq_sum_chebyshev_sub_depletions
    (M : ℕ) :
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy M -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 =
      (∑ N ∈ Finset.range M,
          xiHeatCassiniNormalizedChebyshevErrorIncrement N) -
        (∑ N ∈ Finset.range M,
          xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1))) -
        ∑ N ∈ Finset.range M, xiHeatCassiniPrimeBackwardLogDepletion N := by
  have hterm : ∀ N ∈ Finset.range M,
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
          xiHeatCassiniOrderedWoldResidualLogDiscrepancy N =
        xiHeatCassiniNormalizedChebyshevErrorIncrement N -
          xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) -
            xiHeatCassiniPrimeBackwardLogDepletion N := by
    intro N hN
    exact xiHeatCassiniOrderedWoldResidualIncrement_eq_chebyshevIncrement_sub_depletions N
  calc
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy M -
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy 0 =
      ∑ N ∈ Finset.range M,
        (xiHeatCassiniOrderedWoldResidualLogDiscrepancy (N + 1) -
          xiHeatCassiniOrderedWoldResidualLogDiscrepancy N) := by
        symm
        exact Finset.sum_range_sub _ M
    _ = ∑ N ∈ Finset.range M,
        (xiHeatCassiniNormalizedChebyshevErrorIncrement N -
          xiHeatCassiniWoldEulerTraceCorrection (nthPrimeSubtype (N + 1)) -
            xiHeatCassiniPrimeBackwardLogDepletion N) := by
        exact Finset.sum_congr rfl hterm
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

end

end RHTower
