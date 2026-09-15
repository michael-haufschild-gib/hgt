import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovQuadraticHorizonError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedEnergy
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovTunedMinLogAsymptotic
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedQuadraticHorizonEnergy

open Finset
open Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

theorem abs_barbanVehovIncludedLongHarmonicKernel_sub_continuous_le_horizon
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovIncludedLongHarmonicKernel L (L * M) q r -
        barbanVehovLongHarmonicKernelContinuous L (L * min q r) q r| ≤
      322 / (L : ℝ) := by
  have hmin1 : 1 ≤ min q r := le_min hq hr
  have hLmin : L ≤ L * min q r := by
    simpa using Nat.mul_le_mul_left L hmin1
  have heL := (lcm_le_square_of_bounded hq hr hqM hrM).trans hscale
  rw [barbanVehovIncludedLongHarmonicKernel_eq_minEndpoint hqM hrM]
  exact abs_barbanVehovLongHarmonicKernel_sub_continuous_le_horizon
    hq hr heL hLmin

theorem abs_barbanVehovIncludedLongFirstLogKernel_sub_continuous_le_horizon
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovIncludedLongFirstLogKernel L (L * M) q r -
        barbanVehovLongFirstLogKernelContinuous L (L * min q r) q r| ≤
      2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ) := by
  have hmin1 : 1 ≤ min q r := le_min hq hr
  have hminM : min q r ≤ M := (Nat.min_le_left q r).trans hqM
  have hLmin : L ≤ L * min q r := by
    simpa using Nat.mul_le_mul_left L hmin1
  have hU : L * min q r ≤ L * M := Nat.mul_le_mul_left L hminM
  have heL := (lcm_le_square_of_bounded hq hr hqM hrM).trans hscale
  rw [barbanVehovIncludedLongFirstLogKernel_eq_minEndpoint hqM hrM]
  refine (abs_barbanVehovLongFirstLogKernel_sub_continuous_le_horizon
    hq hr heL hLmin).trans ?_
  have hlog : Real.log (L * min q r + 1 : ℕ) ≤ Real.log (L * M + 1 : ℕ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hU 1)
  have hleft : 0 ≤ 1 + Real.log (L * min q r + 1 : ℕ) := by positivity
  have hright : 0 ≤ 1 + Real.log (L * M + 1 : ℕ) := by positivity
  have hsq : (1 + Real.log (L * min q r + 1 : ℕ)) ^ 2 ≤
      (1 + Real.log (L * M + 1 : ℕ)) ^ 2 := by
    nlinarith [mul_le_mul (show 1 + Real.log (L * min q r + 1 : ℕ) ≤
      1 + Real.log (L * M + 1 : ℕ) by linarith)
      (show 1 + Real.log (L * min q r + 1 : ℕ) ≤
        1 + Real.log (L * M + 1 : ℕ) by linarith) hleft hright]
  gcongr

theorem abs_barbanVehovIncludedLongSecondLogKernel_sub_continuous_le_horizon
    {L M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovIncludedLongSecondLogKernel L (L * M) q r -
        barbanVehovLongSecondLogKernelContinuous L (L * min q r) q r| ≤
      20000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ) := by
  have hmin1 : 1 ≤ min q r := le_min hq hr
  have hminM : min q r ≤ M := (Nat.min_le_left q r).trans hqM
  have hLmin : L ≤ L * min q r := by
    simpa using Nat.mul_le_mul_left L hmin1
  have hU : L * min q r ≤ L * M := Nat.mul_le_mul_left L hminM
  have heL := (lcm_le_square_of_bounded hq hr hqM hrM).trans hscale
  rw [barbanVehovIncludedLongSecondLogKernel_eq_minEndpoint hqM hrM]
  refine (abs_barbanVehovLongSecondLogKernel_sub_continuous_le_horizon
    hq hr heL hLmin).trans ?_
  have hlog : Real.log (L * min q r + 1 : ℕ) ≤ Real.log (L * M + 1 : ℕ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hU 1)
  have hleft : 0 ≤ 1 + Real.log (L * min q r + 1 : ℕ) := by positivity
  have hright : 0 ≤ 1 + Real.log (L * M + 1 : ℕ) := by positivity
  have hsq : (1 + Real.log (L * min q r + 1 : ℕ)) ^ 2 ≤
      (1 + Real.log (L * M + 1 : ℕ)) ^ 2 := by
    nlinarith [mul_le_mul (show 1 + Real.log (L * min q r + 1 : ℕ) ≤
      1 + Real.log (L * M + 1 : ℕ) by linarith)
      (show 1 + Real.log (L * min q r + 1 : ℕ) ≤
        1 + Real.log (L * M + 1 : ℕ) by linarith) hleft hright]
  gcongr

theorem abs_barbanVehovIncludedLongBaseLcm_sub_continuous_le_horizon
    {L M : ℕ} (hM : 1 ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovIncludedLongBaseLcm L M -
        barbanVehovIncludedLongBaseContinuous L M| ≤
      (M : ℝ) ^ 2 * (322 / (L : ℝ)) := by
  rw [barbanVehovIncludedLongBaseLcm, barbanVehovIncludedLongBaseContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovIncludedLongHarmonicKernel L (L * M) p.1 p.2 -
          barbanVehovLongHarmonicKernelContinuous L (L * min p.1 p.2) p.1 p.2| ≤
        322 / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovIncludedLongHarmonicKernel_sub_continuous_le_horizon
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovIncludedLongHarmonicKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongHarmonicKernelContinuous L (L * min p.1 p.2) p.1 p.2)
    hpoint
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le_quadratic hM) (by positivity))

theorem abs_barbanVehovIncludedLongCrossLcm_sub_continuous_le_horizon
    {L M : ℕ} (hM : 1 ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovIncludedLongCrossLcm L M -
        barbanVehovIncludedLongCrossContinuous L M| ≤
      (M : ℝ) ^ 2 *
        (2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
  rw [barbanVehovIncludedLongCrossLcm, barbanVehovIncludedLongCrossContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovIncludedLongFirstLogKernel L (L * M) p.1 p.2 -
          barbanVehovLongFirstLogKernelContinuous L (L * min p.1 p.2) p.1 p.2| ≤
        2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovIncludedLongFirstLogKernel_sub_continuous_le_horizon
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2))
    (fun p => barbanVehovIncludedLongFirstLogKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongFirstLogKernelContinuous L (L * min p.1 p.2) p.1 p.2)
    hpoint
  change |(∑ p ∈ s, -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovIncludedLongFirstLogKernel L (L * M) p.1 p.2) -
    ∑ p ∈ s, -(barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
      barbanVehovLongFirstLogKernelContinuous L (L * min p.1 p.2) p.1 p.2| ≤ _
  calc
    _ ≤ (∑ p ∈ s, |-(barbanVehovWeight M p.1 * barbanVehovWeight M p.2)|) *
        (2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := hraw
    _ = (∑ p ∈ s, |barbanVehovWeight M p.1 * barbanVehovWeight M p.2|) *
        (2000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
      simp only [abs_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_product_abs_barbanVehovWeight_le_quadratic hM) (by positivity)

theorem abs_barbanVehovIncludedLongDerivativeLcm_sub_continuous_le_horizon
    {L M : ℕ} (hM : 1 ≤ M) (hscale : M ^ 2 ≤ L) :
    |barbanVehovIncludedLongDerivativeLcm L M -
        barbanVehovIncludedLongDerivativeContinuous L M| ≤
      (M : ℝ) ^ 2 *
        (20000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ)) := by
  rw [barbanVehovIncludedLongDerivativeLcm, barbanVehovIncludedLongDerivativeContinuous]
  let s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  have hpoint : ∀ p ∈ s,
      |barbanVehovIncludedLongSecondLogKernel L (L * M) p.1 p.2 -
          barbanVehovLongSecondLogKernelContinuous L (L * min p.1 p.2) p.1 p.2| ≤
        20000 * (1 + Real.log (L * M + 1 : ℕ)) ^ 2 / (L : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    exact abs_barbanVehovIncludedLongSecondLogKernel_sub_continuous_le_horizon
      hp1.1 hp2.1 hp1.2 hp2.2 hscale
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise s
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovIncludedLongSecondLogKernel L (L * M) p.1 p.2)
    (fun p => barbanVehovLongSecondLogKernelContinuous L (L * min p.1 p.2) p.1 p.2)
    hpoint
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le_quadratic hM) (by positivity))

private theorem one_le_two_mul_log_nat_included {N : ℕ} (hN : 2 ≤ N) :
    (1 : ℝ) ≤ 2 * Real.log N := by
  have hlogmono : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  nlinarith [Real.log_two_gt_d9]

theorem abs_barbanVehovIncludedLongBaseLcm_quadraticHorizon_div_log_sq_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovIncludedLongBaseLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log N) ^ 2 -
        barbanVehovIncludedLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log N) ^ 2| ≤
      322 / (49 * Real.log N) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 49 := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ 49 := hM0
  have hscale : (N ^ 49) ^ 2 ≤ N ^ 98 := by
    have : (N ^ 49) ^ 2 = N ^ 98 := by ring
    exact this.le
  have herr := abs_barbanVehovIncludedLongBaseLcm_sub_continuous_le_horizon hM1 hscale
  rw [barbanVehovIncludedLongBaseContinuous_eq_polynomialMain (pow_pos hN0 98)] at herr
  have herr' :
      |barbanVehovIncludedLongBaseLcm (N ^ 98) (N ^ 49) -
          barbanVehovIncludedLongBasePolynomialMain (N ^ 49)| ≤ 322 := by
    refine herr.trans_eq ?_
    norm_num [Nat.cast_pow]
    field_simp [hNR.ne']
  exact abs_div_sub_div_le_of_abs_sub_le
    (sq_nonneg (49 * Real.log (N : ℝ))) herr'

theorem abs_barbanVehovIncludedLongCrossLcm_quadraticHorizon_div_log_cube_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovIncludedLongCrossLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log N) ^ 3 -
        barbanVehovIncludedLongCrossPolynomialMain
            (98 * Real.log N) (N ^ 49) /
          (49 * Real.log N) ^ 3| ≤
      400 / Real.log N := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 49 := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ 49 := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogL : Real.log (((N ^ 98 : ℕ) : ℝ)) = 98 * Real.log (N : ℝ) := by
    rw [show (((N ^ 98 : ℕ) : ℝ)) = (N : ℝ) ^ 98 by norm_num,
      Real.log_pow]
    norm_num
  let K := Real.log (N ^ 98 * N ^ 49 + 1 : ℕ)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : K ≤ 148 * Real.log N :=
    log_quadraticHorizon_mul_add_one_le_oneHundredFortyEight_log hN
  have h1K : 1 + K ≤ 150 * Real.log N := by
    nlinarith [one_le_two_mul_log_nat_included hN]
  have h1K0 : 0 ≤ 1 + K := by positivity
  have h1Ksq : (1 + K) ^ 2 ≤ 22500 * Real.log N ^ 2 := by
    nlinarith [mul_le_mul h1K h1K h1K0 (by positivity)]
  have hscale : (N ^ 49) ^ 2 ≤ N ^ 98 := by
    have : (N ^ 49) ^ 2 = N ^ 98 := by ring
    exact this.le
  have herr := abs_barbanVehovIncludedLongCrossLcm_sub_continuous_le_horizon hM1 hscale
  rw [barbanVehovIncludedLongCrossContinuous_eq_polynomialMain (pow_pos hN0 98), hlogL] at herr
  have herr' :
      |barbanVehovIncludedLongCrossLcm (N ^ 98) (N ^ 49) -
          barbanVehovIncludedLongCrossPolynomialMain
            (98 * Real.log N) (N ^ 49)| ≤ 2000 * (1 + K) ^ 2 := by
    refine herr.trans_eq ?_
    dsimp [K]
    norm_num [Nat.cast_pow]
    field_simp [hNR.ne']
  have hscaled := abs_div_sub_div_le_of_abs_sub_le
    (D := (49 * Real.log (N : ℝ)) ^ 3) (pow_nonneg (by positivity) 3) herr'
  calc
    _ ≤ (2000 * (1 + K) ^ 2) / (49 * Real.log N) ^ 3 := hscaled
    _ ≤ 400 / Real.log N := by
      rw [div_le_div_iff₀ (by positivity) hlogPos]
      have hs := mul_le_mul_of_nonneg_left h1Ksq (by norm_num : (0 : ℝ) ≤ 2000)
      nlinarith

theorem abs_barbanVehovIncludedLongDerivativeLcm_quadraticHorizon_div_log_four_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovIncludedLongDerivativeLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log N) ^ 4 -
        barbanVehovIncludedLongDerivativePolynomialMain
            (98 * Real.log N) (N ^ 49) /
          (49 * Real.log N) ^ 4| ≤
      79 / Real.log N ^ 2 := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 49 := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ 49 := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogL : Real.log (((N ^ 98 : ℕ) : ℝ)) = 98 * Real.log (N : ℝ) := by
    rw [show (((N ^ 98 : ℕ) : ℝ)) = (N : ℝ) ^ 98 by norm_num,
      Real.log_pow]
    norm_num
  let K := Real.log (N ^ 98 * N ^ 49 + 1 : ℕ)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : K ≤ 148 * Real.log N :=
    log_quadraticHorizon_mul_add_one_le_oneHundredFortyEight_log hN
  have h1K : 1 + K ≤ 150 * Real.log N := by
    nlinarith [one_le_two_mul_log_nat_included hN]
  have h1K0 : 0 ≤ 1 + K := by positivity
  have h1Ksq : (1 + K) ^ 2 ≤ 22500 * Real.log N ^ 2 := by
    nlinarith [mul_le_mul h1K h1K h1K0 (by positivity)]
  have hscale : (N ^ 49) ^ 2 ≤ N ^ 98 := by
    have : (N ^ 49) ^ 2 = N ^ 98 := by ring
    exact this.le
  have herr := abs_barbanVehovIncludedLongDerivativeLcm_sub_continuous_le_horizon hM1 hscale
  rw [barbanVehovIncludedLongDerivativeContinuous_eq_polynomialMain (pow_pos hN0 98), hlogL] at herr
  have herr' :
      |barbanVehovIncludedLongDerivativeLcm (N ^ 98) (N ^ 49) -
          barbanVehovIncludedLongDerivativePolynomialMain
            (98 * Real.log N) (N ^ 49)| ≤ 20000 * (1 + K) ^ 2 := by
    refine herr.trans_eq ?_
    dsimp [K]
    norm_num [Nat.cast_pow]
    field_simp [hNR.ne']
  have hscaled := abs_div_sub_div_le_of_abs_sub_le
    (D := (49 * Real.log (N : ℝ)) ^ 4) (pow_nonneg (by positivity) 4) herr'
  calc
    _ ≤ (20000 * (1 + K) ^ 2) / (49 * Real.log N) ^ 4 := hscaled
    _ ≤ 79 / Real.log N ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hlogPos)]
      have hs := mul_le_mul_of_nonneg_left h1Ksq (by norm_num : (0 : ℝ) ≤ 20000)
      nlinarith

private theorem tendsto_nat_pow_fortyNine_atTop_included_horizon :
    Tendsto (fun N : ℕ => N ^ 49) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop (max B 1)] with N hN
  have hBN : B ≤ N := (Nat.le_max_left B 1).trans hN
  have hN1 : 1 ≤ N := (Nat.le_max_right B 1).trans hN
  exact hBN.trans (by
    calc
      N ≤ N * N ^ 48 := Nat.le_mul_of_pos_right N (pow_pos hN1 48)
      _ = N ^ 49 := by ring)

theorem tendsto_barbanVehovIncludedLongEnergyPolynomialMain_quadraticHorizon_half :
    Tendsto (fun N : ℕ =>
      barbanVehovIncludedLongEnergyPolynomialMain
        ((1 / 2 : ℝ) / (49 * Real.log N))
        (98 * Real.log N) (N ^ 49))
      atTop (𝓝 ((1 / 2 : ℝ) ^ 2 / 12)) := by
  have hbase := tendsto_barbanVehovIncludedLongEnergyPolynomialMain_tuned_rho
    (1 / 2 : ℝ) (by norm_num)
  have hcomp := hbase.comp tendsto_nat_pow_fortyNine_atTop_included_horizon
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  simp only [Function.comp_apply]
  rw [show (((N ^ 49 : ℕ) : ℝ)) = (N : ℝ) ^ 49 by norm_num,
    Real.log_pow]
  congr 2
  ring

theorem abs_levinsonCriticalDetectorLongEnergy_quadraticHorizon_half_sub_polynomialMain_le
    {N : ℕ} (hN : 2 ≤ N) :
    |RHTower.levinsonCriticalDetectorLongEnergy
          ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ 98) (N ^ 49) -
        barbanVehovIncludedLongEnergyPolynomialMain
          ((1 / 2 : ℝ) / (49 * Real.log N))
          (98 * Real.log N) (N ^ 49)| ≤
      322 / (49 * Real.log N) ^ 2 + 400 / Real.log N +
        (1 / 4 : ℝ) * (79 / Real.log N ^ 2) := by
  have hN0 : 0 < N := by omega
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hM : 1 < N ^ 49 := by
    exact (by omega : 1 < N).trans_le (by
      calc
        N ≤ N * N ^ 48 := Nat.le_mul_of_pos_right N (pow_pos hN0 48)
        _ = N ^ 49 := by ring)
  have hML : N ^ 49 ≤ N ^ 98 := by
    calc
      N ^ 49 ≤ N ^ 49 * N ^ 49 :=
        Nat.le_mul_of_pos_right _ (pow_pos hN0 49)
      _ = N ^ 98 := by ring
  have hlogM : Real.log (((N ^ 49 : ℕ) : ℝ)) = 49 * Real.log N := by
    rw [show (((N ^ 49 : ℕ) : ℝ)) = (N : ℝ) ^ 49 by norm_num,
      Real.log_pow]
    norm_num
  rw [levinsonCriticalDetectorLongEnergy_eq_includedLcm
    ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ 98) hM hML,
    barbanVehovIncludedLongEnergyLcm,
    barbanVehovIncludedLongEnergyPolynomialMain, hlogM]
  let eB := barbanVehovIncludedLongBaseLcm (N ^ 98) (N ^ 49) /
      (49 * Real.log N) ^ 2 -
    barbanVehovIncludedLongBasePolynomialMain (N ^ 49) /
      (49 * Real.log N) ^ 2
  let eC := barbanVehovIncludedLongCrossLcm (N ^ 98) (N ^ 49) /
      (49 * Real.log N) ^ 3 -
    barbanVehovIncludedLongCrossPolynomialMain (98 * Real.log N) (N ^ 49) /
      (49 * Real.log N) ^ 3
  let eD := barbanVehovIncludedLongDerivativeLcm (N ^ 98) (N ^ 49) /
      (49 * Real.log N) ^ 4 -
    barbanVehovIncludedLongDerivativePolynomialMain (98 * Real.log N) (N ^ 49) /
      (49 * Real.log N) ^ 4
  have hbase : |eB| ≤ 322 / (49 * Real.log N) ^ 2 := by
    exact abs_barbanVehovIncludedLongBaseLcm_quadraticHorizon_div_log_sq_sub_polynomial_le hN
  have hcross : |eC| ≤ 400 / Real.log N := by
    exact abs_barbanVehovIncludedLongCrossLcm_quadraticHorizon_div_log_cube_sub_polynomial_le hN
  have hderiv : |eD| ≤ 79 / Real.log N ^ 2 := by
    exact abs_barbanVehovIncludedLongDerivativeLcm_quadraticHorizon_div_log_four_sub_polynomial_le hN
  have heq :
      (barbanVehovIncludedLongBaseLcm (N ^ 98) (N ^ 49) +
            2 * ((1 / 2 : ℝ) / (49 * Real.log N)) *
              barbanVehovIncludedLongCrossLcm (N ^ 98) (N ^ 49) +
            ((1 / 2 : ℝ) / (49 * Real.log N)) ^ 2 *
              barbanVehovIncludedLongDerivativeLcm (N ^ 98) (N ^ 49)) /
          (49 * Real.log N) ^ 2 -
        (barbanVehovIncludedLongBasePolynomialMain (N ^ 49) +
            2 * ((1 / 2 : ℝ) / (49 * Real.log N)) *
              barbanVehovIncludedLongCrossPolynomialMain (98 * Real.log N) (N ^ 49) +
            ((1 / 2 : ℝ) / (49 * Real.log N)) ^ 2 *
              barbanVehovIncludedLongDerivativePolynomialMain
                (98 * Real.log N) (N ^ 49)) /
          (49 * Real.log N) ^ 2 = eB + eC + (1 / 4 : ℝ) * eD := by
    dsimp only [eB, eC, eD]
    field_simp [hlog]
    ring
  rw [heq]
  calc
    |eB + eC + (1 / 4 : ℝ) * eD| ≤
        |eB| + |eC| + (1 / 4 : ℝ) * |eD| := by
      calc
        _ ≤ |eB + eC| + |(1 / 4 : ℝ) * eD| := abs_add_le _ _
        _ ≤ (|eB| + |eC|) + |(1 / 4 : ℝ) * eD| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_mul]; norm_num
    _ ≤ 322 / (49 * Real.log N) ^ 2 + 400 / Real.log N +
        (1 / 4 : ℝ) * (79 / Real.log N ^ 2) := by
      exact add_le_add (add_le_add hbase hcross)
        (mul_le_mul_of_nonneg_left hderiv (by norm_num))

private theorem tendsto_const_div_log_nat_included_horizon (c : ℝ) :
    Tendsto (fun N : ℕ => c / Real.log N) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem tendsto_const_div_log_nat_sq_included_horizon (c : ℝ) :
    Tendsto (fun N : ℕ => c / Real.log N ^ 2) atTop (𝓝 0) := by
  have hc := tendsto_const_div_log_nat_included_horizon c
  have h1 := tendsto_const_div_log_nat_included_horizon 1
  have hmul := hc.mul h1
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  field_simp [hlog]

/-- Actual included detector retains exact mass `1/48` at `L=M²`. -/
theorem tendsto_levinsonCriticalDetectorLongEnergy_quadraticHorizon_half :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorLongEnergy
        ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ 98) (N ^ 49))
      atTop (𝓝 (1 / 48 : ℝ)) := by
  let P : ℕ → ℝ := fun N =>
    barbanVehovIncludedLongEnergyPolynomialMain
      ((1 / 2 : ℝ) / (49 * Real.log N)) (98 * Real.log N) (N ^ 49)
  have hP : Tendsto P atTop (𝓝 (1 / 48 : ℝ)) := by
    convert tendsto_barbanVehovIncludedLongEnergyPolynomialMain_quadraticHorizon_half using 1
    norm_num
  have hbase : Tendsto (fun N : ℕ =>
      322 / (49 * Real.log N) ^ 2) atTop (𝓝 0) := by
    have h := tendsto_const_div_log_nat_sq_included_horizon (322 / 49 ^ 2)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
    field_simp [hlog]
  have hbound := (hbase.add (tendsto_const_div_log_nat_included_horizon 400)).add
    ((tendsto_const_div_log_nat_sq_included_horizon 79).const_mul (1 / 4 : ℝ))
  have hbound' : Tendsto (fun N : ℕ =>
      322 / (49 * Real.log N) ^ 2 + 400 / Real.log N +
        (1 / 4 : ℝ) * (79 / Real.log N ^ 2)) atTop (𝓝 0) := by
    simpa using hbound
  have habs : Tendsto (fun N : ℕ =>
      |RHTower.levinsonCriticalDetectorLongEnergy
          ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ 98) (N ^ 49) - P N|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hbound'
    filter_upwards [eventually_ge_atTop 2] with N hN
    simpa only [P] using
      abs_levinsonCriticalDetectorLongEnergy_quadraticHorizon_half_sub_polynomialMain_le hN
  have herr : Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorLongEnergy
          ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ 98) (N ^ 49) - P N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, norm_zero] using habs
  simpa only [P, zero_add] using (herr.add hP).congr'
    (Eventually.of_forall fun N => by ring)

end
end RHTower.Sieve
