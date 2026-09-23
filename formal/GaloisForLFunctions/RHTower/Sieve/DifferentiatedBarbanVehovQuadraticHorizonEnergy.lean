import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovQuadraticHorizonError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovGeneralScaleMain
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorFullLongMomentExpansion

open Filter Topology

namespace RHTower.Sieve

noncomputable section

private theorem quadratic_horizon_eq {N : ℕ} : (N ^ (49 : ℕ)) ^ (2 : ℕ) = N ^ (98 : ℕ) := by ring

private theorem quadratic_horizon_log_relation {N : ℕ} :
    Real.log (((N ^ (98 : ℕ) : ℕ) : ℝ)) =
      (2 : ℝ) * Real.log (((N ^ (49 : ℕ) : ℕ) : ℝ)) := by
  rw [show (((N ^ (98 : ℕ) : ℕ) : ℝ)) = (N : ℝ) ^ (98 : ℕ) by norm_num,
    show (((N ^ (49 : ℕ) : ℕ) : ℝ)) = (N : ℝ) ^ (49 : ℕ) by norm_num,
    Real.log_pow, Real.log_pow]
  norm_num
  ring

private theorem one_le_two_mul_log_nat {N : ℕ} (hN : 2 ≤ N) :
    (1 : ℝ) ≤ 2 * Real.log N := by
  have hlogmono : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  nlinarith [Real.log_two_gt_d9]

private theorem log_quadratic_horizon_mul_add_one_le {N : ℕ} (hN : 2 ≤ N) :
    Real.log (N ^ (98 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ) ≤ 148 * Real.log N := by
  have hprodPos : 0 < N ^ (98 : ℕ) * N ^ (49 : ℕ) := by positivity
  have hpow : N ^ (98 : ℕ) * N ^ (49 : ℕ) + 1 ≤ N ^ (148 : ℕ) := by
    calc
      N ^ (98 : ℕ) * N ^ (49 : ℕ) + 1 ≤
          N ^ (98 : ℕ) * N ^ (49 : ℕ) + N ^ (98 : ℕ) * N ^ (49 : ℕ) :=
        Nat.add_le_add_left hprodPos _
      _ = 2 * (N ^ (98 : ℕ) * N ^ (49 : ℕ)) := by ring
      _ ≤ N * (N ^ (98 : ℕ) * N ^ (49 : ℕ)) := Nat.mul_le_mul_right _ hN
      _ = N ^ (148 : ℕ) := by ring
  have hlog := Real.log_le_log
    (show (0 : ℝ) < ((N ^ (98 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ) : ℝ) by positivity)
    (show ((N ^ (98 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ) : ℝ) ≤ ((N ^ (148 : ℕ) : ℕ) : ℝ) by
      exact_mod_cast hpow)
  rw [show ((N ^ (148 : ℕ) : ℕ) : ℝ) = (N : ℝ) ^ (148 : ℕ) by norm_num,
    Real.log_pow] at hlog
  norm_num at hlog
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hlog ⊢
  exact hlog

private theorem abs_common_div_sub_common_div_le
    {a b E D : ℝ} (hD : 0 ≤ D) (h : |a - b| ≤ E) :
    |a / D - b / D| ≤ E / D := by
  rw [← sub_div, abs_div, abs_of_nonneg hD]
  exact div_le_div_of_nonneg_right h hD

theorem abs_barbanVehovFullLongBaseLcm_quadraticHorizon_div_log_sq_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovFullLongBaseLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (2 : ℕ) -
        barbanVehovLongBasePolynomialMain (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (2 : ℕ)| ≤
      322 / (49 * Real.log N) ^ (2 : ℕ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ (49 : ℕ) := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ (49 : ℕ) := hM0
  have hscale : (N ^ (49 : ℕ)) ^ (2 : ℕ) ≤ N ^ (98 : ℕ) := quadratic_horizon_eq.le
  have herr := abs_barbanVehovFullLongBaseLcm_sub_continuous_le_horizon hM1 hscale
  rw [barbanVehovFullLongBaseContinuous_eq_polynomialMain
    (pow_pos hN0 98) hM0 quadratic_horizon_log_relation] at herr
  have herr' :
      |barbanVehovFullLongBaseLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) -
          barbanVehovLongBasePolynomialMain (N ^ (49 : ℕ))| ≤ 322 := by
    refine herr.trans_eq ?_
    norm_num [Nat.cast_pow]
    field_simp [hNR.ne']
  exact abs_common_div_sub_common_div_le
    (sq_nonneg (49 * Real.log (N : ℝ))) herr'

theorem abs_barbanVehovFullLongCrossLcm_quadraticHorizon_div_log_cube_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovFullLongCrossLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ) -
        barbanVehovLongCrossPolynomialMain 2 (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ)| ≤
      400 / Real.log N := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ (49 : ℕ) := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ (49 : ℕ) := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let K := Real.log (N ^ (98 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hK : K ≤ 148 * Real.log N := log_quadratic_horizon_mul_add_one_le hN
  have h1K : 1 + K ≤ 150 * Real.log N := by
    nlinarith [one_le_two_mul_log_nat hN]
  have h1K0 : 0 ≤ 1 + K := by positivity
  have h1Ksq : (1 + K) ^ (2 : ℕ) ≤ 22500 * Real.log N ^ (2 : ℕ) := by
    nlinarith [mul_le_mul h1K h1K h1K0 (by positivity)]
  have hscale : (N ^ (49 : ℕ)) ^ (2 : ℕ) ≤ N ^ (98 : ℕ) := quadratic_horizon_eq.le
  have herr := abs_barbanVehovFullLongCrossLcm_sub_continuous_le_horizon hM1 hscale
  rw [barbanVehovFullLongCrossContinuous_eq_polynomialMain
    (pow_pos hN0 98) hM0 quadratic_horizon_log_relation] at herr
  have herr' :
      |barbanVehovFullLongCrossLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) -
          barbanVehovLongCrossPolynomialMain 2 (N ^ (49 : ℕ))| ≤
        2000 * (1 + K) ^ (2 : ℕ) := by
    refine herr.trans_eq ?_
    dsimp [K]
    norm_num [Nat.cast_pow]
    field_simp [hNR.ne']
  have hscaled := abs_common_div_sub_common_div_le
    (D := (49 * Real.log (N : ℝ)) ^ (3 : ℕ)) (pow_nonneg (by positivity) 3) herr'
  calc
    |barbanVehovFullLongCrossLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ) -
        barbanVehovLongCrossPolynomialMain 2 (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ)| ≤
      (2000 * (1 + K) ^ (2 : ℕ)) / (49 * Real.log N) ^ (3 : ℕ) := hscaled
    _ ≤ 400 / Real.log N := by
      rw [div_le_div_iff₀ (by positivity) hlogPos]
      have hs := mul_le_mul_of_nonneg_left h1Ksq (by norm_num : (0 : ℝ) ≤ 2000)
      nlinarith

theorem abs_barbanVehovFullLongDerivativeLcm_quadraticHorizon_div_log_four_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovFullLongDerivativeLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ) -
        barbanVehovLongDerivativePolynomialMain 2 (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ)| ≤
      79 / Real.log N ^ (2 : ℕ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ (49 : ℕ) := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ (49 : ℕ) := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let K := Real.log (N ^ (98 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hK : K ≤ 148 * Real.log N := log_quadratic_horizon_mul_add_one_le hN
  have h1K : 1 + K ≤ 150 * Real.log N := by
    nlinarith [one_le_two_mul_log_nat hN]
  have h1K0 : 0 ≤ 1 + K := by positivity
  have h1Ksq : (1 + K) ^ (2 : ℕ) ≤ 22500 * Real.log N ^ (2 : ℕ) := by
    nlinarith [mul_le_mul h1K h1K h1K0 (by positivity)]
  have hscale : (N ^ (49 : ℕ)) ^ (2 : ℕ) ≤ N ^ (98 : ℕ) := quadratic_horizon_eq.le
  have herr := abs_barbanVehovFullLongDerivativeLcm_sub_continuous_le_horizon hM1 hscale
  rw [barbanVehovFullLongDerivativeContinuous_eq_polynomialMain
    (pow_pos hN0 98) hM0 quadratic_horizon_log_relation] at herr
  have herr' :
      |barbanVehovFullLongDerivativeLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) -
          barbanVehovLongDerivativePolynomialMain 2 (N ^ (49 : ℕ))| ≤
        20000 * (1 + K) ^ (2 : ℕ) := by
    refine herr.trans_eq ?_
    dsimp [K]
    norm_num [Nat.cast_pow]
    field_simp [hNR.ne']
  have hscaled := abs_common_div_sub_common_div_le
    (D := (49 * Real.log (N : ℝ)) ^ (4 : ℕ)) (pow_nonneg (by positivity) 4) herr'
  calc
    |barbanVehovFullLongDerivativeLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ) -
        barbanVehovLongDerivativePolynomialMain 2 (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ)| ≤
      (20000 * (1 + K) ^ (2 : ℕ)) / (49 * Real.log N) ^ (4 : ℕ) := hscaled
    _ ≤ 79 / Real.log N ^ (2 : ℕ) := by
      rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hlogPos)]
      have hs := mul_le_mul_of_nonneg_left h1Ksq (by norm_num : (0 : ℝ) ≤ 20000)
      nlinarith

private theorem tendsto_nat_pow_fortyNine_atTop_quadratic_full :
    Tendsto (fun N : ℕ => N ^ (49 : ℕ)) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop (max B 1)] with N hN
  have hBN : B ≤ N := (Nat.le_max_left B 1).trans hN
  have hN1 : 1 ≤ N := (Nat.le_max_right B 1).trans hN
  exact hBN.trans (by
    calc
      N ≤ N * N ^ (48 : ℕ) := Nat.le_mul_of_pos_right N (pow_pos hN1 48)
      _ = N ^ (49 : ℕ) := by ring)

private theorem tendsto_const_div_log_nat (c : ℝ) :
    Tendsto (fun N : ℕ => c / Real.log N) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem tendsto_const_div_log_nat_sq (c : ℝ) :
    Tendsto (fun N : ℕ => c / Real.log N ^ (2 : ℕ)) atTop (𝓝 0) := by
  have hc := tendsto_const_div_log_nat c
  have h1 := tendsto_const_div_log_nat 1
  have hmul := hc.mul h1
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  field_simp [hlog]

theorem tendsto_barbanVehovFullLongBaseLcm_quadraticHorizon_div_log_sq_one :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongBaseLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (2 : ℕ)) atTop (𝓝 1) := by
  have hbound : Tendsto (fun N : ℕ =>
      322 / (49 * Real.log N) ^ (2 : ℕ)) atTop (𝓝 0) := by
    have h := tendsto_const_div_log_nat_sq (322 / 49 ^ (2 : ℕ))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
    field_simp [hlog]
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongBaseLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (2 : ℕ) -
        barbanVehovLongBasePolynomialMain (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (2 : ℕ)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact abs_barbanVehovFullLongBaseLcm_quadraticHorizon_div_log_sq_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongBaseLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (2 : ℕ) -
        barbanVehovLongBasePolynomialMain (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (2 : ℕ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain := tendsto_barbanVehovLongBasePolynomialMain_div_log_sq_one.comp
    tendsto_nat_pow_fortyNine_atTop_quadratic_full
  have hmain' : Tendsto (fun N : ℕ =>
      barbanVehovLongBasePolynomialMain (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (2 : ℕ)) atTop (𝓝 1) := by
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [Function.comp_apply]
    rw [show ((N ^ (49 : ℕ) : ℕ) : ℝ) = (N : ℝ) ^ (49 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  simpa only [sub_add_cancel, zero_add] using hdiff.add hmain'

theorem tendsto_barbanVehovFullLongCrossLcm_quadraticHorizon_div_log_cube :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongCrossLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (3 : ℕ)) atTop (𝓝 (-(2 + (1 / 2 : ℝ)))) := by
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongCrossLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ) -
        barbanVehovLongCrossPolynomialMain 2 (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
      (tendsto_const_div_log_nat 400)
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact abs_barbanVehovFullLongCrossLcm_quadraticHorizon_div_log_cube_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongCrossLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ) -
        barbanVehovLongCrossPolynomialMain 2 (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain := (tendsto_barbanVehovLongCrossPolynomialMain_div_log_cube 2).comp
    tendsto_nat_pow_fortyNine_atTop_quadratic_full
  have hmain' : Tendsto (fun N : ℕ =>
      barbanVehovLongCrossPolynomialMain 2 (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (3 : ℕ)) atTop (𝓝 (-(2 + (1 / 2 : ℝ)))) := by
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [Function.comp_apply]
    rw [show ((N ^ (49 : ℕ) : ℕ) : ℝ) = (N : ℝ) ^ (49 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  simpa only [sub_add_cancel, zero_add] using hdiff.add hmain'

theorem tendsto_barbanVehovFullLongDerivativeLcm_quadraticHorizon_div_log_four :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongDerivativeLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (4 : ℕ)) atTop (𝓝 ((2 : ℝ) ^ (2 : ℕ) + 2 + 2 / 3)) := by
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongDerivativeLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ) -
        barbanVehovLongDerivativePolynomialMain 2 (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
      (tendsto_const_div_log_nat_sq 79)
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact abs_barbanVehovFullLongDerivativeLcm_quadraticHorizon_div_log_four_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongDerivativeLcm (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ) -
        barbanVehovLongDerivativePolynomialMain 2 (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain := (tendsto_barbanVehovLongDerivativePolynomialMain_div_log_four 2).comp
    tendsto_nat_pow_fortyNine_atTop_quadratic_full
  have hmain' : Tendsto (fun N : ℕ =>
      barbanVehovLongDerivativePolynomialMain 2 (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (4 : ℕ)) atTop (𝓝 ((2 : ℝ) ^ (2 : ℕ) + 2 + 2 / 3)) := by
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [Function.comp_apply]
    rw [show ((N ^ (49 : ℕ) : ℕ) : ℝ) = (N : ℝ) ^ (49 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  simpa only [sub_add_cancel, zero_add] using hdiff.add hmain'

private theorem pow_fortyNine_le_pow_ninetyEight {N : ℕ} (hN : 0 < N) :
    N ^ (49 : ℕ) ≤ N ^ (98 : ℕ) := by
  calc
    N ^ (49 : ℕ) ≤ N ^ (49 : ℕ) * N ^ (49 : ℕ) :=
      Nat.le_mul_of_pos_right _ (pow_pos hN 49)
    _ = N ^ (98 : ℕ) := by ring

private theorem two_le_pow_fortyNine_quadratic {N : ℕ} (hN : 2 ≤ N) :
    2 ≤ N ^ (49 : ℕ) := by
  refine hN.trans ?_
  calc
    N ≤ N * N ^ (48 : ℕ) := Nat.le_mul_of_pos_right N (pow_pos (by omega) 48)
    _ = N ^ (49 : ℕ) := by ring

theorem tendsto_levinsonCriticalDetectorFullLongBaseMoment_quadraticHorizon_div_log_sq_one :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongBaseMoment (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (2 : ℕ)) atTop (𝓝 1) := by
  refine tendsto_barbanVehovFullLongBaseLcm_quadraticHorizon_div_log_sq_one.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongBaseMoment_eq_lcm
    (Nat.one_lt_two.trans_le (two_le_pow_fortyNine_quadratic hN))
      (pow_fortyNine_le_pow_ninetyEight (by omega))]

theorem tendsto_levinsonCriticalDetectorFullLongCrossMoment_quadraticHorizon_div_log_cube :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongCrossMoment (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (3 : ℕ)) atTop (𝓝 (-(2 + (1 / 2 : ℝ)))) := by
  refine tendsto_barbanVehovFullLongCrossLcm_quadraticHorizon_div_log_cube.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongCrossMoment_eq_lcm
    (Nat.one_lt_two.trans_le (two_le_pow_fortyNine_quadratic hN))
      (pow_fortyNine_le_pow_ninetyEight (by omega))]

theorem tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_quadraticHorizon_div_log_four :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongDerivativeMoment (N ^ (98 : ℕ)) (N ^ (49 : ℕ)) /
        (49 * Real.log N) ^ (4 : ℕ)) atTop (𝓝 ((2 : ℝ) ^ (2 : ℕ) + 2 + 2 / 3)) := by
  refine tendsto_barbanVehovFullLongDerivativeLcm_quadraticHorizon_div_log_four.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongDerivativeMoment_eq_lcm
    (Nat.one_lt_two.trans_le (two_le_pow_fortyNine_quadratic hN))
      (pow_fortyNine_le_pow_ninetyEight (by omega))]

/-- Full detector energy law at exact quadratic horizon `L=M²`. -/
theorem tendsto_levinsonCriticalDetectorFullLongEnergy_quadraticHorizon (r : ℝ) :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongEnergy
        (r / (49 * Real.log N)) (N ^ (98 : ℕ)) (N ^ (49 : ℕ))) atTop
      (𝓝 (1 + 2 * r * (-(2 + (1 / 2 : ℝ))) +
        r ^ (2 : ℕ) * ((2 : ℝ) ^ (2 : ℕ) + 2 + 2 / 3))) := by
  have hbase :=
    tendsto_levinsonCriticalDetectorFullLongBaseMoment_quadraticHorizon_div_log_sq_one
  have hcross :=
    tendsto_levinsonCriticalDetectorFullLongCrossMoment_quadraticHorizon_div_log_cube
  have hderiv :=
    tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_quadraticHorizon_div_log_four
  have hlim := (hbase.add (hcross.const_mul (2 * r))).add
    (hderiv.const_mul (r ^ (2 : ℕ)))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  rw [RHTower.levinsonCriticalDetectorFullLongEnergy_eq_momentQuadratic
    (r / (49 * Real.log N)) (N ^ (98 : ℕ))
      (Nat.one_lt_two.trans_le (two_le_pow_fortyNine_quadratic hN))]
  rw [show Real.log (((N ^ (49 : ℕ) : ℕ) : ℝ)) = 49 * Real.log (N : ℝ) by
    rw [show ((N ^ (49 : ℕ) : ℕ) : ℝ) = (N : ℝ) ^ (49 : ℕ) by norm_num,
      Real.log_pow]
    norm_num]
  field_simp [hlog]

/-- Reciprocal tuning has exact full mass `1/6` on the square-root boundary. -/
theorem tendsto_levinsonCriticalDetectorFullLongEnergy_quadraticHorizon_half :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongEnergy
        ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ (98 : ℕ)) (N ^ (49 : ℕ)))
      atTop (𝓝 (1 / 6 : ℝ)) := by
  convert tendsto_levinsonCriticalDetectorFullLongEnergy_quadraticHorizon (1 / 2 : ℝ)
    using 1
  norm_num

end
end RHTower.Sieve
