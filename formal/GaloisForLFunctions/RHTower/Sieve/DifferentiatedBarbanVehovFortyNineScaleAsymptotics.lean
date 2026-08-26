import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedFortyNineError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovGeneralScaleMain
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorFullLongMomentExpansion

/-!
# Full differentiated Barban--Vehov asymptotics at exponent `49/100`

The exact natural-power scale `L=N^100`, `M=N^49` is strictly below the square-root barrier and
matches the explicit Levinson scalar certificate.  Existing general-scale continuous reductions
and Selberg polynomial limits yield the three exact full long-moment limits and their detector
energy quadratic; normalized discretization errors decay as `N⁻²`.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

theorem abs_barbanVehovFullLongBaseLcm_fortyNine_div_log_sq_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovFullLongBaseLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 2 -
        barbanVehovLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log N) ^ 2| ≤
      3 / (N : ℝ) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hM0 : 0 < N ^ 49 := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ 49 := hM0
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hlogM : Real.log ((N : ℝ) ^ 49) = 49 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have herr := abs_barbanVehovFullLongBaseLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovFullLongBaseContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0
      (log_pow_hundred_eq_hundred_fortyNine_log_pow_fortyNine N)] at herr
  have herr' :
      |barbanVehovFullLongBaseLcm (N ^ 100) (N ^ 49) -
          barbanVehovLongBasePolynomialMain (N ^ 49)| ≤
        (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (3 / (N : ℝ) ^ 100)) := by
    simpa only [Nat.cast_pow, hlogM] using herr
  have hscaled := abs_div_sub_div_le_of_abs_sub_le
    (sq_nonneg (49 * Real.log (N : ℝ))) herr'
  calc
    |barbanVehovFullLongBaseLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 2 -
        barbanVehovLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 2| ≤
      (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (3 / (N : ℝ) ^ 100)) / (49 * Real.log (N : ℝ)) ^ 2 :=
      hscaled
    _ = 3 / (N : ℝ) ^ 2 := by
      field_simp [hlogN]

theorem abs_barbanVehovFullLongCrossLcm_fortyNine_div_log_cube_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovFullLongCrossLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 3 -
        barbanVehovLongCrossPolynomialMain (100 / 49) (N ^ 49) /
          (49 * Real.log N) ^ 3| ≤
      19 / (N : ℝ) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 49 := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ 49 := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  have hlogM : Real.log ((N : ℝ) ^ 49) = 49 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  let K := Real.log (N ^ 100 * N ^ 49 + 1 : ℕ)
  have hK : K ≤ 150 * Real.log N :=
    log_fortyNine_mul_add_one_le_oneHundredFifty_log (by omega : 2 ≤ N)
  have herr := abs_barbanVehovFullLongCrossLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovFullLongCrossContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0
      (log_pow_hundred_eq_hundred_fortyNine_log_pow_fortyNine N)] at herr
  have herr' :
      |barbanVehovFullLongCrossLcm (N ^ 100) (N ^ 49) -
          barbanVehovLongCrossPolynomialMain (100 / 49) (N ^ 49)| ≤
        ((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (6 * K / (N : ℝ) ^ 100) := by
    simpa [K, Nat.cast_pow, hlogM] using herr
  have hden : 0 ≤ (49 * Real.log (N : ℝ)) ^ 3 := pow_nonneg (by positivity) 3
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovFullLongCrossLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 3 -
        barbanVehovLongCrossPolynomialMain (100 / 49) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 3| ≤
      (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (6 * K / (N : ℝ) ^ 100)) /
        (49 * Real.log (N : ℝ)) ^ 3 := hscaled
    _ = 6 * K / (49 * (N : ℝ) ^ 2 * Real.log N) := by
      field_simp [hlogN, hNR.ne']
    _ ≤ 19 / (N : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity : 0 < 49 * (N : ℝ) ^ 2 * Real.log N)]
      rw [div_eq_mul_inv]
      field_simp [hNR.ne']
      nlinarith

theorem abs_barbanVehovFullLongDerivativeLcm_fortyNine_div_log_four_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovFullLongDerivativeLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 4 -
        barbanVehovLongDerivativePolynomialMain (100 / 49) (N ^ 49) /
          (49 * Real.log N) ^ 4| ≤
      113 / (N : ℝ) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 49 := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ 49 := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  have hlogM : Real.log ((N : ℝ) ^ 49) = 49 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  let K := Real.log (N ^ 100 * N ^ 49 + 1 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg
      (by exact_mod_cast (by omega : 1 ≤ N ^ 100 * N ^ 49 + 1))
  have hK : K ≤ 150 * Real.log N :=
    log_fortyNine_mul_add_one_le_oneHundredFifty_log (by omega : 2 ≤ N)
  have hKsq : K ^ 2 ≤ 22500 * Real.log N ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hK hK0
    have h2 := mul_le_mul_of_nonneg_right hK
      (by positivity : 0 ≤ 150 * Real.log N)
    nlinarith
  have herr := abs_barbanVehovFullLongDerivativeLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovFullLongDerivativeContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0
      (log_pow_hundred_eq_hundred_fortyNine_log_pow_fortyNine N)] at herr
  have herr' :
      |barbanVehovFullLongDerivativeLcm (N ^ 100) (N ^ 49) -
          barbanVehovLongDerivativePolynomialMain (100 / 49) (N ^ 49)| ≤
        ((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (12 * K ^ 2 / (N : ℝ) ^ 100) := by
    simpa [K, Nat.cast_pow, hlogM] using herr
  have hden : 0 ≤ (49 * Real.log (N : ℝ)) ^ 4 := pow_nonneg (by positivity) 4
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovFullLongDerivativeLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 4 -
        barbanVehovLongDerivativePolynomialMain (100 / 49) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 4| ≤
      (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (12 * K ^ 2 / (N : ℝ) ^ 100)) /
        (49 * Real.log (N : ℝ)) ^ 4 := hscaled
    _ = 12 * K ^ 2 /
        (49 ^ 2 * (N : ℝ) ^ 2 * Real.log N ^ 2) := by
      field_simp [hlogN, hNR.ne']
    _ ≤ 113 / (N : ℝ) ^ 2 := by
      rw [div_le_iff₀
        (by positivity : 0 < (49 : ℝ) ^ 2 * (N : ℝ) ^ 2 * Real.log N ^ 2)]
      rw [div_eq_mul_inv]
      field_simp [hNR.ne']
      nlinarith

private theorem tendsto_nat_pow_fortyNine_atTop :
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

private theorem tendsto_const_div_nat_sq (c : ℝ) :
    Tendsto (fun N : ℕ => c / (N : ℝ) ^ 2) atTop (nhds 0) := by
  have hc : Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hmul := hc.mul hone
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hNR]

theorem tendsto_barbanVehovFullLongBaseLcm_fortyNine_div_log_sq_one :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongBaseLcm (N ^ 100) (N ^ 49) /
        (49 * Real.log N) ^ 2) atTop (nhds 1) := by
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongBaseLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 2 -
        barbanVehovLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log N) ^ 2|) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat_sq 3)
    filter_upwards [eventually_ge_atTop 8] with N hN
    exact abs_barbanVehovFullLongBaseLcm_fortyNine_div_log_sq_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongBaseLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 2 -
        barbanVehovLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log N) ^ 2) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain := tendsto_barbanVehovLongBasePolynomialMain_div_log_sq_one.comp
    tendsto_nat_pow_fortyNine_atTop
  have hmain' : Tendsto (fun N : ℕ =>
      barbanVehovLongBasePolynomialMain (N ^ 49) /
        (49 * Real.log N) ^ 2) atTop (nhds 1) := by
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [Function.comp_apply]
    rw [show ((N ^ 49 : ℕ) : ℝ) = (N : ℝ) ^ 49 by norm_num,
      Real.log_pow]
    norm_num
  simpa only [sub_add_cancel, zero_add] using hdiff.add hmain'

theorem tendsto_barbanVehovFullLongCrossLcm_fortyNine_div_log_cube :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongCrossLcm (N ^ 100) (N ^ 49) /
        (49 * Real.log N) ^ 3) atTop
      (nhds (-((100 / 49 : ℝ) + 1 / 2))) := by
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongCrossLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 3 -
        barbanVehovLongCrossPolynomialMain (100 / 49) (N ^ 49) /
          (49 * Real.log N) ^ 3|) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat_sq 19)
    filter_upwards [eventually_ge_atTop 8] with N hN
    exact abs_barbanVehovFullLongCrossLcm_fortyNine_div_log_cube_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongCrossLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 3 -
        barbanVehovLongCrossPolynomialMain (100 / 49) (N ^ 49) /
          (49 * Real.log N) ^ 3) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain :=
    (tendsto_barbanVehovLongCrossPolynomialMain_div_log_cube (100 / 49)).comp
      tendsto_nat_pow_fortyNine_atTop
  have hmain' : Tendsto (fun N : ℕ =>
      barbanVehovLongCrossPolynomialMain (100 / 49) (N ^ 49) /
        (49 * Real.log N) ^ 3) atTop
      (nhds (-((100 / 49 : ℝ) + 1 / 2))) := by
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [Function.comp_apply]
    rw [show ((N ^ 49 : ℕ) : ℝ) = (N : ℝ) ^ 49 by norm_num,
      Real.log_pow]
    norm_num
  simpa only [sub_add_cancel, zero_add] using hdiff.add hmain'

theorem tendsto_barbanVehovFullLongDerivativeLcm_fortyNine_div_log_four :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongDerivativeLcm (N ^ 100) (N ^ 49) /
        (49 * Real.log N) ^ 4) atTop
      (nhds ((100 / 49 : ℝ) ^ 2 + (100 / 49 : ℝ) + 2 / 3)) := by
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongDerivativeLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 4 -
        barbanVehovLongDerivativePolynomialMain (100 / 49) (N ^ 49) /
          (49 * Real.log N) ^ 4|) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat_sq 113)
    filter_upwards [eventually_ge_atTop 8] with N hN
    exact abs_barbanVehovFullLongDerivativeLcm_fortyNine_div_log_four_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongDerivativeLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 4 -
        barbanVehovLongDerivativePolynomialMain (100 / 49) (N ^ 49) /
          (49 * Real.log N) ^ 4) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain :=
    (tendsto_barbanVehovLongDerivativePolynomialMain_div_log_four (100 / 49)).comp
      tendsto_nat_pow_fortyNine_atTop
  have hmain' : Tendsto (fun N : ℕ =>
      barbanVehovLongDerivativePolynomialMain (100 / 49) (N ^ 49) /
        (49 * Real.log N) ^ 4) atTop
      (nhds ((100 / 49 : ℝ) ^ 2 + (100 / 49 : ℝ) + 2 / 3)) := by
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [Function.comp_apply]
    rw [show ((N ^ 49 : ℕ) : ℝ) = (N : ℝ) ^ 49 by norm_num,
      Real.log_pow]
    norm_num
  simpa only [sub_add_cancel, zero_add] using hdiff.add hmain'

private theorem pow_fortyNine_le_pow_hundred {N : ℕ} (hN : 0 < N) :
    N ^ 49 ≤ N ^ 100 := by
  calc
    N ^ 49 ≤ N ^ 49 * N ^ 51 :=
      Nat.le_mul_of_pos_right _ (pow_pos hN 51)
    _ = N ^ 100 := by ring

private theorem two_le_pow_fortyNine {N : ℕ} (hN : 2 ≤ N) :
    2 ≤ N ^ 49 := by
  refine hN.trans ?_
  calc
    N ≤ N * N ^ 48 := Nat.le_mul_of_pos_right N (pow_pos (by omega) 48)
    _ = N ^ 49 := by ring

theorem tendsto_levinsonCriticalDetectorFullLongBaseMoment_fortyNine_div_log_sq_one :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongBaseMoment (N ^ 100) (N ^ 49) /
        (49 * Real.log N) ^ 2) atTop (nhds 1) := by
  refine tendsto_barbanVehovFullLongBaseLcm_fortyNine_div_log_sq_one.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongBaseMoment_eq_lcm
    (Nat.one_lt_two.trans_le (two_le_pow_fortyNine hN))
      (pow_fortyNine_le_pow_hundred (by omega))]

theorem tendsto_levinsonCriticalDetectorFullLongCrossMoment_fortyNine_div_log_cube :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongCrossMoment (N ^ 100) (N ^ 49) /
        (49 * Real.log N) ^ 3) atTop
      (nhds (-((100 / 49 : ℝ) + 1 / 2))) := by
  refine tendsto_barbanVehovFullLongCrossLcm_fortyNine_div_log_cube.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongCrossMoment_eq_lcm
    (Nat.one_lt_two.trans_le (two_le_pow_fortyNine hN))
      (pow_fortyNine_le_pow_hundred (by omega))]

theorem tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_fortyNine_div_log_four :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongDerivativeMoment (N ^ 100) (N ^ 49) /
        (49 * Real.log N) ^ 4) atTop
      (nhds ((100 / 49 : ℝ) ^ 2 + (100 / 49 : ℝ) + 2 / 3)) := by
  refine tendsto_barbanVehovFullLongDerivativeLcm_fortyNine_div_log_four.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongDerivativeMoment_eq_lcm
    (Nat.one_lt_two.trans_le (two_le_pow_fortyNine hN))
      (pow_fortyNine_le_pow_hundred (by omega))]

theorem tendsto_levinsonCriticalDetectorFullLongEnergy_fortyNine (r : ℝ) :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongEnergy
        (r / (49 * Real.log N)) (N ^ 100) (N ^ 49)) atTop
      (nhds (1 + 2 * r * (-((100 / 49 : ℝ) + 1 / 2)) +
        r ^ 2 * ((100 / 49 : ℝ) ^ 2 + (100 / 49 : ℝ) + 2 / 3))) := by
  have hbase :=
    tendsto_levinsonCriticalDetectorFullLongBaseMoment_fortyNine_div_log_sq_one
  have hcross :=
    tendsto_levinsonCriticalDetectorFullLongCrossMoment_fortyNine_div_log_cube
  have hderiv :=
    tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_fortyNine_div_log_four
  have hlim := (hbase.add (hcross.const_mul (2 * r))).add
    (hderiv.const_mul (r ^ 2))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [RHTower.levinsonCriticalDetectorFullLongEnergy_eq_momentQuadratic
    (r / (49 * Real.log N)) (N ^ 100)
      (Nat.one_lt_two.trans_le (two_le_pow_fortyNine hN))]
  rw [show Real.log (((N ^ 49 : ℕ) : ℝ)) = 49 * Real.log (N : ℝ) by
    rw [show ((N ^ 49 : ℕ) : ℝ) = (N : ℝ) ^ 49 by norm_num,
      Real.log_pow]
    norm_num]
  field_simp [hlog]

end

end RHTower.Sieve
