import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovGeneralScaleMain
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorFullLongMomentExpansion

/-!
# Differentiated Barban--Vehov asymptotics at mollifier exponent `2/5`

Take height `L = N^5` and mollifier length `M = N^2`.  The general long-scale bounds give explicit
normalized errors `3/N`, `24/N`, and `192/N`.  Consequently the exact lcm moments and actual
differentiated detector moments converge to `1`, `-3`, and `113/12`, and the detector energy tends
to `1 - 6r + (113/12)r²`.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

private theorem twoFifths_scale_condition {N : ℕ} (hN : 8 ≤ N) :
    8 * (N ^ 2) ^ 2 ≤ N ^ 5 := by
  calc
    8 * (N ^ 2) ^ 2 = 8 * N ^ 4 := by ring
    _ ≤ N * N ^ 4 := Nat.mul_le_mul_right _ hN
    _ = N ^ 5 := by ring

private theorem log_pow_five_eq_five_halves_log_pow_two
    (N : ℕ) :
    Real.log (((N ^ 5 : ℕ) : ℝ)) =
      (5 / 2 : ℝ) * Real.log (((N ^ 2 : ℕ) : ℝ)) := by
  norm_num [Nat.cast_pow, Real.log_pow]
  ring

theorem log_twoFifths_mul_add_one_le_eight_log
    {N : ℕ} (hN : 2 ≤ N) :
    Real.log (N ^ 5 * N ^ 2 + 1 : ℕ) ≤ 8 * Real.log N := by
  have hprodPos : 0 < N ^ 5 * N ^ 2 := by positivity
  have hprod1 : 1 ≤ N ^ 5 * N ^ 2 := hprodPos
  have hpow : N ^ 5 * N ^ 2 + 1 ≤ N ^ 8 := by
    calc
      N ^ 5 * N ^ 2 + 1 ≤ N ^ 5 * N ^ 2 + N ^ 5 * N ^ 2 :=
        Nat.add_le_add_left hprod1 _
      _ = 2 * (N ^ 5 * N ^ 2) := by ring
      _ ≤ N * (N ^ 5 * N ^ 2) := Nat.mul_le_mul_right _ hN
      _ = N ^ 8 := by ring
  have hleftPos : (0 : ℝ) < ((N ^ 5 * N ^ 2 + 1 : ℕ) : ℝ) := by positivity
  have hpowR : ((N ^ 5 * N ^ 2 + 1 : ℕ) : ℝ) ≤ ((N ^ 8 : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log hleftPos hpowR
  rw [show ((N ^ 8 : ℕ) : ℝ) = (N : ℝ) ^ 8 by norm_num, Real.log_pow] at hlog
  norm_num at hlog
  norm_num [Nat.cast_pow]
  exact hlog

theorem abs_barbanVehovFullLongBaseLcm_twoFifths_div_log_sq_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovFullLongBaseLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 2 -
        barbanVehovLongBasePolynomialMain (N ^ 2) /
          Real.log (N ^ 2) ^ 2| ≤
      3 / (N : ℝ) := by
  have hN0 : 0 < N := by omega
  have hM0 : 0 < N ^ 2 := pow_pos hN0 2
  have hM1 : 1 ≤ N ^ 2 := hM0
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hlog : Real.log ((N ^ 2 : ℕ) : ℝ) ≠ 0 := by
    rw [show ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) ^ 2 by norm_num, Real.log_pow]
    exact mul_ne_zero (by norm_num) hlogN
  have herr := abs_barbanVehovFullLongBaseLcm_sub_continuous_le
    hM1 (twoFifths_scale_condition hN)
  rw [barbanVehovFullLongBaseContinuous_eq_polynomialMain
    (pow_pos hN0 5) hM0 (log_pow_five_eq_five_halves_log_pow_two N)] at herr
  norm_num [Nat.cast_pow] at herr ⊢
  rw [← sub_div, abs_div, abs_of_nonneg (sq_nonneg (2 * Real.log (N : ℝ)))]
  calc
    |barbanVehovFullLongBaseLcm (N ^ 5) (N ^ 2) -
        barbanVehovLongBasePolynomialMain (N ^ 2)| / (2 * Real.log (N : ℝ)) ^ 2 ≤
      (((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (3 / (N : ℝ) ^ 5)) / (2 * Real.log (N : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_right herr (sq_nonneg _)
    _ = 3 / (N : ℝ) := by
      field_simp [hlog, hlogN]

theorem abs_barbanVehovFullLongCrossLcm_twoFifths_div_log_cube_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovFullLongCrossLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 3 -
        barbanVehovLongCrossPolynomialMain (5 / 2) (N ^ 2) /
          Real.log (N ^ 2) ^ 3| ≤
      24 / (N : ℝ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 2 := pow_pos hN0 2
  have hM1 : 1 ≤ N ^ 2 := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  let K := Real.log (N ^ 5 * N ^ 2 + 1 : ℕ)
  have hK : K ≤ 8 * Real.log N :=
    log_twoFifths_mul_add_one_le_eight_log (by omega : 2 ≤ N)
  have herr := abs_barbanVehovFullLongCrossLcm_sub_continuous_le
    hM1 (twoFifths_scale_condition hN)
  rw [barbanVehovFullLongCrossContinuous_eq_polynomialMain
    (pow_pos hN0 5) hM0 (log_pow_five_eq_five_halves_log_pow_two N)] at herr
  have herr' :
      |barbanVehovFullLongCrossLcm (N ^ 5) (N ^ 2) -
          barbanVehovLongCrossPolynomialMain (5 / 2) (N ^ 2)| ≤
        ((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (6 * K / (N : ℝ) ^ 5) := by
    simpa [K, Nat.cast_pow] using herr
  norm_num [Nat.cast_pow] at ⊢
  rw [← sub_div, abs_div,
    abs_of_nonneg (pow_nonneg (mul_nonneg (by norm_num) hlogPos.le) 3)]
  calc
    |barbanVehovFullLongCrossLcm (N ^ 5) (N ^ 2) -
        barbanVehovLongCrossPolynomialMain (5 / 2) (N ^ 2)| /
          (2 * Real.log (N : ℝ)) ^ 3 ≤
      (((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (6 * K / (N : ℝ) ^ 5)) /
        (2 * Real.log (N : ℝ)) ^ 3 :=
      div_le_div_of_nonneg_right herr' (pow_nonneg (by positivity) 3)
    _ = 3 * K / ((N : ℝ) * Real.log N) := by
      dsimp [K]
      field_simp [hlogN, hNR.ne']
      ring
    _ ≤ 24 / (N : ℝ) := by
      rw [div_le_iff₀ (mul_pos hNR hlogPos), div_eq_mul_inv]
      field_simp [hNR.ne']
      nlinarith

theorem abs_barbanVehovFullLongDerivativeLcm_twoFifths_div_log_four_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovFullLongDerivativeLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 4 -
        barbanVehovLongDerivativePolynomialMain (5 / 2) (N ^ 2) /
          Real.log (N ^ 2) ^ 4| ≤
      192 / (N : ℝ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 2 := pow_pos hN0 2
  have hM1 : 1 ≤ N ^ 2 := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  let K := Real.log (N ^ 5 * N ^ 2 + 1 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N ^ 5 * N ^ 2 + 1))
  have hK : K ≤ 8 * Real.log N :=
    log_twoFifths_mul_add_one_le_eight_log (by omega : 2 ≤ N)
  have hKsq : K ^ 2 ≤ 64 * Real.log N ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hK hK0
    have h2 := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 8 * Real.log N)
    nlinarith
  have herr := abs_barbanVehovFullLongDerivativeLcm_sub_continuous_le
    hM1 (twoFifths_scale_condition hN)
  rw [barbanVehovFullLongDerivativeContinuous_eq_polynomialMain
    (pow_pos hN0 5) hM0 (log_pow_five_eq_five_halves_log_pow_two N)] at herr
  have herr' :
      |barbanVehovFullLongDerivativeLcm (N ^ 5) (N ^ 2) -
          barbanVehovLongDerivativePolynomialMain (5 / 2) (N ^ 2)| ≤
        ((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (12 * K ^ 2 / (N : ℝ) ^ 5) := by
    simpa [K, Nat.cast_pow] using herr
  norm_num [Nat.cast_pow] at ⊢
  rw [← sub_div, abs_div,
    abs_of_nonneg (pow_nonneg (mul_nonneg (by norm_num) hlogPos.le) 4)]
  calc
    |barbanVehovFullLongDerivativeLcm (N ^ 5) (N ^ 2) -
        barbanVehovLongDerivativePolynomialMain (5 / 2) (N ^ 2)| /
          (2 * Real.log (N : ℝ)) ^ 4 ≤
      (((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (12 * K ^ 2 / (N : ℝ) ^ 5)) /
        (2 * Real.log (N : ℝ)) ^ 4 :=
      div_le_div_of_nonneg_right herr' (pow_nonneg (by positivity) 4)
    _ = 3 * K ^ 2 / ((N : ℝ) * Real.log N ^ 2) := by
      field_simp [hlogN, hNR.ne']
      ring
    _ ≤ 192 / (N : ℝ) := by
      rw [div_le_iff₀ (mul_pos hNR (sq_pos_of_pos hlogPos))]
      rw [div_eq_mul_inv]
      field_simp [hNR.ne']
      nlinarith

private theorem tendsto_nat_square_atTop :
    Tendsto (fun N : ℕ => N ^ 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (max b 1)] with N hN
  have hbN : b ≤ N := (Nat.le_max_left b 1).trans hN
  have hN1 : 1 ≤ N := (Nat.le_max_right b 1).trans hN
  exact hbN.trans (by simpa [pow_two] using Nat.le_mul_of_pos_right N hN1)

private theorem tendsto_const_div_nat (c : ℝ) :
    Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem tendsto_barbanVehovFullLongBaseLcm_twoFifths_div_log_sq_one :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongBaseLcm (N ^ 5) (N ^ 2) /
        Real.log (N ^ 2) ^ 2) atTop (nhds 1) := by
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongBaseLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 2 -
        barbanVehovLongBasePolynomialMain (N ^ 2) /
          Real.log (N ^ 2) ^ 2|) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat 3)
    filter_upwards [eventually_ge_atTop 8] with N hN
    exact abs_barbanVehovFullLongBaseLcm_twoFifths_div_log_sq_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongBaseLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 2 -
        barbanVehovLongBasePolynomialMain (N ^ 2) /
          Real.log (N ^ 2) ^ 2) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain := tendsto_barbanVehovLongBasePolynomialMain_div_log_sq_one.comp
    tendsto_nat_square_atTop
  simpa only [Function.comp_apply, Nat.cast_pow, sub_add_cancel, zero_add] using
    hdiff.add hmain

theorem tendsto_barbanVehovFullLongCrossLcm_twoFifths_div_log_cube :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongCrossLcm (N ^ 5) (N ^ 2) /
        Real.log (N ^ 2) ^ 3) atTop (nhds (-3)) := by
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongCrossLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 3 -
        barbanVehovLongCrossPolynomialMain (5 / 2) (N ^ 2) /
          Real.log (N ^ 2) ^ 3|) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat 24)
    filter_upwards [eventually_ge_atTop 8] with N hN
    exact abs_barbanVehovFullLongCrossLcm_twoFifths_div_log_cube_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongCrossLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 3 -
        barbanVehovLongCrossPolynomialMain (5 / 2) (N ^ 2) /
          Real.log (N ^ 2) ^ 3) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain := (tendsto_barbanVehovLongCrossPolynomialMain_div_log_cube (5 / 2)).comp
    tendsto_nat_square_atTop
  have hresult := hdiff.add hmain
  norm_num at hresult ⊢
  simpa only [Function.comp_apply, Nat.cast_pow, sub_add_cancel, zero_add] using hresult

theorem tendsto_barbanVehovFullLongDerivativeLcm_twoFifths_div_log_four :
    Tendsto (fun N : ℕ =>
      barbanVehovFullLongDerivativeLcm (N ^ 5) (N ^ 2) /
        Real.log (N ^ 2) ^ 4) atTop (nhds (113 / 12)) := by
  have habs : Tendsto (fun N : ℕ =>
      |barbanVehovFullLongDerivativeLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 4 -
        barbanVehovLongDerivativePolynomialMain (5 / 2) (N ^ 2) /
          Real.log (N ^ 2) ^ 4|) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ?_ (tendsto_const_div_nat 192)
    filter_upwards [eventually_ge_atTop 8] with N hN
    exact abs_barbanVehovFullLongDerivativeLcm_twoFifths_div_log_four_sub_polynomial_le hN
  have hdiff : Tendsto (fun N : ℕ =>
      barbanVehovFullLongDerivativeLcm (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 4 -
        barbanVehovLongDerivativePolynomialMain (5 / 2) (N ^ 2) /
          Real.log (N ^ 2) ^ 4) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hmain := (tendsto_barbanVehovLongDerivativePolynomialMain_div_log_four (5 / 2)).comp
    tendsto_nat_square_atTop
  have hresult := hdiff.add hmain
  norm_num at hresult ⊢
  simpa only [Function.comp_apply, Nat.cast_pow, sub_add_cancel, zero_add] using hresult

private theorem square_le_pow_five {N : ℕ} (hN : 0 < N) :
    N ^ 2 ≤ N ^ 5 := by
  calc
    N ^ 2 ≤ N ^ 2 * N ^ 3 := Nat.le_mul_of_pos_right _ (pow_pos hN 3)
    _ = N ^ 5 := by ring

theorem tendsto_levinsonCriticalDetectorFullLongBaseMoment_twoFifths_div_log_sq_one :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongBaseMoment (N ^ 5) (N ^ 2) /
        Real.log (N ^ 2) ^ 2) atTop (nhds 1) := by
  refine tendsto_barbanVehovFullLongBaseLcm_twoFifths_div_log_sq_one.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongBaseMoment_eq_lcm
    (by nlinarith) (square_le_pow_five (by omega))]

theorem tendsto_levinsonCriticalDetectorFullLongCrossMoment_twoFifths_div_log_cube :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongCrossMoment (N ^ 5) (N ^ 2) /
        Real.log (N ^ 2) ^ 3) atTop (nhds (-3)) := by
  refine tendsto_barbanVehovFullLongCrossLcm_twoFifths_div_log_cube.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongCrossMoment_eq_lcm
    (by nlinarith) (square_le_pow_five (by omega))]

theorem tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_twoFifths_div_log_four :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongDerivativeMoment (N ^ 5) (N ^ 2) /
        Real.log (N ^ 2) ^ 4) atTop (nhds (113 / 12)) := by
  refine tendsto_barbanVehovFullLongDerivativeLcm_twoFifths_div_log_four.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [levinsonCriticalDetectorFullLongDerivativeMoment_eq_lcm
    (by nlinarith) (square_le_pow_five (by omega))]

theorem tendsto_levinsonCriticalDetectorFullLongEnergy_twoFifths (r : ℝ) :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongEnergy
        (r / Real.log (N ^ 2)) (N ^ 5) (N ^ 2)) atTop
      (nhds (1 - 6 * r + (113 / 12 : ℝ) * r ^ 2)) := by
  have hbase := tendsto_levinsonCriticalDetectorFullLongBaseMoment_twoFifths_div_log_sq_one
  have hcross := tendsto_levinsonCriticalDetectorFullLongCrossMoment_twoFifths_div_log_cube
  have hderiv := tendsto_levinsonCriticalDetectorFullLongDerivativeMoment_twoFifths_div_log_four
  have hlim := (hbase.add (hcross.const_mul (2 * r))).add
    (hderiv.const_mul (r ^ 2))
  have hfun : Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorFullLongEnergy
        (r / Real.log (N ^ 2)) (N ^ 5) (N ^ 2)) atTop
      (nhds (1 + 2 * r * (-3) + r ^ 2 * (113 / 12))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (((N ^ 2 : ℕ) : ℝ)) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by nlinarith : 1 < N ^ 2))).ne'
    have hlogR : Real.log ((N : ℝ) ^ 2) ≠ 0 := by
      rw [Real.log_pow]
      exact mul_ne_zero (by norm_num)
        (Real.log_pos (by exact_mod_cast hN)).ne'
    change RHTower.levinsonCriticalDetectorFullLongBaseMoment (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 2 +
        2 * r * (RHTower.levinsonCriticalDetectorFullLongCrossMoment (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 3) +
        r ^ 2 * (RHTower.levinsonCriticalDetectorFullLongDerivativeMoment (N ^ 5) (N ^ 2) /
          Real.log (N ^ 2) ^ 4) = _
    rw [RHTower.levinsonCriticalDetectorFullLongEnergy_eq_momentQuadratic
      (r / Real.log (N ^ 2)) (N ^ 5) (by nlinarith)]
    norm_num [Nat.cast_pow] at hlog ⊢
    field_simp [hlog, hlogR]
  convert hfun using 1
  ring

end

end RHTower.Sieve
