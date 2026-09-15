import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedQuadraticHorizonError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedTunedEnergy

/-!
# Exact quadratic-horizon omitted energy

At `M=N^49` and `L=N^98=M^2`, retaining the omitted lower endpoint gives normalized
base, cross, and derivative errors of order `(1 + log N)/N^49`. The actual omitted
Levinson energy therefore retains its full limiting mass `7/48` exactly on the quadratic horizon.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

attribute [local irreducible] barbanVehovOmittedLongBasePolynomialMain
  barbanVehovOmittedLongCrossPolynomialMain
  barbanVehovOmittedLongDerivativePolynomialMain

theorem quadraticHorizon_scale_condition {N : ℕ} (hN : 2 ≤ N) :
    8 * N ^ 49 ≤ N ^ 98 := by
  have h8 : 8 ≤ N ^ 49 := by
    calc
      8 ≤ 2 ^ 49 := by norm_num
      _ ≤ N ^ 49 := Nat.pow_le_pow_left hN 49
  calc
    8 * N ^ 49 ≤ N ^ 49 * N ^ 49 := Nat.mul_le_mul_right _ h8
    _ = N ^ 98 := by ring

theorem log_quadraticHorizon_mul_add_one_le_oneHundredFortyEight_log
    {N : ℕ} (hN : 2 ≤ N) :
    Real.log (N ^ 98 * N ^ 49 + 1 : ℕ) ≤ 148 * Real.log N := by
  have hprodPos : 0 < N ^ 98 * N ^ 49 := by positivity
  have hprod1 : 1 ≤ N ^ 98 * N ^ 49 := hprodPos
  have hpow : N ^ 98 * N ^ 49 + 1 ≤ N ^ 148 := by
    calc
      N ^ 98 * N ^ 49 + 1 ≤
          N ^ 98 * N ^ 49 + N ^ 98 * N ^ 49 :=
        Nat.add_le_add_left hprod1 _
      _ = 2 * (N ^ 98 * N ^ 49) := by ring
      _ ≤ N * (N ^ 98 * N ^ 49) := Nat.mul_le_mul_right _ hN
      _ = N ^ 148 := by ring
  have hleftPos : (0 : ℝ) < ((N ^ 98 * N ^ 49 + 1 : ℕ) : ℝ) := by positivity
  have hpowR : ((N ^ 98 * N ^ 49 + 1 : ℕ) : ℝ) ≤ ((N ^ 148 : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log hleftPos hpowR
  rw [show ((N ^ 148 : ℕ) : ℝ) = (N : ℝ) ^ 148 by norm_num,
    Real.log_pow] at hlog
  norm_num at hlog
  norm_num [Nat.cast_pow]
  exact hlog

theorem abs_barbanVehovOmittedLongBaseLcm_quadraticHorizon_div_log_sq_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovOmittedLongBaseLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log N) ^ 2 -
        barbanVehovOmittedLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log N) ^ 2| ≤
      3 * (1 + 49 * Real.log N) / (N : ℝ) ^ 49 := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 49 := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ 49 := hM0
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hlogM : Real.log ((N : ℝ) ^ 49) = 49 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have herr := abs_barbanVehovOmittedLongBaseLcm_sub_continuous_le_quadratic
    hM1 (quadraticHorizon_scale_condition hN)
  rw [barbanVehovOmittedLongBaseContinuous_eq_polynomialMain
    (pow_pos hN0 98) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongBaseLcm (N ^ 98) (N ^ 49) -
          barbanVehovOmittedLongBasePolynomialMain (N ^ 49)| ≤
        ((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ)) ^ 2 *
          (1 + 49 * Real.log (N : ℝ))) * (3 / (N : ℝ) ^ 98) := by
    simpa only [Nat.cast_pow, hlogM] using herr
  have hscaled := abs_div_sub_div_le_of_abs_sub_le
    (sq_nonneg (49 * Real.log (N : ℝ))) herr'
  calc
    |barbanVehovOmittedLongBaseLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 2 -
        barbanVehovOmittedLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 2| ≤
      (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ)) ^ 2 *
          (1 + 49 * Real.log (N : ℝ))) * (3 / (N : ℝ) ^ 98)) /
        (49 * Real.log (N : ℝ)) ^ 2 := hscaled
    _ = 3 * (1 + 49 * Real.log N) / (N : ℝ) ^ 49 := by
      field_simp [hlogN, hNR.ne']

theorem abs_barbanVehovOmittedLongCrossLcm_quadraticHorizon_div_log_cube_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovOmittedLongCrossLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log N) ^ 3 -
        barbanVehovOmittedLongCrossPolynomialMain
            (98 * Real.log N) (N ^ 49) /
          (49 * Real.log N) ^ 3| ≤
      19 * (1 + 49 * Real.log N) / (N : ℝ) ^ 49 := by
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
  have hlogL : Real.log ((N : ℝ) ^ 98) = 98 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  let K := Real.log (N ^ 98 * N ^ 49 + 1 : ℕ)
  have hK : K ≤ 148 * Real.log N :=
    log_quadraticHorizon_mul_add_one_le_oneHundredFortyEight_log hN
  have hA0 : 0 ≤ 1 + 49 * Real.log N := by positivity
  have herr := abs_barbanVehovOmittedLongCrossLcm_sub_continuous_le_quadratic
    hM1 (quadraticHorizon_scale_condition hN)
  rw [barbanVehovOmittedLongCrossContinuous_eq_polynomialMain
    (pow_pos hN0 98) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongCrossLcm (N ^ 98) (N ^ 49) -
          barbanVehovOmittedLongCrossPolynomialMain
            (98 * Real.log (N : ℝ)) (N ^ 49)| ≤
        ((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ)) ^ 2 *
          (1 + 49 * Real.log (N : ℝ))) *
            (6 * K / (N : ℝ) ^ 98) := by
    simpa [K, Nat.cast_pow, hlogM, hlogL] using herr
  have hden : 0 ≤ (49 * Real.log (N : ℝ)) ^ 3 := pow_nonneg (by positivity) 3
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovOmittedLongCrossLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 3 -
        barbanVehovOmittedLongCrossPolynomialMain
          (98 * Real.log (N : ℝ)) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 3| ≤
      (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ)) ^ 2 *
          (1 + 49 * Real.log (N : ℝ))) *
            (6 * K / (N : ℝ) ^ 98)) /
        (49 * Real.log (N : ℝ)) ^ 3 := hscaled
    _ = 6 * K * (1 + 49 * Real.log N) /
        (49 * (N : ℝ) ^ 49 * Real.log N) := by
      field_simp [hlogN, hNR.ne']
    _ ≤ 19 * (1 + 49 * Real.log N) / (N : ℝ) ^ 49 := by
      rw [div_le_iff₀ (by positivity : 0 < 49 * (N : ℝ) ^ 49 * Real.log N)]
      rw [div_eq_mul_inv]
      field_simp [hNR.ne']
      have hKA := mul_le_mul_of_nonneg_right hK hA0
      nlinarith

theorem abs_barbanVehovOmittedLongDerivativeLcm_quadraticHorizon_div_log_four_sub_polynomial_le
    {N : ℕ} (hN : 2 ≤ N) :
    |barbanVehovOmittedLongDerivativeLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log N) ^ 4 -
        barbanVehovOmittedLongDerivativePolynomialMain
            (98 * Real.log N) (N ^ 49) /
          (49 * Real.log N) ^ 4| ≤
      110 * (1 + 49 * Real.log N) / (N : ℝ) ^ 49 := by
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
  have hlogL : Real.log ((N : ℝ) ^ 98) = 98 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  let K := Real.log (N ^ 98 * N ^ 49 + 1 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg
      (by exact_mod_cast (by omega : 1 ≤ N ^ 98 * N ^ 49 + 1))
  have hK : K ≤ 148 * Real.log N :=
    log_quadraticHorizon_mul_add_one_le_oneHundredFortyEight_log hN
  have hKsq : K ^ 2 ≤ 21904 * Real.log N ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hK hK0
    have h2 := mul_le_mul_of_nonneg_right hK
      (by positivity : 0 ≤ 148 * Real.log N)
    nlinarith
  have hA0 : 0 ≤ 1 + 49 * Real.log N := by positivity
  have herr := abs_barbanVehovOmittedLongDerivativeLcm_sub_continuous_le_quadratic
    hM1 (quadraticHorizon_scale_condition hN)
  rw [barbanVehovOmittedLongDerivativeContinuous_eq_polynomialMain
    (pow_pos hN0 98) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongDerivativeLcm (N ^ 98) (N ^ 49) -
          barbanVehovOmittedLongDerivativePolynomialMain
            (98 * Real.log (N : ℝ)) (N ^ 49)| ≤
        ((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ)) ^ 2 *
          (1 + 49 * Real.log (N : ℝ))) *
            (12 * K ^ 2 / (N : ℝ) ^ 98) := by
    simpa [K, Nat.cast_pow, hlogM, hlogL] using herr
  have hden : 0 ≤ (49 * Real.log (N : ℝ)) ^ 4 := pow_nonneg (by positivity) 4
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovOmittedLongDerivativeLcm (N ^ 98) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 4 -
        barbanVehovOmittedLongDerivativePolynomialMain
          (98 * Real.log (N : ℝ)) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 4| ≤
      (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ)) ^ 2 *
          (1 + 49 * Real.log (N : ℝ))) *
            (12 * K ^ 2 / (N : ℝ) ^ 98)) /
        (49 * Real.log (N : ℝ)) ^ 4 := hscaled
    _ = 12 * K ^ 2 * (1 + 49 * Real.log N) /
        (49 ^ 2 * (N : ℝ) ^ 49 * Real.log N ^ 2) := by
      field_simp [hlogN, hNR.ne']
    _ ≤ 110 * (1 + 49 * Real.log N) / (N : ℝ) ^ 49 := by
      rw [div_le_iff₀
        (by positivity : 0 < (49 : ℝ) ^ 2 * (N : ℝ) ^ 49 * Real.log N ^ 2)]
      rw [div_eq_mul_inv]
      field_simp [hNR.ne']
      have hKA := mul_le_mul_of_nonneg_right hKsq hA0
      nlinarith

private theorem tendsto_nat_pow_fortyNine_atTop_quadraticHorizon :
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

/-- At exact quadratic-horizon tuning, omitted polynomial energy has mass `7/48`. -/
theorem tendsto_barbanVehovOmittedLongEnergyPolynomialMain_quadraticHorizon_half :
    Tendsto (fun N : ℕ =>
      barbanVehovOmittedLongEnergyPolynomialMain
        ((1 / 2 : ℝ) / (49 * Real.log N))
        (98 * Real.log N) (N ^ 49))
      atTop (𝓝 ((7 / 12 : ℝ) * (1 / 2 : ℝ) ^ 2)) := by
  have hrem :=
    tendsto_selbergOriginalTunedMinLogRemainder_div_log_four_seven_twelfths.comp
      tendsto_nat_pow_fortyNine_atTop_quadraticHorizon
  have hscaled := hrem.const_mul ((1 / 2 : ℝ) ^ 2)
  have hscaled' : Tendsto (fun N : ℕ =>
      (1 / 2 : ℝ) ^ 2 *
        (selbergOriginalTunedMinLogRemainder (N ^ 49) /
          Real.log (((N ^ 49 : ℕ) : ℝ)) ^ 4))
      atTop (𝓝 ((7 / 12 : ℝ) * (1 / 2 : ℝ) ^ 2)) := by
    simpa only [Function.comp_apply, mul_comm] using hscaled
  refine hscaled'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hM : 0 < N ^ 49 := pow_pos (by omega) 49
  have htune :
      ((1 / 2 : ℝ) / (49 * Real.log N)) * (98 * Real.log N) = 1 := by
    field_simp [hlog]
    norm_num
  rw [barbanVehovOmittedLongEnergyPolynomialMain_eq_tunedRemainder hM htune]
  rw [show (((N ^ 49 : ℕ) : ℝ)) = (N : ℝ) ^ 49 by norm_num,
    Real.log_pow]
  field_simp [hlog]
  ring

/-- Explicit energy error constant at exact quadratic-horizon scale. -/
def barbanVehovOmittedQuadraticHorizonEnergyErrorConstant (r : ℝ) : ℝ :=
  3 + 38 * |r| + 110 * r ^ 2

theorem abs_levinsonCriticalDetectorOmittedLongEnergy_quadraticHorizon_sub_polynomialMain_le
    (r : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    |RHTower.levinsonCriticalDetectorOmittedLongEnergy
          (r / (49 * Real.log N)) (N ^ 98) (N ^ 49) -
        barbanVehovOmittedLongEnergyPolynomialMain
          (r / (49 * Real.log N)) (98 * Real.log N) (N ^ 49)| ≤
      barbanVehovOmittedQuadraticHorizonEnergyErrorConstant r *
        ((1 + 49 * Real.log N) / (N : ℝ) ^ 49) := by
  have hN0 : 0 < N := by omega
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hM : 1 < N ^ 49 := by
    have hNpow : N ≤ N ^ 49 := by
      calc
        N ≤ N * N ^ 48 := Nat.le_mul_of_pos_right N (pow_pos hN0 48)
        _ = N ^ 49 := by ring
    exact (by omega : 1 < N).trans_le hNpow
  have hML : N ^ 49 ≤ N ^ 98 := by
    calc
      N ^ 49 ≤ N ^ 49 * N ^ 49 :=
        Nat.le_mul_of_pos_right _ (pow_pos hN0 49)
      _ = N ^ 98 := by ring
  have hlogM : Real.log (((N ^ 49 : ℕ) : ℝ)) = 49 * Real.log N := by
    rw [show (((N ^ 49 : ℕ) : ℝ)) = (N : ℝ) ^ 49 by norm_num,
      Real.log_pow]
    norm_num
  rw [RHTower.levinsonCriticalDetectorOmittedLongEnergy_eq_momentQuadratic
    (r / (49 * Real.log N)) (N ^ 98) hM,
    levinsonCriticalDetectorOmittedLongBaseMoment_eq_lcm hM hML,
    levinsonCriticalDetectorOmittedLongCrossMoment_eq_lcm hM hML,
    levinsonCriticalDetectorOmittedLongDerivativeMoment_eq_lcm hM hML,
    barbanVehovOmittedLongEnergyPolynomialMain, hlogM]
  have hbase :=
    abs_barbanVehovOmittedLongBaseLcm_quadraticHorizon_div_log_sq_sub_polynomial_le hN
  have hcross :=
    abs_barbanVehovOmittedLongCrossLcm_quadraticHorizon_div_log_cube_sub_polynomial_le hN
  have hderiv :=
    abs_barbanVehovOmittedLongDerivativeLcm_quadraticHorizon_div_log_four_sub_polynomial_le hN
  let F := (1 + 49 * Real.log N) / (N : ℝ) ^ 49
  let eB :=
    barbanVehovOmittedLongBaseLcm (N ^ 98) (N ^ 49) /
        (49 * Real.log N) ^ 2 -
      barbanVehovOmittedLongBasePolynomialMain (N ^ 49) /
        (49 * Real.log N) ^ 2
  let eC :=
    barbanVehovOmittedLongCrossLcm (N ^ 98) (N ^ 49) /
        (49 * Real.log N) ^ 3 -
      barbanVehovOmittedLongCrossPolynomialMain (98 * Real.log N) (N ^ 49) /
        (49 * Real.log N) ^ 3
  let eD :=
    barbanVehovOmittedLongDerivativeLcm (N ^ 98) (N ^ 49) /
        (49 * Real.log N) ^ 4 -
      barbanVehovOmittedLongDerivativePolynomialMain (98 * Real.log N) (N ^ 49) /
        (49 * Real.log N) ^ 4
  have hbaseF : |eB| ≤ 3 * F := by
    dsimp only [eB, F]
    simpa only [mul_div_assoc] using hbase
  have hcrossF : |eC| ≤ 19 * F := by
    dsimp only [eC, F]
    simpa only [mul_div_assoc] using hcross
  have hderivF : |eD| ≤ 110 * F := by
    dsimp only [eD, F]
    simpa only [mul_div_assoc] using hderiv
  have heq :
      (barbanVehovOmittedLongBaseLcm (N ^ 98) (N ^ 49) +
            2 * (r / (49 * Real.log N)) *
              barbanVehovOmittedLongCrossLcm (N ^ 98) (N ^ 49) +
            (r / (49 * Real.log N)) ^ 2 *
              barbanVehovOmittedLongDerivativeLcm (N ^ 98) (N ^ 49)) /
          (49 * Real.log N) ^ 2 -
        (barbanVehovOmittedLongBasePolynomialMain (N ^ 49) +
            2 * (r / (49 * Real.log N)) *
              barbanVehovOmittedLongCrossPolynomialMain
                (98 * Real.log N) (N ^ 49) +
            (r / (49 * Real.log N)) ^ 2 *
              barbanVehovOmittedLongDerivativePolynomialMain
                (98 * Real.log N) (N ^ 49)) /
          (49 * Real.log N) ^ 2 =
        eB + 2 * r * eC + r ^ 2 * eD := by
    dsimp only [eB, eC, eD]
    field_simp [hlog]
    ring
  rw [heq]
  calc
    |eB + 2 * r * eC + r ^ 2 * eD| ≤
        |eB| + |2 * r * eC| + |r ^ 2 * eD| := by
      exact (abs_add_le (eB + 2 * r * eC) (r ^ 2 * eD)).trans
        (add_le_add (abs_add_le eB (2 * r * eC)) (le_refl _))
    _ = |eB| + 2 * |r| * |eC| + r ^ 2 * |eD| := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, sq_abs]
      norm_num
    _ ≤ 3 * F + 2 * |r| * (19 * F) + r ^ 2 * (110 * F) := by
      exact add_le_add
        (add_le_add hbaseF
          (mul_le_mul_of_nonneg_left hcrossF
            (mul_nonneg (by norm_num) (abs_nonneg r))))
        (mul_le_mul_of_nonneg_left hderivF (sq_nonneg r))
    _ = barbanVehovOmittedQuadraticHorizonEnergyErrorConstant r * F := by
      rw [barbanVehovOmittedQuadraticHorizonEnergyErrorConstant]
      ring

private theorem tendsto_quadraticHorizon_error_factor_zero :
    Tendsto (fun N : ℕ =>
      (1 + 49 * Real.log N) / (N : ℝ) ^ 49) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum : Tendsto (fun N : ℕ =>
      1 / (N : ℝ) + 49 * (Real.log N / (N : ℝ))) atTop (𝓝 0) := by
    simpa using hone.add (hlog.const_mul 49)
  have hinv48 : Tendsto (fun N : ℕ => (1 / (N : ℝ)) ^ 48) atTop (𝓝 0) := by
    simpa using hone.pow 48
  have hmul := hsum.mul hinv48
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hNR]

/-- Actual omitted energy retains exact mass `7/48` at `L=M²`. -/
theorem tendsto_levinsonCriticalDetectorOmittedLongEnergy_quadraticHorizon_half :
    Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorOmittedLongEnergy
        ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ 98) (N ^ 49))
      atTop (𝓝 ((7 / 12 : ℝ) * (1 / 2 : ℝ) ^ 2)) := by
  let P : ℕ → ℝ := fun N =>
    barbanVehovOmittedLongEnergyPolynomialMain
      ((1 / 2 : ℝ) / (49 * Real.log N))
      (98 * Real.log N) (N ^ 49)
  have hP : Tendsto P atTop (𝓝 ((7 / 12 : ℝ) * (1 / 2 : ℝ) ^ 2)) :=
    tendsto_barbanVehovOmittedLongEnergyPolynomialMain_quadraticHorizon_half
  have hbound : Tendsto (fun N : ℕ =>
      barbanVehovOmittedQuadraticHorizonEnergyErrorConstant (1 / 2 : ℝ) *
        ((1 + 49 * Real.log N) / (N : ℝ) ^ 49)) atTop (𝓝 0) := by
    simpa using tendsto_quadraticHorizon_error_factor_zero.const_mul
      (barbanVehovOmittedQuadraticHorizonEnergyErrorConstant (1 / 2 : ℝ))
  have habs : Tendsto (fun N : ℕ =>
      |RHTower.levinsonCriticalDetectorOmittedLongEnergy
          ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ 98) (N ^ 49) - P N|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop 2] with N hN
    simpa only [P] using
      abs_levinsonCriticalDetectorOmittedLongEnergy_quadraticHorizon_sub_polynomialMain_le
        (1 / 2 : ℝ) hN
  have herr : Tendsto (fun N : ℕ =>
      RHTower.levinsonCriticalDetectorOmittedLongEnergy
          ((1 / 2 : ℝ) / (49 * Real.log N)) (N ^ 98) (N ^ 49) - P N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, norm_zero] using habs
  simpa only [P, zero_add] using (herr.add hP).congr'
    (Eventually.of_forall fun N => by ring)

end
end RHTower.Sieve

