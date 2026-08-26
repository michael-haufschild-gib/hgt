import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedPolynomialMain

/-!
# Omitted-head approximation errors at mollifier exponent `49/100`

Take `L=N^100` and `M=N^49`.  This exact natural-power scale matches the explicit scalar
certificate `θ=49/100`, while `M²/L=N⁻²` leaves a strict long-fibre saving.  The normalized exact
omitted lcm moments differ from their boundary polynomials by at most `3/N²`, `19/N²`, and
`113/N²`.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

attribute [local irreducible] barbanVehovOmittedLongBasePolynomialMain
  barbanVehovOmittedLongCrossPolynomialMain
  barbanVehovOmittedLongDerivativePolynomialMain

theorem fortyNine_scale_condition {N : ℕ} (hN : 8 ≤ N) :
    8 * (N ^ 49) ^ 2 ≤ N ^ 100 := by
  calc
    8 * (N ^ 49) ^ 2 = 8 * N ^ 98 := by ring
    _ ≤ N * N ^ 98 := Nat.mul_le_mul_right _ hN
    _ = N ^ 99 := by ring
    _ ≤ N ^ 99 * N := Nat.le_mul_of_pos_right _ (by omega)
    _ = N ^ 100 := by ring

theorem log_pow_hundred_eq_hundred_fortyNine_log_pow_fortyNine
    (N : ℕ) :
    Real.log (((N ^ 100 : ℕ) : ℝ)) =
      (100 / 49 : ℝ) * Real.log (((N ^ 49 : ℕ) : ℝ)) := by
  norm_num [Nat.cast_pow, Real.log_pow]
  ring

theorem log_fortyNine_mul_add_one_le_oneHundredFifty_log
    {N : ℕ} (hN : 2 ≤ N) :
    Real.log (N ^ 100 * N ^ 49 + 1 : ℕ) ≤ 150 * Real.log N := by
  have hprodPos : 0 < N ^ 100 * N ^ 49 := by positivity
  have hprod1 : 1 ≤ N ^ 100 * N ^ 49 := hprodPos
  have hpow : N ^ 100 * N ^ 49 + 1 ≤ N ^ 150 := by
    calc
      N ^ 100 * N ^ 49 + 1 ≤
          N ^ 100 * N ^ 49 + N ^ 100 * N ^ 49 :=
        Nat.add_le_add_left hprod1 _
      _ = 2 * (N ^ 100 * N ^ 49) := by ring
      _ ≤ N * (N ^ 100 * N ^ 49) := Nat.mul_le_mul_right _ hN
      _ = N ^ 150 := by ring
  have hleftPos : (0 : ℝ) < ((N ^ 100 * N ^ 49 + 1 : ℕ) : ℝ) := by positivity
  have hpowR : ((N ^ 100 * N ^ 49 + 1 : ℕ) : ℝ) ≤ ((N ^ 150 : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log hleftPos hpowR
  rw [show ((N ^ 150 : ℕ) : ℝ) = (N : ℝ) ^ 150 by norm_num,
    Real.log_pow] at hlog
  norm_num at hlog
  norm_num [Nat.cast_pow]
  exact hlog

theorem abs_barbanVehovOmittedLongBaseLcm_fortyNine_div_log_sq_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongBaseLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 2 -
        barbanVehovOmittedLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log N) ^ 2| ≤
      3 / (N : ℝ) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hM0 : 0 < N ^ 49 := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ 49 := hM0
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hlogpow : Real.log ((N : ℝ) ^ 49) = 49 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have herr := abs_barbanVehovOmittedLongBaseLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovOmittedLongBaseContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongBaseLcm (N ^ 100) (N ^ 49) -
          barbanVehovOmittedLongBasePolynomialMain (N ^ 49)| ≤
        (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (3 / (N : ℝ) ^ 100)) := by
    simpa only [Nat.cast_pow, hlogpow] using herr
  have hscaled := abs_div_sub_div_le_of_abs_sub_le
    (sq_nonneg (49 * Real.log (N : ℝ))) herr'
  calc
    |barbanVehovOmittedLongBaseLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 2 -
        barbanVehovOmittedLongBasePolynomialMain (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 2| ≤
      (((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (3 / (N : ℝ) ^ 100)) / (49 * Real.log (N : ℝ)) ^ 2 :=
      hscaled
    _ = 3 / (N : ℝ) ^ 2 := by
      field_simp [hlogN]

theorem abs_barbanVehovOmittedLongCrossLcm_fortyNine_div_log_cube_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongCrossLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 3 -
        barbanVehovOmittedLongCrossPolynomialMain
            (100 * Real.log N) (N ^ 49) /
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
  have hlogL : Real.log ((N : ℝ) ^ 100) = 100 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  let K := Real.log (N ^ 100 * N ^ 49 + 1 : ℕ)
  have hK : K ≤ 150 * Real.log N :=
    log_fortyNine_mul_add_one_le_oneHundredFifty_log (by omega : 2 ≤ N)
  have herr := abs_barbanVehovOmittedLongCrossLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovOmittedLongCrossContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongCrossLcm (N ^ 100) (N ^ 49) -
          barbanVehovOmittedLongCrossPolynomialMain
            (100 * Real.log (N : ℝ)) (N ^ 49)| ≤
        ((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (6 * K / (N : ℝ) ^ 100) := by
    simpa [K, Nat.cast_pow, hlogM, hlogL] using herr
  have hden : 0 ≤ (49 * Real.log (N : ℝ)) ^ 3 := pow_nonneg (by positivity) 3
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovOmittedLongCrossLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 3 -
        barbanVehovOmittedLongCrossPolynomialMain
          (100 * Real.log (N : ℝ)) (N ^ 49) /
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

theorem abs_barbanVehovOmittedLongDerivativeLcm_fortyNine_div_log_four_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongDerivativeLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log N) ^ 4 -
        barbanVehovOmittedLongDerivativePolynomialMain
            (100 * Real.log N) (N ^ 49) /
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
  have hlogL : Real.log ((N : ℝ) ^ 100) = 100 * Real.log (N : ℝ) := by
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
  have herr := abs_barbanVehovOmittedLongDerivativeLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovOmittedLongDerivativeContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongDerivativeLcm (N ^ 100) (N ^ 49) -
          barbanVehovOmittedLongDerivativePolynomialMain
            (100 * Real.log (N : ℝ)) (N ^ 49)| ≤
        ((N : ℝ) ^ 49 * (49 * Real.log (N : ℝ))) ^ 2 *
          (12 * K ^ 2 / (N : ℝ) ^ 100) := by
    simpa [K, Nat.cast_pow, hlogM, hlogL] using herr
  have hden : 0 ≤ (49 * Real.log (N : ℝ)) ^ 4 := pow_nonneg (by positivity) 4
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovOmittedLongDerivativeLcm (N ^ 100) (N ^ 49) /
          (49 * Real.log (N : ℝ)) ^ 4 -
        barbanVehovOmittedLongDerivativePolynomialMain
          (100 * Real.log (N : ℝ)) (N ^ 49) /
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

end

end RHTower.Sieve
