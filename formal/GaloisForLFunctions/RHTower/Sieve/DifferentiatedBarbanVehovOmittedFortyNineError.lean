import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedPolynomialMain

/-!
# Omitted-head approximation errors at mollifier exponent `49/100`

Take `L=N^(100 : ℕ)` and `M=N^(49 : ℕ)`.  This exact natural-power scale matches the explicit scalar
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
    8 * (N ^ (49 : ℕ)) ^ (2 : ℕ) ≤ N ^ (100 : ℕ) := by
  calc
    8 * (N ^ (49 : ℕ)) ^ (2 : ℕ) = 8 * N ^ (98 : ℕ) := by ring
    _ ≤ N * N ^ (98 : ℕ) := Nat.mul_le_mul_right _ hN
    _ = N ^ (99 : ℕ) := by ring
    _ ≤ N ^ (99 : ℕ) * N := Nat.le_mul_of_pos_right _ (by omega)
    _ = N ^ (100 : ℕ) := by ring

theorem log_pow_hundred_eq_hundred_fortyNine_log_pow_fortyNine
    (N : ℕ) :
    Real.log (((N ^ (100 : ℕ) : ℕ) : ℝ)) =
      (100 / 49 : ℝ) * Real.log (((N ^ (49 : ℕ) : ℕ) : ℝ)) := by
  norm_num [Nat.cast_pow, Real.log_pow]
  ring

theorem log_fortyNine_mul_add_one_le_oneHundredFifty_log
    {N : ℕ} (hN : 2 ≤ N) :
    Real.log (N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ) ≤ 150 * Real.log N := by
  have hprodPos : 0 < N ^ (100 : ℕ) * N ^ (49 : ℕ) := by positivity
  have hprod1 : 1 ≤ N ^ (100 : ℕ) * N ^ (49 : ℕ) := hprodPos
  have hpow : N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1 ≤ N ^ (150 : ℕ) := by
    calc
      N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1 ≤
          N ^ (100 : ℕ) * N ^ (49 : ℕ) + N ^ (100 : ℕ) * N ^ (49 : ℕ) :=
        Nat.add_le_add_left hprod1 _
      _ = 2 * (N ^ (100 : ℕ) * N ^ (49 : ℕ)) := by ring
      _ ≤ N * (N ^ (100 : ℕ) * N ^ (49 : ℕ)) := Nat.mul_le_mul_right _ hN
      _ = N ^ (150 : ℕ) := by ring
  have hleftPos : (0 : ℝ) < ((N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have hpowR : ((N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ) : ℝ) ≤ ((N ^ (150 : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log hleftPos hpowR
  rw [show ((N ^ (150 : ℕ) : ℕ) : ℝ) = (N : ℝ) ^ (150 : ℕ) by norm_num,
    Real.log_pow] at hlog
  norm_num at hlog
  norm_num [Nat.cast_pow]
  exact hlog

theorem abs_barbanVehovOmittedLongBaseLcm_fortyNine_div_log_sq_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongBaseLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (2 : ℕ) -
        barbanVehovOmittedLongBasePolynomialMain (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (2 : ℕ)| ≤
      3 / (N : ℝ) ^ (2 : ℕ) := by
  have hN0 : 0 < N := by omega
  have hM0 : 0 < N ^ (49 : ℕ) := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ (49 : ℕ) := hM0
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hlogpow : Real.log ((N : ℝ) ^ (49 : ℕ)) = 49 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have herr := abs_barbanVehovOmittedLongBaseLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovOmittedLongBaseContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongBaseLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) -
          barbanVehovOmittedLongBasePolynomialMain (N ^ (49 : ℕ))| ≤
        (((N : ℝ) ^ (49 : ℕ) * (49 * Real.log (N : ℝ))) ^ (2 : ℕ) *
          (3 / (N : ℝ) ^ (100 : ℕ))) := by
    simpa only [Nat.cast_pow, hlogpow] using herr
  have hscaled := abs_div_sub_div_le_of_abs_sub_le
    (sq_nonneg (49 * Real.log (N : ℝ))) herr'
  calc
    |barbanVehovOmittedLongBaseLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log (N : ℝ)) ^ (2 : ℕ) -
        barbanVehovOmittedLongBasePolynomialMain (N ^ (49 : ℕ)) /
          (49 * Real.log (N : ℝ)) ^ (2 : ℕ)| ≤
      (((N : ℝ) ^ (49 : ℕ) * (49 * Real.log (N : ℝ))) ^ (2 : ℕ) *
          (3 / (N : ℝ) ^ (100 : ℕ))) / (49 * Real.log (N : ℝ)) ^ (2 : ℕ) :=
      hscaled
    _ = 3 / (N : ℝ) ^ (2 : ℕ) := by
      field_simp [hlogN]

theorem abs_barbanVehovOmittedLongCrossLcm_fortyNine_div_log_cube_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongCrossLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ) -
        barbanVehovOmittedLongCrossPolynomialMain
            (100 * Real.log N) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (3 : ℕ)| ≤
      19 / (N : ℝ) ^ (2 : ℕ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ (49 : ℕ) := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ (49 : ℕ) := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  have hlogM : Real.log ((N : ℝ) ^ (49 : ℕ)) = 49 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have hlogL : Real.log ((N : ℝ) ^ (100 : ℕ)) = 100 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  let K := Real.log (N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ)
  have hK : K ≤ 150 * Real.log N :=
    log_fortyNine_mul_add_one_le_oneHundredFifty_log (by omega : 2 ≤ N)
  have herr := abs_barbanVehovOmittedLongCrossLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovOmittedLongCrossContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongCrossLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) -
          barbanVehovOmittedLongCrossPolynomialMain
            (100 * Real.log (N : ℝ)) (N ^ (49 : ℕ))| ≤
        ((N : ℝ) ^ (49 : ℕ) * (49 * Real.log (N : ℝ))) ^ (2 : ℕ) *
          (6 * K / (N : ℝ) ^ (100 : ℕ)) := by
    simpa [K, Nat.cast_pow, hlogM, hlogL] using herr
  have hden : 0 ≤ (49 * Real.log (N : ℝ)) ^ (3 : ℕ) := pow_nonneg (by positivity) 3
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovOmittedLongCrossLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log (N : ℝ)) ^ (3 : ℕ) -
        barbanVehovOmittedLongCrossPolynomialMain
          (100 * Real.log (N : ℝ)) (N ^ (49 : ℕ)) /
          (49 * Real.log (N : ℝ)) ^ (3 : ℕ)| ≤
      (((N : ℝ) ^ (49 : ℕ) * (49 * Real.log (N : ℝ))) ^ (2 : ℕ) *
          (6 * K / (N : ℝ) ^ (100 : ℕ))) /
        (49 * Real.log (N : ℝ)) ^ (3 : ℕ) := hscaled
    _ = 6 * K / (49 * (N : ℝ) ^ (2 : ℕ) * Real.log N) := by
      field_simp [hlogN, hNR.ne']
    _ ≤ 19 / (N : ℝ) ^ (2 : ℕ) := by
      rw [div_le_iff₀ (by positivity : 0 < 49 * (N : ℝ) ^ (2 : ℕ) * Real.log N)]
      rw [div_eq_mul_inv]
      field_simp [hNR.ne']
      nlinarith

theorem abs_barbanVehovOmittedLongDerivativeLcm_fortyNine_div_log_four_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongDerivativeLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ) -
        barbanVehovOmittedLongDerivativePolynomialMain
            (100 * Real.log N) (N ^ (49 : ℕ)) /
          (49 * Real.log N) ^ (4 : ℕ)| ≤
      113 / (N : ℝ) ^ (2 : ℕ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ (49 : ℕ) := pow_pos hN0 49
  have hM1 : 1 ≤ N ^ (49 : ℕ) := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  have hlogM : Real.log ((N : ℝ) ^ (49 : ℕ)) = 49 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have hlogL : Real.log ((N : ℝ) ^ (100 : ℕ)) = 100 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  let K := Real.log (N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1 : ℕ)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg
      (by exact_mod_cast (by omega : 1 ≤ N ^ (100 : ℕ) * N ^ (49 : ℕ) + 1))
  have hK : K ≤ 150 * Real.log N :=
    log_fortyNine_mul_add_one_le_oneHundredFifty_log (by omega : 2 ≤ N)
  have hKsq : K ^ (2 : ℕ) ≤ 22500 * Real.log N ^ (2 : ℕ) := by
    have h1 := mul_le_mul_of_nonneg_left hK hK0
    have h2 := mul_le_mul_of_nonneg_right hK
      (by positivity : 0 ≤ 150 * Real.log N)
    nlinarith
  have herr := abs_barbanVehovOmittedLongDerivativeLcm_sub_continuous_le
    hM1 (fortyNine_scale_condition hN)
  rw [barbanVehovOmittedLongDerivativeContinuous_eq_polynomialMain
    (pow_pos hN0 100) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongDerivativeLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) -
          barbanVehovOmittedLongDerivativePolynomialMain
            (100 * Real.log (N : ℝ)) (N ^ (49 : ℕ))| ≤
        ((N : ℝ) ^ (49 : ℕ) * (49 * Real.log (N : ℝ))) ^ (2 : ℕ) *
          (12 * K ^ (2 : ℕ) / (N : ℝ) ^ (100 : ℕ)) := by
    simpa [K, Nat.cast_pow, hlogM, hlogL] using herr
  have hden : 0 ≤ (49 * Real.log (N : ℝ)) ^ (4 : ℕ) := pow_nonneg (by positivity) 4
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovOmittedLongDerivativeLcm (N ^ (100 : ℕ)) (N ^ (49 : ℕ)) /
          (49 * Real.log (N : ℝ)) ^ (4 : ℕ) -
        barbanVehovOmittedLongDerivativePolynomialMain
          (100 * Real.log (N : ℝ)) (N ^ (49 : ℕ)) /
          (49 * Real.log (N : ℝ)) ^ (4 : ℕ)| ≤
      (((N : ℝ) ^ (49 : ℕ) * (49 * Real.log (N : ℝ))) ^ (2 : ℕ) *
          (12 * K ^ (2 : ℕ) / (N : ℝ) ^ (100 : ℕ))) /
        (49 * Real.log (N : ℝ)) ^ (4 : ℕ) := hscaled
    _ = 12 * K ^ (2 : ℕ) /
        (49 ^ (2 : ℕ) * (N : ℝ) ^ (2 : ℕ) * Real.log N ^ (2 : ℕ)) := by
      field_simp [hlogN, hNR.ne']
    _ ≤ 113 / (N : ℝ) ^ (2 : ℕ) := by
      rw [div_le_iff₀
        (by positivity : 0 < (49 : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (2 : ℕ) * Real.log N ^ (2 : ℕ))]
      rw [div_eq_mul_inv]
      field_simp [hNR.ne']
      nlinarith

end

end RHTower.Sieve
