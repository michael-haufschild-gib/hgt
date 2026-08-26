import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedPolynomialMain
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovTwoFifthsScaleAsymptotics

/-!
# Omitted-head approximation errors at mollifier exponent `2/5`

At `L=N^5` and `M=N^2`, the exact omitted lcm moments differ from their max-weighted boundary
polynomials by normalized errors `3/N`, `24/N`, and `192/N`.  Thus only the three boundary
Selberg limits remain in the omitted arithmetic tail.
-/

namespace RHTower.Sieve

noncomputable section

attribute [local irreducible] barbanVehovOmittedLongBasePolynomialMain
  barbanVehovOmittedLongCrossPolynomialMain
  barbanVehovOmittedLongDerivativePolynomialMain

theorem abs_barbanVehovOmittedLongBaseLcm_twoFifths_div_log_sq_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongBaseLcm (N ^ 5) (N ^ 2) /
          (2 * Real.log N) ^ 2 -
        barbanVehovOmittedLongBasePolynomialMain (N ^ 2) /
          (2 * Real.log N) ^ 2| ≤
      3 / (N : ℝ) := by
  have hN0 : 0 < N := by omega
  have hM0 : 0 < N ^ 2 := pow_pos hN0 2
  have hM1 : 1 ≤ N ^ 2 := hM0
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hlogpow : Real.log ((N : ℝ) ^ 2) = 2 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have herr := abs_barbanVehovOmittedLongBaseLcm_sub_continuous_le
    hM1 (twoFifths_scale_condition hN)
  rw [barbanVehovOmittedLongBaseContinuous_eq_polynomialMain
    (pow_pos hN0 5) hM0] at herr
  have herr' :
      |barbanVehovOmittedLongBaseLcm (N ^ 5) (N ^ 2) -
          barbanVehovOmittedLongBasePolynomialMain (N ^ 2)| ≤
        (((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (3 / (N : ℝ) ^ 5)) := by
    simpa only [Nat.cast_pow, hlogpow] using herr
  have hscaled := abs_div_sub_div_le_of_abs_sub_le
    (sq_nonneg (2 * Real.log (N : ℝ))) herr'
  calc
    |barbanVehovOmittedLongBaseLcm (N ^ 5) (N ^ 2) /
          (2 * Real.log (N : ℝ)) ^ 2 -
        barbanVehovOmittedLongBasePolynomialMain (N ^ 2) /
          (2 * Real.log (N : ℝ)) ^ 2| ≤
      (((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (3 / (N : ℝ) ^ 5)) / (2 * Real.log (N : ℝ)) ^ 2 :=
      hscaled
    _ = 3 / (N : ℝ) := by
      field_simp [hlogN]

theorem abs_barbanVehovOmittedLongCrossLcm_twoFifths_div_log_cube_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongCrossLcm (N ^ 5) (N ^ 2) /
          (2 * Real.log N) ^ 3 -
        barbanVehovOmittedLongCrossPolynomialMain
            (5 / 2 * (2 * Real.log N)) (N ^ 2) /
          (2 * Real.log N) ^ 3| ≤
      24 / (N : ℝ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 2 := pow_pos hN0 2
  have hM1 : 1 ≤ N ^ 2 := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  have hlogpow : Real.log ((N : ℝ) ^ 2) = 2 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  let K := Real.log (N ^ 5 * N ^ 2 + 1 : ℕ)
  have hK : K ≤ 8 * Real.log N :=
    log_twoFifths_mul_add_one_le_eight_log (by omega : 2 ≤ N)
  have herr := abs_barbanVehovOmittedLongCrossLcm_sub_continuous_le
    hM1 (twoFifths_scale_condition hN)
  rw [barbanVehovOmittedLongCrossContinuous_eq_polynomialMain
    (pow_pos hN0 5) hM0,
    log_pow_five_eq_five_halves_log_pow_two] at herr
  have herr' :
      |barbanVehovOmittedLongCrossLcm (N ^ 5) (N ^ 2) -
          barbanVehovOmittedLongCrossPolynomialMain
            (5 / 2 * (2 * Real.log (N : ℝ))) (N ^ 2)| ≤
        ((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (6 * K / (N : ℝ) ^ 5) := by
    simpa [K, Nat.cast_pow, hlogpow] using herr
  have hden : 0 ≤ (2 * Real.log (N : ℝ)) ^ 3 := pow_nonneg (by positivity) 3
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovOmittedLongCrossLcm (N ^ 5) (N ^ 2) /
          (2 * Real.log (N : ℝ)) ^ 3 -
        barbanVehovOmittedLongCrossPolynomialMain
          (5 / 2 * (2 * Real.log (N : ℝ))) (N ^ 2) /
          (2 * Real.log (N : ℝ)) ^ 3| ≤
      (((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (6 * K / (N : ℝ) ^ 5)) /
        (2 * Real.log (N : ℝ)) ^ 3 :=
      hscaled
    _ = 3 * K / ((N : ℝ) * Real.log N) := by
      dsimp [K]
      field_simp [hlogN, hNR.ne']
      ring
    _ ≤ 24 / (N : ℝ) := by
      rw [div_le_iff₀ (mul_pos hNR hlogPos), div_eq_mul_inv]
      field_simp [hNR.ne']
      nlinarith

theorem abs_barbanVehovOmittedLongDerivativeLcm_twoFifths_div_log_four_sub_polynomial_le
    {N : ℕ} (hN : 8 ≤ N) :
    |barbanVehovOmittedLongDerivativeLcm (N ^ 5) (N ^ 2) /
          (2 * Real.log N) ^ 4 -
        barbanVehovOmittedLongDerivativePolynomialMain
            (5 / 2 * (2 * Real.log N)) (N ^ 2) /
          (2 * Real.log N) ^ 4| ≤
      192 / (N : ℝ) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hM0 : 0 < N ^ 2 := pow_pos hN0 2
  have hM1 : 1 ≤ N ^ 2 := hM0
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN : Real.log (N : ℝ) ≠ 0 := hlogPos.ne'
  have hlogpow : Real.log ((N : ℝ) ^ 2) = 2 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
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
  have herr := abs_barbanVehovOmittedLongDerivativeLcm_sub_continuous_le
    hM1 (twoFifths_scale_condition hN)
  rw [barbanVehovOmittedLongDerivativeContinuous_eq_polynomialMain
    (pow_pos hN0 5) hM0,
    log_pow_five_eq_five_halves_log_pow_two] at herr
  have herr' :
      |barbanVehovOmittedLongDerivativeLcm (N ^ 5) (N ^ 2) -
          barbanVehovOmittedLongDerivativePolynomialMain
            (5 / 2 * (2 * Real.log (N : ℝ))) (N ^ 2)| ≤
        ((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (12 * K ^ 2 / (N : ℝ) ^ 5) := by
    simpa [K, Nat.cast_pow, hlogpow] using herr
  have hden : 0 ≤ (2 * Real.log (N : ℝ)) ^ 4 := pow_nonneg (by positivity) 4
  have hscaled := abs_div_sub_div_le_of_abs_sub_le hden herr'
  calc
    |barbanVehovOmittedLongDerivativeLcm (N ^ 5) (N ^ 2) /
          (2 * Real.log (N : ℝ)) ^ 4 -
        barbanVehovOmittedLongDerivativePolynomialMain
          (5 / 2 * (2 * Real.log (N : ℝ))) (N ^ 2) /
          (2 * Real.log (N : ℝ)) ^ 4| ≤
      (((N : ℝ) ^ 2 * (2 * Real.log (N : ℝ))) ^ 2 *
          (12 * K ^ 2 / (N : ℝ) ^ 5)) /
        (2 * Real.log (N : ℝ)) ^ 4 :=
      hscaled
    _ = 3 * K ^ 2 / ((N : ℝ) * Real.log N ^ 2) := by
      field_simp [hlogN, hNR.ne']
      ring
    _ ≤ 192 / (N : ℝ) := by
      rw [div_le_iff₀ (mul_pos hNR (sq_pos_of_pos hlogPos))]
      rw [div_eq_mul_inv]
      field_simp [hNR.ne']
      nlinarith

end

end RHTower.Sieve
