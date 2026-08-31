import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSecondScale

/-!
# Algebra of the canonical Heath--Brown second scale

This module proves exact quarter-power and crossover inequalities needed to turn the selected
two-step recurrence into the published sparse mean-value exponents.
-/

namespace RHTower.Sieve

private theorem rpow_quarters_mul {x : ℝ} (hx : 0 < x) :
    x ^ (7 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (2 : ℕ) := by
  calc
    x ^ (7 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ ((7 / 4 : ℝ) + 1 / 4) :=
      (Real.rpow_add hx _ _).symm
    _ = x ^ (2 : ℝ) := by norm_num
    _ = x ^ (2 : ℕ) := Real.rpow_natCast x 2

private theorem rpow_threeQuarters_mul_quarter {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x := by
  calc
    x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ ((3 / 4 : ℝ) + 1 / 4) :=
      (Real.rpow_add hx _ _).symm
    _ = x ^ (1 : ℝ) := by norm_num
    _ = x := Real.rpow_one x

private theorem rpow_one_half_quarter {x : ℝ} (hx : 0 < x) :
    x * x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (7 / 4 : ℝ) := by
  calc
    x * x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) =
        x * (x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) := by ring
    _ = x * x ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hx]
      norm_num
    _ = x ^ (1 : ℝ) * x ^ (3 / 4 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + 3 / 4) := (Real.rpow_add hx _ _).symm
    _ = x ^ (7 / 4 : ℝ) := by norm_num

private theorem sqrt_eq_rpow_half (x : ℝ) :
    Real.sqrt x = x ^ (1 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]

theorem height_le_heathBrownSecondScale_cube
    {T R : ℝ} (hT : 0 ≤ T) :
    T ≤ (heathBrownSecondScale T R : ℝ) ^ 3 := by
  have hscale := heathBrown_rpow_oneThird_le_secondScale T R
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hT _) hscale
    (show 0 ≤ (3 : ℝ) by norm_num)
  calc
    T = (T ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := by
      rw [← Real.rpow_mul hT]
      norm_num
    _ ≤ ((heathBrownSecondScale T R : ℝ)) ^ (3 : ℝ) := hpow
    _ = ((heathBrownSecondScale T R : ℝ)) ^ (3 : ℕ) :=
      Real.rpow_natCast _ 3

theorem heathBrown_height_mul_card_sq_div_secondScale_le_mixed
    {T R : ℝ} (hT : 1 ≤ T) (hR : 0 < R) :
    T * R ^ 2 / (heathBrownSecondScale T R : ℝ) ≤
      R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
  have hK : 0 < (heathBrownSecondScale T R : ℝ) := by
    have : 1 ≤ heathBrownSecondScale T R :=
      one_le_heathBrownSecondScale hT
    exact_mod_cast Nat.zero_lt_of_lt this
  rw [div_le_iff₀ hK]
  have hlower := heathBrown_mul_rpow_oneFourth_le_secondScale T R
  calc
    T * R ^ 2 =
        (R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) *
          (R * T) ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow hR.le (zero_le_one.trans hT)]
      rw [mul_mul_mul_comm, rpow_quarters_mul hR,
        rpow_threeQuarters_mul_quarter (lt_of_lt_of_le zero_lt_one hT)]
      ring
    _ ≤ (R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) *
          (heathBrownSecondScale T R : ℝ) := by gcongr

theorem heathBrownSecondScale_mul_card_sqrt_le
    {T R : ℝ} (hT : 1 ≤ T) (hR : 0 < R) :
    (heathBrownSecondScale T R : ℝ) * R * Real.sqrt (T * R) ≤
      3 * (R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hR0 : 0 ≤ R := hR.le
  have hK := cast_heathBrownSecondScale_le_two_mul_oneThird_add_oneFourth hT hR0
  have hsqrt : Real.sqrt (T * R) = T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) := by
    rw [sqrt_eq_rpow_half, Real.mul_rpow hT0.le hR0]
  rw [hsqrt]
  have hmain :
      T ^ (1 / 3 : ℝ) * R * (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) ≤
        R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
    by_cases hcase : R ≤ T ^ (1 / 3 : ℝ)
    · have hsqrtR : R ^ (1 / 2 : ℝ) ≤ (T ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hR0 hcase (by norm_num)
      have hpowT :
          T ^ (1 / 3 : ℝ) * T ^ (1 / 2 : ℝ) *
              (T ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) = T := by
        rw [← Real.rpow_mul hT0.le]
        rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
        norm_num
      calc
        T ^ (1 / 3 : ℝ) * R * (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) =
            R * (T ^ (1 / 3 : ℝ) * T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) := by ring
        _ ≤ R * (T ^ (1 / 3 : ℝ) * T ^ (1 / 2 : ℝ) *
              (T ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ)) := by gcongr
        _ = R * T := by rw [hpowT]
        _ ≤ R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) :=
          le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hR.le _)
            (Real.rpow_nonneg hT0.le _))
    · have hcase' : T ^ (1 / 3 : ℝ) ≤ R := le_of_not_ge hcase
      have hquarter : (T ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) ≤
          R ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) hcase' (by norm_num)
      have hpowT :
          T ^ (1 / 3 : ℝ) * T ^ (1 / 2 : ℝ) =
            T ^ (3 / 4 : ℝ) * (T ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
        norm_num
      have hpowR : R * R ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ) =
          R ^ (7 / 4 : ℝ) := rpow_one_half_quarter hR
      calc
        T ^ (1 / 3 : ℝ) * R * (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) =
            (R * R ^ (1 / 2 : ℝ)) *
              (T ^ (3 / 4 : ℝ) * (T ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ)) := by
                rw [← hpowT]
                ring
        _ ≤ (R * R ^ (1 / 2 : ℝ)) *
              (T ^ (3 / 4 : ℝ) * R ^ (1 / 4 : ℝ)) := by gcongr
        _ = R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
          calc
            (R * R ^ (1 / 2 : ℝ)) *
                (T ^ (3 / 4 : ℝ) * R ^ (1 / 4 : ℝ)) =
              (R * R ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)) *
                T ^ (3 / 4 : ℝ) := by ring
            _ = R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by rw [hpowR]
        _ ≤ R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) :=
          le_add_of_nonneg_left (mul_nonneg hR.le hT0.le)
  have hquarter :
      (R * T) ^ (1 / 4 : ℝ) * R *
          (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) =
        R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow hR.le hT0.le]
    have hRpow : R ^ (1 / 4 : ℝ) * R * R ^ (1 / 2 : ℝ) = R ^ (7 / 4 : ℝ) := by
      calc
        R ^ (1 / 4 : ℝ) * R * R ^ (1 / 2 : ℝ) =
            R * R ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ) := by ring
        _ = R ^ (7 / 4 : ℝ) := rpow_one_half_quarter hR
    have hTpow : T ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) = T ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hT0]
      norm_num
    rw [show R ^ (1 / 4 : ℝ) * T ^ (1 / 4 : ℝ) * R *
      (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) =
      (R ^ (1 / 4 : ℝ) * R * R ^ (1 / 2 : ℝ)) *
        (T ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) by ring, hRpow, hTpow]
  calc
    (heathBrownSecondScale T R : ℝ) * R *
        (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) ≤
      (2 * T ^ (1 / 3 : ℝ) + (R * T) ^ (1 / 4 : ℝ)) * R *
        (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) := by gcongr
    _ = 2 * (T ^ (1 / 3 : ℝ) * R *
        (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ))) +
          (R * T) ^ (1 / 4 : ℝ) * R *
            (T ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) := by ring
    _ ≤ 2 * (R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) +
          R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by rw [hquarter]; gcongr
    _ ≤ 3 * (R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
      have hRT0 : 0 ≤ R * T := mul_nonneg hR.le hT0.le
      have hmixed0 : 0 ≤ R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) :=
        mul_nonneg (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg hT0.le _)
      linarith

/-- The rounded second scale is at most three times the height when `R ≤ T`. -/
theorem cast_heathBrownSecondScale_le_three_mul_height
    {T R : ℝ} (hT : 1 ≤ T) (hR : 0 ≤ R) (hRT : R ≤ T) :
    (heathBrownSecondScale T R : ℝ) ≤ 3 * T := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hthird : T ^ (1 / 3 : ℝ) ≤ T := by
    calc
      T ^ (1 / 3 : ℝ) ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = T := Real.rpow_one T
  have hmul : R * T ≤ T * T := mul_le_mul_of_nonneg_right hRT hT0
  have hquarter0 :
      (R * T) ^ (1 / 4 : ℝ) ≤ (T * T) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (mul_nonneg hR hT0) hmul (by norm_num)
  have hquarter : (R * T) ^ (1 / 4 : ℝ) ≤ T := by
    calc
      (R * T) ^ (1 / 4 : ℝ) ≤ (T * T) ^ (1 / 4 : ℝ) := hquarter0
      _ = T ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow hT0 hT0, ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hT)]
        norm_num
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = T := Real.rpow_one T
  have hscale := cast_heathBrownSecondScale_le_two_mul_oneThird_add_oneFourth hT hR
  linarith

/-- Divisor loss at the canonical second scale, with exponent quartered before squaring. -/
theorem heathBrownSquareDivisorScale_secondScale_sq_le
    {T R : ℝ} (hT : 1 ≤ T) (hR : 0 ≤ R) (hRT : R ≤ T)
    {N : ℕ} (hN : 1 ≤ N) {eta : ℝ} (heta : 0 < eta) :
    heathBrownSquareDivisorScale (heathBrownSecondScale T R) (eta / 4) ^ 2 ≤
      (divisorBoundConst (eta / 4) ^ 2 * (3 : ℝ) ^ eta) *
        ((N : ℝ) * T) ^ eta := by
  let K : ℕ := heathBrownSecondScale T R
  let C : ℝ := divisorBoundConst (eta / 4)
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  have hKup : (K : ℝ) ≤ 3 * T :=
    cast_heathBrownSecondScale_le_three_mul_height hT hR hRT
  have hKK : (((K * K : ℕ) : ℝ)) ≤ (3 * T) ^ 2 := by
    norm_num only [Nat.cast_mul]
    nlinarith [mul_self_le_mul_self hK0 hKup]
  have he : 0 ≤ eta / 4 := by positivity
  have hpow : (((K * K : ℕ) : ℝ)) ^ (eta / 4) ≤
      ((3 * T) ^ 2) ^ (eta / 4) :=
    Real.rpow_le_rpow (by positivity) hKK he
  have hC0 : 0 ≤ C := (divisorBoundConst_pos (by positivity : 0 < eta / 4)).le
  have hraw :
      heathBrownSquareDivisorScale K (eta / 4) ^ 2 ≤
        (C * (((3 * T) ^ 2) ^ (eta / 4))) ^ 2 := by
    rw [heathBrownSquareDivisorScale]
    dsimp only [C]
    have hsmall0 : 0 ≤ divisorBoundConst (eta / 4) *
        (((K * K : ℕ) : ℝ)) ^ (eta / 4) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hpow hC0
    exact (sq_le_sq₀ hsmall0 (hsmall0.trans hmul)).2 hmul
  have hpowid : (((3 * T) ^ 2) ^ (eta / 4)) ^ 2 = (3 * T) ^ eta := by
    have hx0 : 0 ≤ 3 * T := by positivity
    have hinner : ((3 * T) ^ 2) ^ (eta / 4) =
        (3 * T) ^ ((2 : ℝ) * (eta / 4)) := by
      calc
        ((3 * T) ^ (2 : ℕ)) ^ (eta / 4) =
            ((3 * T) ^ (2 : ℝ)) ^ (eta / 4) :=
          congrArg (fun x : ℝ => x ^ (eta / 4))
            (Real.rpow_natCast (3 * T) 2).symm
        _ = (3 * T) ^ ((2 : ℝ) * (eta / 4)) :=
          (Real.rpow_mul hx0 _ _).symm
    have houter : ((3 * T) ^ ((2 : ℝ) * (eta / 4))) ^ 2 =
        (3 * T) ^ (((2 : ℝ) * (eta / 4)) * 2) := by
      calc
        ((3 * T) ^ ((2 : ℝ) * (eta / 4))) ^ (2 : ℕ) =
            ((3 * T) ^ ((2 : ℝ) * (eta / 4))) ^ (2 : ℝ) :=
          (Real.rpow_natCast ((3 * T) ^ ((2 : ℝ) * (eta / 4))) 2).symm
        _ = (3 * T) ^ (((2 : ℝ) * (eta / 4)) * 2) :=
          (Real.rpow_mul hx0 _ _).symm
    calc
      (((3 * T) ^ 2) ^ (eta / 4)) ^ 2 =
          ((3 * T) ^ ((2 : ℝ) * (eta / 4))) ^ 2 := by rw [hinner]
      _ = (3 * T) ^ (((2 : ℝ) * (eta / 4)) * 2) := houter
      _ = (3 * T) ^ eta := by congr 1; ring
  have hNT : T ≤ (N : ℝ) * T := by
    have hNcast : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hTpow : T ^ eta ≤ ((N : ℝ) * T) ^ eta :=
    Real.rpow_le_rpow hT0.le hNT heta.le
  calc
    heathBrownSquareDivisorScale K (eta / 4) ^ 2 ≤
        (C * (((3 * T) ^ 2) ^ (eta / 4))) ^ 2 := hraw
    _ = C ^ 2 * (3 * T) ^ eta := by rw [mul_pow, hpowid]
    _ = (C ^ 2 * (3 : ℝ) ^ eta) * T ^ eta := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hT0.le]
      ring
    _ ≤ (C ^ 2 * (3 : ℝ) ^ eta) * ((N : ℝ) * T) ^ eta := by
      gcongr

end RHTower.Sieve
