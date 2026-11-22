import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.FarRangeScales

/-! Exponential height and short-difference scales in the low-conductor range. -/

noncomputable section

namespace QH.PrimeProgressions

/-- Put `U = exp(a √log y)`, use height `U⁸` and difference fraction `U⁻⁴`. The conductor fits
inside `U`, the zero-free gap pays `U⁻¹⁶`, and the ramp power error pays `U⁻⁸`. -/
theorem near_range_scales (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C) :
    ∃ a D : ℝ, 0 < a ∧ 0 < D ∧ ∀ M y : ℝ, 8 ≤ M → 2 ≤ y →
      Real.log M ≤ a * Real.sqrt (Real.log y) →
      let U := Real.exp (a * Real.sqrt (Real.log y))
      8 ≤ U ∧ U ^ 4 ≤ y ∧
      (M * U ^ 8) ^ C * y ^ (-(κ / 2)) ≤ (U ^ 8)⁻¹ ∧
      y ^ (-(κ / 2)) ≤ (U ^ 8)⁻¹ ∧
      Real.log (2 * y) ≤ D * U ∧
      Real.log (2 * y) * Real.log (M * U ^ 8) ^ 2 ≤ D * U ∧
      Real.log (M * (U ^ 8 + 3)) ≤ D * U ∧
      Real.exp (-(cZ * Real.log y / Real.log (M * (U ^ 8 + 3)))) ≤ (U ^ 16)⁻¹ := by
  let a := min (1 / 64 : ℝ) (min (cZ / 128) (κ / (2 * (9 * C + 8))))
  have ha : 0 < a := lt_min (by norm_num) (lt_min (by positivity [cZ_pos]) (by positivity))
  have ha₁ : a ≤ 1 / 64 := min_le_left _ _
  have haz : a ≤ cZ / 128 := (min_le_right _ _).trans (min_le_left _ _)
  have haκ : a ≤ κ / (2 * (9 * C + 8)) := (min_le_right _ _).trans (min_le_right _ _)
  let D : ℝ := 200 * (4 / a) ^ 4
  refine ⟨a, D, ha, by positivity, ?_⟩
  intro M y hM hy hMlog
  let v := Real.sqrt (Real.log y)
  let U := Real.exp (a * v)
  change Real.log M ≤ a * v at hMlog
  have hM0 : 0 < M := by linarith
  have hy0 : 0 < y := by linarith
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hvv : v ^ 2 = Real.log y := Real.sq_sqrt hly
  have hsv : 1 ≤ a * v := (one_le_log_of_three_le (by linarith : 3 ≤ M)).trans hMlog
  have hv : 1 ≤ v := by
    by_contra! hn
    have hle := mul_le_mul_of_nonneg_left hn.le ha.le
    nlinarith only [hsv, hle, ha₁]
  have hMU : M ≤ U := (Real.log_le_iff_le_exp hM0).mp hMlog
  have hU : 8 ≤ U := hM.trans hMU
  have hU1 : 1 ≤ U := by linarith
  have hU0 : 0 < U := by linarith
  have hT4 : 4 ≤ U ^ (8 : ℕ) := (by linarith : 4 ≤ U).trans (le_self_pow₀ hU1 (by norm_num))
  have hlogU : Real.log U = a * v := Real.log_exp _
  have hlogT : Real.log (U ^ (8 : ℕ)) = 8 * a * v := by
    rw [Real.log_pow, hlogU]
    push_cast
    ring
  have hlogMT : Real.log (M * U ^ (8 : ℕ)) ≤ 9 * a * v := by
    rw [Real.log_mul hM0.ne' (by positivity), hlogT]
    linarith only [hMlog]
  have hlog4 : Real.log 4 ≤ a * v :=
    (Real.log_le_log (by norm_num) (show 4 ≤ M by linarith)).trans hMlog
  have hlogMT' : Real.log (M * (U ^ (8 : ℕ) + 3)) ≤ 10 * a * v := by
    rw [Real.log_mul hM0.ne' (by positivity)]
    have hle := Real.log_le_log (show 0 < U ^ (8 : ℕ) + 3 by positivity)
      (show U ^ (8 : ℕ) + 3 ≤ 4 * U ^ (8 : ℕ) by linarith only [hT4])
    rw [Real.log_mul (by norm_num) (by positivity), hlogT] at hle
    linarith only [hle, hlog4, hMlog]
  have hlgy : Real.log (2 * y) ≤ 2 * v ^ 2 := by
    rw [Real.log_mul (by norm_num) hy0.ne', ← hvv]
    linarith only [Real.log_two_lt_d9, one_le_pow₀ hv (n := 2)]
  have hvexp : v ^ 4 ≤ (4 / a) ^ 4 * U := by
    have h := Real.add_one_le_exp (a * v / 4)
    have hv' : v ≤ (4 / a) * Real.exp (a * v / 4) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      linarith only [h]
    calc v ^ 4 ≤ ((4 / a) * Real.exp (a * v / 4)) ^ 4 :=
          pow_le_pow_left₀ (by linarith) hv' _
      _ = (4 / a) ^ 4 * U := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 1
          change Real.exp (((4 : ℕ) : ℝ) * (a * v / 4)) = Real.exp (a * v)
          congr 1
          push_cast
          ring
  have hCscale : (9 * C + 8) * a ≤ κ / 2 := by
    rw [le_div_iff₀ (by positivity)] at haκ
    nlinarith only [haκ]
  have hquad : (9 * C + 8) * a * v ≤ κ / 2 * v ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hCscale (show 0 ≤ v by linarith)
    have h2 := le_mul_of_one_le_right (by positivity : 0 ≤ κ / 2 * v) hv
    nlinarith only [h1, h2]
  have ht : y ^ (-(κ / 2)) = Real.exp (-(κ / 2 * v ^ 2)) := by
    rw [Real.rpow_def_of_pos hy0, hvv]
    congr 1
    ring
  have hpow : (M * U ^ 8) ^ C * y ^ (-(κ / 2)) ≤ (U ^ (8 : ℕ))⁻¹ := by
    rw [Real.rpow_def_of_pos (by positivity : 0 < M * U ^ (8 : ℕ)), ht, ← Real.exp_add,
      inv_pow_eq_exp hU0, hlogU]
    apply Real.exp_le_exp.mpr
    push_cast
    have hs := mul_le_mul_of_nonneg_right hlogMT hC.le
    nlinarith only [hs, hquad]
  have hsmall : y ^ (-(κ / 2)) ≤ (U ^ (8 : ℕ))⁻¹ := by
    refine (le_mul_of_one_le_left (by positivity) ?_).trans hpow
    exact Real.one_le_rpow (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hU1)) hC.le
  have hyU : U ^ 4 ≤ y := by
    rw [← Real.log_le_log_iff (pow_pos hU0 _) hy0, Real.log_pow, hlogU, ← hvv]
    push_cast
    have h1 := mul_le_mul_of_nonneg_right ha₁ (show 0 ≤ v by linarith)
    have h2 := le_mul_of_one_le_right (show 0 ≤ v by linarith) hv
    nlinarith only [h1, h2]
  have hlogMT0 : 0 ≤ Real.log (M * U ^ (8 : ℕ)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hU1))
  have hlogMT9 : Real.log (M * U ^ (8 : ℕ)) ≤ 9 * v := by
    have hv0 : 0 ≤ v := zero_le_one.trans hv
    have hav := mul_le_mul_of_nonneg_right ha₁ hv0
    exact hlogMT.trans (by nlinarith only [hav, hv0])
  have hp2 : v ^ 2 ≤ v ^ 4 := pow_le_pow_right₀ hv (by norm_num)
  have hp1 : v ≤ v ^ 4 := le_self_pow₀ hv (by norm_num)
  have hlog2 : Real.log (2 * y) ≤ D * U := by
    dsimp only [D]
    nlinarith only [hlgy, hp2, hvexp, show 0 ≤ (4 / a) ^ 4 * U by positivity]
  have hlog4' : Real.log (2 * y) * Real.log (M * U ^ (8 : ℕ)) ^ 2 ≤ D * U := by
    have h := mul_le_mul hlgy (pow_le_pow_left₀ hlogMT0 hlogMT9 2) (sq_nonneg _) (by positivity : 0 ≤ 2 * v ^ 2)
    dsimp only [D]
    nlinarith only [h, hvexp, show 0 ≤ (4 / a) ^ 4 * U by positivity]
  have hlogZ : Real.log (M * (U ^ (8 : ℕ) + 3)) ≤ D * U := by
    dsimp only [D]
    nlinarith only [hlogMT', hp1, hvexp, mul_le_mul_of_nonneg_right ha₁ (show 0 ≤ v by linarith),
      show 0 ≤ (4 / a) ^ 4 * U by positivity]
  refine ⟨hU, hyU, hpow, hsmall, hlog2, hlog4', hlogZ, ?_⟩
  have hZ0 : 0 < Real.log (M * (U ^ (8 : ℕ) + 3)) := by
    apply Real.log_pos
    exact (show 1 < M by linarith).trans_le
      (le_mul_of_one_le_right hM0.le (by linarith only [hT4]))
  change Real.exp (-(cZ * Real.log y / Real.log (M * (U ^ (8 : ℕ) + 3)))) ≤ (U ^ (16 : ℕ))⁻¹
  rw [inv_pow_eq_exp hU0, hlogU, ← hvv]
  apply Real.exp_le_exp.mpr
  push_cast
  apply neg_le_neg
  rw [le_div_iff₀ hZ0]
  have h160 : 160 * a * a ≤ cZ := by
    have h1 := mul_le_mul_of_nonneg_left ha₁ (show 0 ≤ 160 * a by positivity)
    have h2 := mul_le_mul_of_nonneg_left haz (show 0 ≤ (128 : ℝ) by norm_num)
    nlinarith only [h1, h2, ha]
  calc 16 * (a * v) * Real.log (M * (U ^ (8 : ℕ) + 3)) ≤ 16 * (a * v) * (10 * a * v) :=
        mul_le_mul_of_nonneg_left hlogMT' (by positivity)
    _ ≤ cZ * v ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right h160 (sq_nonneg v)]

end QH.PrimeProgressions
