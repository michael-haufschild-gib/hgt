import GaloisForLFunctions.RHTower.ZetaWeylCorrelationBound

/-! # Power bounds for the fifth-derivative logarithmic correlation

The fifth dual scale is comparable to `N⁹/X⁴`, where `X=Th`. Factoring its
powers isolates both correlation exponents and leaves the existing
stationary-phase error terms unchanged.
-/

noncomputable section
open RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Main fifth-dual power after multiplication by the stationary-point amplitude. -/
theorem fifthDiffLog_id_one {X n : ℝ} (hX : 0 < X) (hn : 0 < n) :
    X / n ^ 2 * (n ^ 9 / X ^ 4) ^ (1 / 30 : ℝ) * (n ^ 3 / X) ^ (1 / 2 : ℝ) =
      X ^ (11 / 30 : ℝ) * n ^ (-(1 / 5) : ℝ) := by
  refine log_pos_mul_rpow_eq (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow hX, Real.log_rpow hn,
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- Secondary fifth-dual power after multiplication by the stationary-point amplitude. -/
theorem fifthDiffLog_id_two {X n : ℝ} (hX : 0 < X) (hn : 0 < n) :
    (X / n ^ 2) ^ (7 / 8 : ℝ) * (X ^ 4 / n ^ 9) ^ (1 / 16 : ℝ) *
        (n ^ 3 / X) ^ (1 / 2 : ℝ) =
      X ^ (5 / 8 : ℝ) * n ^ (-(13 / 16) : ℝ) := by
  refine log_pos_mul_rpow_eq (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow hX, Real.log_rpow hn,
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- Lower endpoint scale for the fifth derivative. -/
theorem fifthBlock_lam_ge {n a h X : ℝ} (hX : 0 < X) (hn : 0 < n)
    (ha : n / 2 ≤ a) (hh : 0 ≤ h) :
    1 / 512 * (n ^ 9 / X ^ 4) ≤ (a + h / 2) * (a * (a + h)) ^ 4 / X ^ 4 := by
  have haa := block_aa_ge ha hn.le hh
  have hbase : n / 2 ≤ a + h / 2 := by linarith only [ha, hh]
  have hnum : n ^ 9 / 512 ≤ (a + h / 2) * (a * (a + h)) ^ 4 := by
    calc n ^ 9 / 512 = (n / 2) * (n ^ 2 / 4) ^ 4 := by ring
      _ ≤ _ := mul_le_mul hbase (pow_le_pow_left₀ (by positivity) haa 4)
        (by positivity) (by linarith only [ha, hh, hn])
  calc 1 / 512 * (n ^ 9 / X ^ 4) = (n ^ 9 / 512) / X ^ 4 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hnum (pow_nonneg hX.le 4)

/-- Upper endpoint scale for the fifth derivative. -/
theorem fifthBlock_lam_le {n a h X : ℝ} (hX : 0 < X) (hn : 0 < n)
    (ha : n / 2 ≤ a) (han : a ≤ n) (hh : 0 ≤ h) (hhn : 2 * h ≤ n) :
    (a + h / 2) * (a * (a + h)) ^ 4 / X ^ 4 ≤ 7 * (n ^ 9 / X ^ 4) := by
  have ha0 : 0 ≤ a := by linarith only [ha, hn]
  have hah : a + h ≤ 3 / 2 * n := by linarith only [han, hhn]
  have haa : a * (a + h) ≤ 3 / 2 * n ^ 2 := by
    calc a * (a + h) ≤ n * (3 / 2 * n) := mul_le_mul han hah (by positivity) hn.le
      _ = _ := by ring
  have hnum : (a + h / 2) * (a * (a + h)) ^ 4 ≤ 7 * n ^ 9 := by
    calc _ ≤ (5 / 4 * n) * (3 / 2 * n ^ 2) ^ 4 :=
        mul_le_mul (by linarith only [han, hhn])
          (pow_le_pow_left₀ (by positivity) haa 4) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith only [pow_nonneg hn.le 9]
  calc _ ≤ (7 * n ^ 9) / X ^ 4 := div_le_div_of_nonneg_right hnum (pow_nonneg hX.le 4)
    _ = _ := by ring

/-- A uniform endpoint ratio on a dyadic source interval. -/
theorem fifthBlock_gamma_le {n a b h : ℝ} (hn : 0 < n) (ha : n / 2 ≤ a)
    (hab : a ≤ b) (hbn : b ≤ 2 * n) (hh : 0 ≤ h) (hhn : 2 * h ≤ n) :
    12 * ((b + h / 2) * (b * (b + h)) ^ 4) /
        ((a + h / 2) * (a * (a + h)) ^ 4) ≤ 10 ^ 8 := by
  have ha0 : 0 < a := by linarith only [ha, hn]
  have hb0 : 0 < b := ha0.trans_le hab
  have hbb : b * (b + h) ≤ 5 * n ^ 2 := by
    calc b * (b + h) ≤ (2 * n) * (5 / 2 * n) :=
        mul_le_mul hbn (by linarith only [hbn, hhn]) (by positivity) (by positivity)
      _ = _ := by ring
  have hup : (b + h / 2) * (b * (b + h)) ^ 4 ≤ (5625 / 4) * n ^ 9 := by
    calc _ ≤ (9 / 4 * n) * (5 * n ^ 2) ^ 4 :=
        mul_le_mul (by linarith only [hbn, hhn])
          (pow_le_pow_left₀ (by positivity) hbb 4) (by positivity) (by positivity)
      _ = _ := by ring
  have hlo := fifthBlock_lam_ge (X := 1) (by norm_num) hn ha hh
  norm_num only [one_pow, div_one] at hlo
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [hup, hlo, pow_nonneg hn.le 9]

/-- The stationary-phase remainder is independent of the derivative order used on its dual sum. -/
theorem fifthBlock_B_error_le {n X lam₂ lam₃ ρ K βα : ℝ}
    (hn : 0 < n) (hX : 0 < X) (hXn : n ^ 2 ≤ X)
    (hlam₂ : X / (8 * n ^ 3) ≤ lam₂)
    (hlam₃0 : 0 ≤ lam₃) (hlam₃ : lam₃ ≤ 96 * (X / n ^ 4))
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 125) (hK : K ≤ 11 * (X / n ^ 2))
    (hβα : βα ≤ 5 * (X / n ^ 2)) :
    5 + K + 19 / Real.sqrt lam₂ + βα *
        (3 * lam₃ * (n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ)) ^ 4 +
          3 / (lam₂ * (n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ))) + 2 * ρ) ≤
      2000 * (X / n ^ 2 + (n ^ 3 / X) ^ (1 / 2 : ℝ) +
        X ^ (2 / 5 : ℝ) * n ^ (-(2 / 5) : ℝ)) := by
  obtain ⟨δ, hδ⟩ : ∃ d, d = n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  rw [← hδ]
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨P3, hP3⟩ : ∃ p, p = X / n ^ 2 := ⟨_, rfl⟩
  obtain ⟨P4, hP4⟩ : ∃ p, p = (n ^ 3 / X) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨P5, hP5⟩ : ∃ p, p = X ^ (2 / 5 : ℝ) * n ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  rw [← hP3, ← hP4, ← hP5]
  rw [← hP3] at hK hβα
  have hP3one : 1 ≤ P3 := by
    rw [hP3, le_div_iff₀ (by positivity)]
    simpa only [one_mul] using hXn
  have hP4n : 0 ≤ P4 := by rw [hP4]; positivity
  have hP5n : 0 ≤ P5 := by rw [hP5]; positivity
  have hlam₂0 : 0 < lam₂ := lt_of_lt_of_le (by positivity) hlam₂
  have hf4 : (Real.sqrt lam₂)⁻¹ ≤ 3 * P4 := by
    refine (inv_sqrt_le_rpow (by positivity) hlam₂).trans ?_
    have e : (X / (8 * n ^ 3))⁻¹ = 8 * (n ^ 3 / X) := by field_simp
    rw [e, Real.mul_rpow (by norm_num) (by positivity), hP4]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
    norm_num
  have hδ4 : 3 * lam₃ * δ ^ 4 ≤ 288 * (X / n ^ 4 * δ ^ 4) := by
    have hm := mul_le_mul_of_nonneg_right hlam₃ (pow_nonneg hδ0.le 4)
    linarith only [hm]
  have hδ1 : 3 / (lam₂ * δ) ≤ 24 * (n ^ 3 / X / δ) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ 8 * n ^ 3 / X * lam₂ := by
      have hm := mul_le_mul_of_nonneg_left hlam₂ (by positivity : 0 ≤ 8 * n ^ 3 / X)
      have he : 8 * n ^ 3 / X * (X / (8 * n ^ 3)) = 1 := by field_simp
      rw [he] at hm
      exact hm
    have he : 24 * (n ^ 3 / X / δ) * (lam₂ * δ) = 3 * (8 * n ^ 3 / X * lam₂) := by
      field_simp
      ring
    rw [he]
    linarith only [h1]
  have hid3 : P3 * (X / n ^ 4 * δ ^ 4) = P5 := by
    rw [hP3, hδ, hP5, diffLog_id_three hX hn]
  have hid4 : P3 * (n ^ 3 / X / δ) = P5 := by
    rw [hP3, hδ, hP5, diffLog_id_four hX hn]
  have h19 : 19 / Real.sqrt lam₂ ≤ 57 * P4 := by
    rw [div_eq_mul_inv]
    linarith only [hf4]
  have hin : 3 * lam₃ * δ ^ 4 + 3 / (lam₂ * δ) + 2 * ρ ≤
      288 * (X / n ^ 4 * δ ^ 4) + 24 * (n ^ 3 / X / δ) + 250 := by
    linarith only [hδ4, hδ1, hρ]
  have hprod := mul_le_mul hβα hin (by positivity) (by positivity)
  have he : 5 * P3 * (288 * (X / n ^ 4 * δ ^ 4) + 24 * (n ^ 3 / X / δ) + 250) =
      1440 * (P3 * (X / n ^ 4 * δ ^ 4)) + 120 * (P3 * (n ^ 3 / X / δ)) + 1250 * P3 := by ring
  rw [he, hid3, hid4] at hprod
  linarith only [hprod, h19, hK, hP3one, hP4n, hP5n]

/-- Explicit power estimate for the fifth-derivative dual sum. -/
theorem fifthBlock_dual_numeric {n X γ M lam lam₂ : ℝ} (hn : 0 < n) (hX : 0 < X)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 10 ^ 8) (hM0 : 0 ≤ M) (hM : M ≤ 5 * (X / n ^ 2))
    (hlamlo : 1 / 512 * (n ^ 9 / X ^ 4) ≤ lam)
    (hlamup : lam ≤ 7 * (n ^ 9 / X ^ 4)) (hlam₂ : X / (8 * n ^ 3) ≤ lam₂) :
    512 * (M * (γ ^ 2 * lam) ^ (1 / 30 : ℝ) +
        M ^ (7 / 8 : ℝ) * lam ^ (-(1 / 16 : ℝ))) * (Real.sqrt lam₂)⁻¹ ≤
      10 ^ 24 * (X ^ (11 / 30 : ℝ) * n ^ (-(1 / 5) : ℝ) +
        X ^ (5 / 8 : ℝ) * n ^ (-(13 / 16) : ℝ)) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlamlo
  have hγsq := pow_le_pow_left₀ hγ0 hγ 2
  have hraw : γ ^ 2 * lam ≤ (7 * 10 ^ 16) * (n ^ 9 / X ^ 4) := by
    calc γ ^ 2 * lam ≤ (10 ^ 8) ^ 2 * (7 * (n ^ 9 / X ^ 4)) :=
        mul_le_mul hγsq hlamup hlam0.le (by positivity)
      _ = _ := by ring
  have hf1 : (γ ^ 2 * lam) ^ (1 / 30 : ℝ) ≤
      (7 * 10 ^ 16) * (n ^ 9 / X ^ 4) ^ (1 / 30 : ℝ) := by
    refine (Real.rpow_le_rpow (by positivity) hraw (by norm_num)).trans ?_
    rw [Real.mul_rpow (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_right
      (rpow_le_self_of_le_one (by norm_num) (by norm_num)) (by positivity)
  have hf2 : lam ^ (-(1 / 16 : ℝ)) ≤ 512 * (X ^ 4 / n ^ 9) ^ (1 / 16 : ℝ) := by
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) hlamlo (by norm_num)).trans ?_
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    have he : (1 / 512 * (n ^ 9 / X ^ 4))⁻¹ = 512 * (X ^ 4 / n ^ 9) := by field_simp
    rw [he, Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right
      (rpow_le_self_of_le_one (by norm_num) (by norm_num)) (by positivity)
  have hf3 : M ^ (7 / 8 : ℝ) ≤ 5 * (X / n ^ 2) ^ (7 / 8 : ℝ) := by
    refine (Real.rpow_le_rpow hM0 hM (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right
      (rpow_le_self_of_le_one (by norm_num) (by norm_num)) (by positivity)
  have hf4 : (Real.sqrt lam₂)⁻¹ ≤ 3 * (n ^ 3 / X) ^ (1 / 2 : ℝ) := by
    refine (inv_sqrt_le_rpow (by positivity) hlam₂).trans ?_
    have he : (X / (8 * n ^ 3))⁻¹ = 8 * (n ^ 3 / X) := by field_simp
    rw [he, Real.mul_rpow (by norm_num) (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
    norm_num
  have hmain := mul_le_mul
    (mul_le_mul hM hf1 (by positivity) (by positivity)) hf4 (by positivity) (by positivity)
  have hsecondary := mul_le_mul
    (mul_le_mul hf3 hf2 (by positivity) (by positivity)) hf4 (by positivity) (by positivity)
  have hm : M * (γ ^ 2 * lam) ^ (1 / 30 : ℝ) * (Real.sqrt lam₂)⁻¹ ≤
      (105 * 10 ^ 16) * (X ^ (11 / 30 : ℝ) * n ^ (-(1 / 5) : ℝ)) := by
    refine hmain.trans_eq ?_
    rw [← fifthDiffLog_id_one hX hn]
    ring
  have hs : M ^ (7 / 8 : ℝ) * lam ^ (-(1 / 16 : ℝ)) * (Real.sqrt lam₂)⁻¹ ≤
      7680 * (X ^ (5 / 8 : ℝ) * n ^ (-(13 / 16) : ℝ)) := by
    refine hsecondary.trans_eq ?_
    rw [← fifthDiffLog_id_two hX hn]
    ring
  have h1 : 0 ≤ X ^ (11 / 30 : ℝ) * n ^ (-(1 / 5) : ℝ) := by positivity
  have h2 : 0 ≤ X ^ (5 / 8 : ℝ) * n ^ (-(13 / 16) : ℝ) := by positivity
  linarith only [hm, hs, h1, h2]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.fifthBlock_gamma_le

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.fifthBlock_B_error_le

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.fifthBlock_dual_numeric
