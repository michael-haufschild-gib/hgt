import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedZeroDifference

/-! A zero-free box controls the error of a finite logarithmic derivative sum. -/

open Complex UpperTheory.Top WindowedLandauTheory.HC
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

namespace QH

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

theorem norm_partialLogDerivative_error_le (hχ : χ ≠ 1) (hp : χ.IsPrimitive) {Q z : ℝ}
    (hbox : ZeroBox Q χ) (hz : 2 ≤ z) (hQ : z ^ 8 + 2 ≤ Q) :
    ‖partialLogDerivative χ z + An.logDerivativeAtOne χ‖ ≤
      50000000 * (1 + Real.log N) * (1 + Real.log z) ^ 2 * z ^ (-1 / 400 : ℝ) := by
  let h := z ^ (399 / 400 : ℝ)
  let T := ⌈z ^ 8⌉₊
  let E := z ^ (-1 / 400 : ℝ)
  let v := 1 + Real.log z
  have hz₁ : 1 < z := one_lt_two.trans_le hz
  have hz₀ : 0 < z := zero_lt_one.trans hz₁
  have hh₁ : 1 ≤ h := Real.one_le_rpow hz₁.le (by norm_num)
  have hh : 0 < h := zero_lt_one.trans_le hh₁
  have hhz : h ≤ z := (Real.rpow_le_rpow_of_exponent_le hz₁.le (by norm_num :
    (399 / 400 : ℝ) ≤ 1)).trans_eq (Real.rpow_one z)
  have hE₀ : 0 ≤ E := by dsimp [E]; positivity
  have hfrac : h / z = E := by
    dsimp [h, E]
    rw [← Real.rpow_sub_one hz₀.ne']
    congr 1
    ring
  have hInv : 1 / z ≤ E := by
    rw [← hfrac]
    exact div_le_div_of_nonneg_right hh₁ hz₀.le
  have hv : 1 ≤ v := le_add_of_nonneg_right (Real.log_nonneg hz₁.le)
  have hTz : z ^ 8 ≤ (T : ℝ) := Nat.le_ceil _
  have hTzu : (T : ℝ) ≤ z ^ 8 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hT : 1 ≤ T := Nat.one_le_cast.mp ((one_le_pow₀ hz₁.le).trans hTz)
  have hTl : (T : ℝ) + 1 ≤ Q := by linarith only [hTzu, hQ]
  have hTlog : Real.log ((T : ℝ) + 3) ≤ 12 * v := by
    have hzPow : z ^ 8 + 4 ≤ z ^ 12 := by
      have h₁ : (2 : ℝ) ≤ z ^ 8 := hz.trans (le_self_pow₀ hz₁.le (by norm_num))
      have h₂ : (4 : ℝ) ≤ z ^ 4 := by
        calc (4 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
          _ ≤ _ := pow_le_pow_left₀ (by norm_num) hz 4
      calc z ^ 8 + 4 ≤ z ^ 8 * z ^ 4 := by
            have hh := mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ z ^ 8)
            linarith only [h₁, hh]
        _ = _ := by rw [← pow_add]
    have hl := Real.log_le_log (by positivity : 0 < (T : ℝ) + 3)
      (show (T : ℝ) + 3 ≤ z ^ 12 by linarith only [hTzu, hzPow])
    rw [Real.log_pow] at hl
    norm_num at hl
    dsimp [v]
    linarith only [hl]
  have hTlog' : 2 + Real.log T ≤ 14 * v := by
    have hT₁ : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have h := Real.log_le_log (zero_lt_one.trans_le hT₁)
      (le_add_of_nonneg_right (by norm_num) : (T : ℝ) ≤ T + 3)
    linarith only [h, hTlog, hv]
  have hsqrt : z ^ 4 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by
    rw [← pow_mul]; exact hTz)
  have hhigher : 8 * (2 * z + h) / h / Real.sqrt T ≤ 24 * E := by
    have h₁ : 8 * (2 * z + h) / h ≤ 24 * z := by
      calc 8 * (2 * z + h) / h ≤ 8 * (2 * z + h) :=
            div_le_self (by positivity) hh₁
        _ ≤ _ := by linarith only [hhz]
    have hzpow : z ^ 2 ≤ z ^ 4 := pow_le_pow_right₀ hz₁.le (by norm_num)
    calc _ ≤ (24 * z) / Real.sqrt T := div_le_div_of_nonneg_right h₁ (Real.sqrt_nonneg _)
      _ ≤ (24 * z) / z ^ 4 := div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt
      _ ≤ (24 * z) / z ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hzpow
      _ = 24 * (1 / z) := by field_simp [hz₀.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by norm_num)
  let Z (t : ℝ) := ∑' q : LZero χ, (t : ℂ) ^ q.point / (q.point * (q.point - 1))
  have hZ : ‖Z (z + h) - Z z‖ / h ≤ 269000 * localCountConst N * v ^ 2 * E := by
    have hZ₀ := norm_smoothed_zero_difference_le hχ hp hbox hz₁.le hh hT hTl
    refine hZ₀.trans ?_
    have hL (t : ℝ) (ht : 1 ≤ t) : 0 ≤ Real.log t := Real.log_nonneg ht
    have hL₀ : 0 ≤ Real.log ((T : ℝ) + 3) := hL _ (by positivity)
    have hL₁ : 0 ≤ 2 + Real.log T := by
      have := hL T (by exact_mod_cast hT)
      linarith
    have hm : Real.log ((T : ℝ) + 3) * (2 + Real.log T) ≤ (12 * v) * (14 * v) :=
      mul_le_mul hTlog hTlog' hL₁ (by linarith only [hv])
    have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 400 * E by positivity)
    have hE' : E ≤ v ^ 2 * E := le_mul_of_one_le_left hE₀ (one_le_pow₀ hv)
    have hc := localCountConst_nonneg (NeZero.pos N)
    calc 4 * localCountConst N *
          (400 * E * Real.log (T + 3) * (2 + Real.log T) + 8 * (2 * z + h) / h / Real.sqrt T)
        ≤ 4 * localCountConst N * (67224 * v ^ 2 * E) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith only [hm', hhigher, hE']
      _ ≤ _ := by
        have hh' : 0 ≤ localCountConst N * v ^ 2 * E := by positivity
        linarith only [hh']
  obtain ⟨β, hβ⟩ := smoothed_identity hχ hp
  let F (t : ℝ) := An.gChi χ t + Z t - (β + efGamma χ * Complex.log t)
  have hz' : 1 < z + h := hz₁.trans_le (le_add_of_nonneg_right hh.le)
  have hF (t : ℝ) (ht : 1 < t) : ‖F t‖ ≤ efD / t := hβ t ht
  have hdiff : An.gChi χ (z + h) - An.gChi χ z =
      (F (z + h) - F z) - (Z (z + h) - Z z) +
        efGamma χ * (Complex.log (z + h) - Complex.log z) := by
    dsimp only [F]
    ring
  have hLog : ‖efGamma χ * (Complex.log (z + h) - Complex.log z)‖ ≤ h / z := by
    have hpos : 0 ≤ Real.log (z + h) - Real.log z :=
      sub_nonneg.mpr (Real.log_le_log hz₀ (by linarith only [hh]))
    rw [norm_mul, ← Complex.ofReal_log (by positivity : 0 ≤ z + h),
      ← Complex.ofReal_log hz₀.le, ← ofReal_sub, norm_real, Real.norm_of_nonneg hpos]
    refine (mul_le_of_le_one_left hpos (norm_efGamma_le χ)).trans ?_
    rw [← Real.log_div (by positivity : z + h ≠ 0) hz₀.ne']
    have hl := Real.log_le_sub_one_of_pos (show 0 < (z + h) / z by positivity)
    convert hl using 1
    field_simp [hz₀.ne']
    ring
  have hw := norm_ramp_difference_sub hχ hz₁ hh
  let D := partialLogDerivative χ z + An.logDerivativeAtOne χ
  have hn : ‖D‖ ≤ ‖Z (z + h) - Z z‖ / h + 5 / z + (h + 1) * Real.log (z + h) / z := by
    have hF₀ : ‖F (z + h) - F z‖ ≤ 4 / z := by
      have ht := div_le_div_of_nonneg_left efD_nonneg hz₀ (le_add_of_nonneg_right hh.le)
      refine (norm_sub_le _ _).trans ((add_le_add ((hF _ hz').trans ht) (hF _ hz₁)).trans ?_)
      have h₀ := div_le_div_of_nonneg_right efD_le_two hz₀.le
      linarith only [h₀]
    have hb : ‖An.gChi χ (z + h) - An.gChi χ z‖ ≤ ‖Z (z + h) - Z z‖ + 4 / z + h / z := by
      rw [hdiff]
      have ht := (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      linarith only [ht, hF₀, hLog]
    have he : (h : ℂ) * D = (An.gChi χ (z + h) - An.gChi χ z) -
        (An.gChi χ (z + h) - An.gChi χ z - (h : ℂ) * D) := by ring
    have hu := (norm_sub_le (An.gChi χ (z + h) - An.gChi χ z)
      (An.gChi χ (z + h) - An.gChi χ z - (h : ℂ) * D))
    rw [← he, norm_mul, norm_real, Real.norm_of_nonneg hh.le, mul_comm h] at hu
    apply (le_div_iff₀ hh).mpr at hu
    refine hu.trans ?_
    have hsum := div_le_div_of_nonneg_right (add_le_add hb hw) hh.le
    have hconst : (4 / z) / h ≤ 4 / z := div_le_self (by positivity) hh₁
    have he' : (h / z) / h = 1 / z := by field_simp [hz₀.ne', hh.ne']
    have hlast : (h * (h + 1) * Real.log (z + h) / z) / h =
        (h + 1) * Real.log (z + h) / z := by field_simp [hz₀.ne', hh.ne']
    simp only [add_div, he', hlast] at hsum
    linarith only [hsum, hconst]
  have htrim : (h + 1) * Real.log (z + h) / z ≤ 2 * v * E := by
    have hlog := Real.log_le_log (by positivity : 0 < z + h) (show z + h ≤ 2 * z by linarith only [hhz])
    rw [Real.log_mul (by norm_num) hz₀.ne'] at hlog
    have hlogv : Real.log (z + h) ≤ v := by
      dsimp [v]
      linarith only [hlog, Real.log_two_lt_d9]
    have h₁ := mul_le_mul (by linarith only [hh₁] : h + 1 ≤ 2 * h) hlogv
      (Real.log_nonneg hz'.le) (by positivity)
    calc _ ≤ (2 * h) * v / z := div_le_div_of_nonneg_right h₁ hz₀.le
      _ = 2 * v * E := by rw [← hfrac]; ring
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hNlog : 0 ≤ Real.log N := Real.log_nonneg hN₁
  have hC : localCountConst N ≤ 140 * (1 + Real.log N) := (localCountConst_le (NeZero.pos N)).trans
    (by linarith only [hNlog])
  have hv₂ : 1 ≤ v ^ 2 := one_le_pow₀ hv
  have hvle : v ≤ v ^ 2 := le_self_pow₀ hv (by norm_num)
  have hN' : 1 ≤ 1 + Real.log N := le_add_of_nonneg_right hNlog
  change ‖D‖ ≤ 50000000 * (1 + Real.log N) * v ^ 2 * E
  calc ‖D‖ ≤ ‖Z (z + h) - Z z‖ / h + 5 / z + (h + 1) * Real.log (z + h) / z := hn
    _ ≤ (269000 * (140 * (1 + Real.log N))) * v ^ 2 * E + 7 * v ^ 2 * E := by
      have hZ' : ‖Z (z + h) - Z z‖ / h ≤
          (269000 * (140 * (1 + Real.log N))) * v ^ 2 * E := hZ.trans (by gcongr)
      have hE₁ := mul_le_mul_of_nonneg_right hv₂ hE₀
      have hE₂ := mul_le_mul_of_nonneg_right hvle hE₀
      linarith only [hZ', hInv, hE₁, hE₂, htrim]
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_right hN' (show 0 ≤ v ^ 2 * E by positivity)
      have h₂ : 0 ≤ (1 + Real.log N) * (v ^ 2 * E) := by positivity
      linarith only [h₁, h₂]

end

end QH
