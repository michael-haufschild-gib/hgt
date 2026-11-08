import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainVKParameters

/-!
# Dilation of the arithmetic contour width

Doubling the height changes the logarithmic zero-free profile by at most
a fixed factor, so the admissible Mellin rectangle retains its full profile.
-/

open RHTower
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Doubling the contour height changes the logarithmic zero-free profile by a fixed factor. -/
theorem vkHadamardWidth_double_add_one_ge {T : ℝ} (hT : Real.exp (Real.exp 1) ≤ T) :
    vkHadamardWidth T / 8 ≤ vkHadamardWidth (2 * T + 1) := by
  have he := Real.add_one_le_exp (1 : ℝ)
  have hee := Real.add_one_le_exp (Real.exp 1)
  have hT3 : 3 ≤ T := by linarith only [he, hee, hT]
  have hT0 : 0 < T := by linarith only [hT3]
  have hL : Real.exp 1 ≤ Real.log T := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hT
  have hL2 : 2 ≤ Real.log T := by linarith only [he, hL]
  have hL0 : 0 < Real.log T := by linarith only [hL2]
  have hM : 1 ≤ Real.log (Real.log T) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hL
  have hM0 : 0 < Real.log (Real.log T) := by linarith only [hM]
  have hTg : T ≤ 2 * T + 1 := by linarith only [hT3]
  have hLg : 0 < Real.log (2 * T + 1) :=
    hL0.trans_le (Real.log_le_log hT0 hTg)
  have hMg : 0 < Real.log (Real.log (2 * T + 1)) :=
    hM0.trans_le (Real.log_le_log hL0 (Real.log_le_log hT0 hTg))
  have hlog : Real.log (2 * T + 1) ≤ 2 * Real.log T := by
    have hs : 2 * T + 1 ≤ T ^ 2 := by nlinarith only [hT3, sq_nonneg (T - 3)]
    have h := Real.log_le_log (show 0 < 2 * T + 1 by positivity) hs
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hloglog : Real.log (Real.log (2 * T + 1)) ≤ 2 * Real.log (Real.log T) := by
    have hs : 2 * Real.log T ≤ Real.log T ^ 2 := by
      nlinarith only [hL2, sq_nonneg (Real.log T - 2)]
    have h := Real.log_le_log hLg (hlog.trans hs)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hfirst := Real.rpow_le_rpow_of_nonpos hLg hlog (by norm_num : -(2 : ℝ) / 3 ≤ 0)
  have hsecond := Real.rpow_le_rpow_of_nonpos hMg hloglog (by norm_num : -(5 : ℝ) / 3 ≤ 0)
  rw [Real.mul_rpow (by norm_num) hL0.le] at hfirst
  rw [Real.mul_rpow (by norm_num) hM0.le] at hsecond
  have hprod := mul_le_mul hfirst hsecond (by positivity)
    (Real.rpow_nonneg hLg.le _)
  have hfactor : (2 : ℝ) ^ (-(2 : ℝ) / 3) * (2 : ℝ) ^ (-(5 : ℝ) / 3) =
      (2 : ℝ) ^ (-(7 : ℝ) / 3) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have htwo : (1 : ℝ) / 8 ≤ (2 : ℝ) ^ (-(7 : ℝ) / 3) := by
    calc
      _ = (2 : ℝ) ^ (-3 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hmul : (1 : ℝ) / 8 *
      (Real.log T ^ (-(2 : ℝ) / 3) * Real.log (Real.log T) ^ (-(5 : ℝ) / 3)) ≤
      (2 : ℝ) ^ (-(7 : ℝ) / 3) *
        (Real.log T ^ (-(2 : ℝ) / 3) * Real.log (Real.log T) ^ (-(5 : ℝ) / 3)) :=
    mul_le_mul_of_nonneg_right htwo (by positivity)
  have heq : (2 : ℝ) ^ (-(2 : ℝ) / 3) * Real.log T ^ (-(2 : ℝ) / 3) *
      ((2 : ℝ) ^ (-(5 : ℝ) / 3) * Real.log (Real.log T) ^ (-(5 : ℝ) / 3)) =
      (2 : ℝ) ^ (-(7 : ℝ) / 3) *
        (Real.log T ^ (-(2 : ℝ) / 3) * Real.log (Real.log T) ^ (-(5 : ℝ) / 3)) := by
    rw [← hfactor]
    ring
  rw [heq] at hprod
  unfold vkHadamardWidth
  linarith only [hmul.trans hprod]

/-- The arithmetic contour keeps a fixed fraction of the unshifted logarithmic profile. -/
theorem narainVKWidth_ge_profile {δ T : ℝ} (hδ : 0 < δ)
    (hT : Real.exp (Real.exp 1) ≤ T) :
    min δ 1 / 64 * vkHadamardWidth T ≤ narainVKWidth δ T := by
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT
  have hraw := narainVKWidth_ge_fraction (T := T) hδ (by linarith only [hT, hT0])
  have hscale := mul_le_mul_of_nonneg_left (vkHadamardWidth_double_add_one_ge hT)
    (show 0 ≤ min δ 1 / 8 by positivity)
  calc
    _ = min δ 1 / 8 * (vkHadamardWidth T / 8) := by ring
    _ ≤ min δ 1 / 8 * vkHadamardWidth (2 * T + 1) := hscale
    _ ≤ _ := hraw

#print axioms vkHadamardWidth_double_add_one_ge
#print axioms narainVKWidth_ge_profile
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
