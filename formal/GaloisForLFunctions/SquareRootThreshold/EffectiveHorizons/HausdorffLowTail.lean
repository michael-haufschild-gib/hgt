import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffRealProfile
import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Low ordinates are exponentially below the Hausdorff saddle

The thermal threshold estimate applies below one quarter of the saddle
height. Its exact normalization yields a loss bounded by `exp (-4p)`.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

open _root_.RHTower

/-- Exact comparison of the thermal bound with the real saddle value. -/
theorem thermal_scale_eq_saddle {R s : ℝ} {p r : ℕ} (hs : 0 < s) (hr : 0 < r)
    (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r) :
    (41 * (p : ℝ) * R / r) ^ p * R ^ r =
      realKernel R p r s * 41 ^ p * (1 + (p : ℝ) / r) ^ (p + r) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h₁ : s⁻¹ ^ 2 * 41 * (1 + (p : ℝ) / r) = 41 * (p : ℝ) * R / r := by
    field_simp [hs.ne', hrR]
    nlinarith only [hbalance]
  have h₂ : (R - s⁻¹ ^ 2) * (1 + (p : ℝ) / r) = R := by
    field_simp [hs.ne', hrR]
    nlinarith only [hbalance]
  rw [realKernel, pow_add]
  calc
    _ = (s⁻¹ ^ 2 * 41 * (1 + (p : ℝ) / r)) ^ p *
        ((R - s⁻¹ ^ 2) * (1 + (p : ℝ) / r)) ^ r := by rw [h₁, h₂]
    _ = _ := by simp only [mul_pow]; ring

/-- The thermal exponential wins uniformly over both normalizing powers. -/
theorem thermal_ratio_le {p r : ℕ} (hr : 0 < r) (hpr : 8 * (p : ℝ) ≤ r) :
    (41 : ℝ) ^ p * (1 + (p : ℝ) / r) ^ (p + r) * Real.exp (-(99 / 10 * (p : ℝ))) ≤
      Real.exp (-4 * (p : ℝ)) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have h41 : (41 : ℝ) ≤ Real.exp 4 := by
    have h : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8 / 3) h 4
    rw [← Real.exp_nat_mul] at h4
    norm_num at h4
    linarith only [h4]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 41) h41 p
  have hq : 0 ≤ 1 + (p : ℝ) / r := by positivity
  have hqexp : 1 + (p : ℝ) / r ≤ Real.exp ((p : ℝ) / r) := by
    linarith only [Real.add_one_le_exp ((p : ℝ) / r)]
  have hqpow := pow_le_pow_left₀ hq hqexp (p + r)
  have hratio : (p : ℝ) / r ≤ 1 / 8 := by
    rw [div_le_iff₀ hrR]
    linarith only [hpr]
  have hlinear : ((p + r : ℕ) : ℝ) * ((p : ℝ) / r) ≤ 9 / 8 * (p : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hratio hpR
    push_cast
    have heq : ((p : ℝ) + r) * ((p : ℝ) / r) = (p : ℝ) * ((p : ℝ) / r) + p := by
      field_simp [hrR.ne']
    rw [heq]
    linarith only [h]
  calc
    _ ≤ Real.exp 4 ^ p * Real.exp ((p : ℝ) / r) ^ (p + r) *
        Real.exp (-(99 / 10 * (p : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hpow hqpow (by positivity) (by positivity)) (Real.exp_pos _).le
    _ = Real.exp ((p : ℝ) * 4 + ((p + r : ℕ) : ℝ) * ((p : ℝ) / r) - 99 / 10 * (p : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-4 * (p : ℝ)) := Real.exp_le_exp.mpr
      (by linarith only [hlinear, hpR])

/-- Low ordinate atoms lie above the thermal threshold and are exponentially small. -/
theorem norm_atom_le_saddle_low {R s T : ℝ} (k r : ℕ) (hR : 0 < R) (hs : 0 < s)
    (hbalance : ((k + 1 : ℕ) : ℝ) * (R * s ^ 2 - 1) = r)
    (hpr : 200 * ((k + 1 : ℕ) : ℝ) ≤ r) (hT : 500 ≤ T)
    (hthermal : 10 * ((k + 1 : ℕ) : ℝ) * R * T ^ 2 = r)
    {q : XiZeroCopy} (hlamR : xiThermalNode q ≤ R) (hq : |(q.1 : ℂ).im| ≤ s / 4) :
    ‖hausdorffAtomTerm R k r q‖ ≤
      realKernel R (k + 1) r s * Real.exp (-4 * ((k + 1 : ℕ) : ℝ)) := by
  have hp : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hrR : 0 < (r : ℝ) := by linarith only [hpr, hp]
  have hr : 0 < r := by exact_mod_cast hrR
  have hT0 : 0 < T := by linarith only [hT]
  have hΛ : 10 * ((k + 1 : ℕ) : ℝ) * R / r = 1 / T ^ 2 := by
    rw [div_eq_div_iff hrR.ne' (sq_pos_of_pos hT0).ne']
    simpa only [one_mul] using hthermal
  have hsep : s / 4 < 97 / 100 * T := by
    have hsp : ((k + 1 : ℕ) : ℝ) * R * s ^ 2 = (r : ℝ) + (k + 1 : ℕ) := by
      nlinarith only [hbalance]
    have hpR : 0 < ((k + 1 : ℕ) : ℝ) * R := by positivity
    have hsq : s ^ 2 < 11 * T ^ 2 := by
      have hdiff : 0 < ((k + 1 : ℕ) : ℝ) * R * (11 * T ^ 2 - s ^ 2) := by
        nlinarith only [hsp, hthermal, hpr, hp]
      exact sub_pos.mp ((mul_pos_iff_of_pos_left hpR).mp hdiff)
    nlinarith only [hsq, hs, hT0]
  have hthreshold : 1 / T ^ 2 < xiThermalNode q := by
    by_contra h
    have hγ := ordinate_ge_of_xiThermalNode_le_inv_sq (by linarith only [hT]) (le_of_not_gt h)
    rw [xiSpectralPoint_re_eq_ordinate'] at hγ
    linarith only [hγ, hq, hsep]
  have hbound := norm_hausdorffAtomTerm_le_of_threshold_lt k r hR le_rfl
    (by norm_cast; omega : 1 ≤ 10 * ((k + 1 : ℕ) : ℝ))
    (by linarith only [hpr]) hT hΛ hlamR hthreshold
  have hbase : 41 / 10 * (1 / T ^ 2) = 41 * ((k + 1 : ℕ) : ℝ) * R / r := by
    rw [← hΛ]
    ring
  rw [hbase, thermal_scale_eq_saddle hs hr hbalance] at hbound
  have hexp : -(99 / 100 * (10 * ((k + 1 : ℕ) : ℝ))) = -(99 / 10 * ((k + 1 : ℕ) : ℝ)) := by ring
  rw [hexp] at hbound
  have hratio := thermal_ratio_le (p := k + 1) hr (by linarith only [hpr, hp])
  have hM := realKernel_saddle_pos hs (Nat.succ_pos k) hr hbalance
  have h := mul_le_mul_of_nonneg_left hratio hM.le
  nlinarith only [hbound, h]

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
