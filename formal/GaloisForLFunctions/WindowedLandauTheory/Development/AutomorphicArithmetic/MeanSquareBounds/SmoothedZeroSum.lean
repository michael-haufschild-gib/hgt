import GaloisForLFunctions.ShortIntervalPrimesInProgressions.SiegelWalfisz
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedIdentity

/-! The normalized smoothed zero sum with a logarithmic zero-free region. -/

open Complex GaloisForLFunctions.ShortIntervalPrimesInProgressions

namespace QH

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

theorem zero_distance_of_gap {c lam : ℝ} (hc : 0 < c) (hlam : 1 ≤ lam) {ρ : ℂ}
    (hρ : ρ.re ≤ 1 - c / (lam + Real.log (|ρ.im| + 3))) :
    min (c / 3) 1 / lam ≤ ‖1 - ρ‖ := by
  have hlam₀ : 0 < lam := zero_lt_one.trans_le hlam
  rcases le_or_gt |ρ.im| 1 with him | him
  · have hlog : Real.log (|ρ.im| + 3) ≤ 2 := by
      have h := Real.log_le_log (by positivity : 0 < |ρ.im| + 3) (show |ρ.im| + 3 ≤ 4 by linarith)
      have h₄ : Real.log (4 : ℝ) ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        linarith only [Real.log_two_lt_d9]
      exact h.trans h₄
    have hnorm : 1 - ρ.re ≤ ‖1 - ρ‖ := by simpa using Complex.re_le_norm (1 - ρ)
    calc min (c / 3) 1 / lam ≤ (c / 3) / lam := div_le_div_of_nonneg_right (min_le_left _ _) hlam₀.le
      _ = c / (3 * lam) := by rw [div_div]
      _ ≤ c / (lam + Real.log (|ρ.im| + 3)) := by
        apply div_le_div_of_nonneg_left hc.le
        · have h := Real.log_nonneg (show 1 ≤ |ρ.im| + 3 by linarith [abs_nonneg ρ.im])
          linarith only [h, hlam]
        · linarith only [hlam, hlog]
      _ ≤ ‖1 - ρ‖ := (by linarith only [hρ] : _ ≤ 1 - ρ.re).trans hnorm
  · have hnorm : |ρ.im| ≤ ‖1 - ρ‖ := by simpa using Complex.abs_im_le_norm (1 - ρ)
    calc min (c / 3) 1 / lam ≤ 1 / lam := div_le_div_of_nonneg_right (min_le_right _ _) hlam₀.le
      _ ≤ 1 := (div_le_one hlam₀).mpr hlam
      _ ≤ ‖1 - ρ‖ := him.le.trans hnorm

theorem zeroKernel_sum_le (hχ : χ ≠ 1) (hp : χ.IsPrimitive) {y A E : ℝ} (hy : 1 ≤ y)
    (hA : 1 ≤ A) (hE : 0 ≤ E) {T : ℕ} (hT : 1 ≤ T)
    (hweight : ∀ q : LZero χ, 1 / (‖q.point‖ * ‖1 - q.point‖) ≤ A)
    (hgap : ∀ q : LZero χ, |q.point.im| ≤ T + 1 → y ^ (q.point.re - 1) ≤ E) :
    ‖∑' q : LZero χ, zeroKernel y q.point‖ ≤
      A * (4 * localCountConst N * ((T + 1) * Real.log (T + 3) * E + 8 / Real.sqrt T)) := by
  have hpt (q : LZero χ) : ‖zeroKernel y q.point‖ ≤ A * RHTower.zeroShortWeight y 1 q.point := by
    have h₀ : 0 ≤ 1 / (‖q.point‖ * ‖1 - q.point‖) := by positivity
    have hmin : 1 / (‖q.point‖ * ‖1 - q.point‖) ≤ A * min 1 (1 / (‖q.point‖ * ‖1 - q.point‖)) := by
      rw [mul_min_of_nonneg _ _ (zero_le_one.trans hA), mul_one]
      exact le_min (hweight q) (le_mul_of_one_le_left h₀ hA)
    rw [norm_zeroKernel (zero_lt_one.trans_le hy), RHTower.zeroShortWeight, div_eq_mul_one_div,
      mul_left_comm A]
    exact mul_le_mul_of_nonneg_left hmin (by positivity)
  have hs := (summable_zeroShortWeight hχ hp hy (Y := 1) zero_le_one).mul_left A
  have hn := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hs
  refine (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hpt hs).trans ?_)
  rw [tsum_mul_left]
  have hw := tsum_zeroShortWeight_le_uniform hχ hp hy (Y := 1) zero_le_one hE hT hgap
  exact mul_le_mul_of_nonneg_left (by simpa only [mul_one] using hw) (zero_le_one.trans hA)

theorem exp_zeroKernel_sum_le (hχ : χ ≠ 1) (hp : χ.IsPrimitive) {y c lam A : ℝ}
    (hy : Real.exp 1 ≤ y) (hc : 0 < c) (hlam : 1 ≤ lam) (hA : 1 ≤ A)
    (hweight : ∀ q : LZero χ, 1 / (‖q.point‖ * ‖1 - q.point‖) ≤ A)
    (hgap : ∀ q : LZero χ, q.point.re ≤ 1 - c / (lam + Real.log (|q.point.im| + 3))) :
    ‖∑' q : LZero χ, zeroKernel y q.point‖ ≤
      4 * A * localCountConst N * (14 + 3 * Real.log y) *
        Real.exp (-(min 1 (c / 8) / 2) * Real.log y / (lam + Real.sqrt (Real.log y))) := by
  have hy₀ : 0 < y := (Real.exp_pos _).trans_le hy
  set v := Real.log y with hv
  have hv₁ : 1 ≤ v := (Real.le_log_iff_exp_le hy₀).mpr hy
  have hv₀ : 0 < v := zero_lt_one.trans_le hv₁
  set d := lam + Real.sqrt v with hd
  have hd₀ : 0 < d := by dsimp [d]; positivity
  have hvs : v / d ≤ Real.sqrt v := by
    rw [div_le_iff₀ hd₀, hd, mul_add, Real.mul_self_sqrt hv₀.le]
    exact le_add_of_nonneg_left (by positivity)
  have hs₁ : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr hv₁
  have hd₁ : 1 ≤ d := hlam.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  set a := min 1 (c / 8) with ha
  have ha₀ : 0 < a := lt_min one_pos (by positivity)
  have ha₁ : a ≤ 1 := min_le_left _ _
  have ha₈ : a ≤ c / 8 := min_le_right _ _
  set w := a * (v / d) with hw
  have hw₀ : 0 ≤ w := by positivity
  have hws : w ≤ Real.sqrt v := (mul_le_of_le_one_left (div_nonneg hv₀.le hd₀.le) ha₁).trans hvs
  have hwv : w ≤ v := (mul_le_of_le_one_left (div_nonneg hv₀.le hd₀.le) ha₁).trans
    (div_le_self hv₀.le hd₁)
  set U := Real.exp w with hU
  have hU₁ : 1 ≤ U := Real.one_le_exp hw₀
  let T := ⌈U⌉₊
  have hTU : U ≤ T := Nat.le_ceil U
  have hT₁ : 1 ≤ T := by exact_mod_cast hU₁.trans hTU
  have hTb : (T : ℝ) ≤ U + 1 := (Nat.ceil_lt_add_one (zero_le_one.trans hU₁)).le
  have hlog₆ : Real.log (6 : ℝ) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (6 : ℝ) ≤ (2.7 : ℝ) ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 2
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hlog (z : ℝ) (hz : 0 < z) (hz' : z ≤ (T : ℝ) + 4) : Real.log z ≤ 2 + w := by
    calc Real.log z ≤ Real.log (6 * U) := Real.log_le_log hz (by linarith only [hz', hTb, hU₁])
      _ = Real.log 6 + w := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', hU, Real.log_exp]
      _ ≤ 2 + w := add_le_add_right hlog₆ _
  have hrate (q : LZero χ) (hq : |q.point.im| ≤ T + 1) :
      y ^ (q.point.re - 1) ≤ Real.exp (-(2 * w)) := by
    have hden : 0 < lam + Real.log (|q.point.im| + 3) := by
      have := Real.log_nonneg (show 1 ≤ |q.point.im| + 3 by linarith [abs_nonneg q.point.im])
      linarith
    have hcmp : 2 * (a / d) ≤ c / (lam + Real.log (|q.point.im| + 3)) := by
      have h₁ := hlog (|q.point.im| + 3) (by positivity) (by linarith only [hq])
      have h₂ : lam + Real.log (|q.point.im| + 3) ≤ 4 * d := by
        dsimp [d]
        linarith only [h₁, hws, hs₁, hlam]
      calc 2 * (a / d) ≤ c / (4 * d) := by
            rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
            calc 2 * a / d * (4 * d) = 8 * a := by field_simp; ring
              _ ≤ c := by linarith only [ha₈]
        _ ≤ _ := div_le_div_of_nonneg_left hc.le hden h₂
    rw [Real.rpow_def_of_pos hy₀]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hcmp hv₀.le
    have hz := mul_le_mul_of_nonneg_left (hgap q) hv₀.le
    rw [hw]
    linarith only [hm, hz]
  have hbound := zeroKernel_sum_le hχ hp ((Real.one_le_exp (by norm_num)).trans hy)
    hA (Real.exp_pos _).le hT₁ hweight hrate
  have hlow : ((T : ℝ) + 1) * Real.log (T + 3) * Real.exp (-(2 * w)) ≤
      (6 + 3 * v) * Real.exp (-(w / 2)) := by
    have hcoef : (T : ℝ) + 1 ≤ 3 * U := by linarith only [hTb, hU₁]
    have hlogT : Real.log ((T : ℝ) + 3) ≤ 2 + v :=
      (hlog _ (by positivity) (by linarith)).trans (by linarith only [hwv])
    calc ((T : ℝ) + 1) * Real.log (T + 3) * Real.exp (-(2 * w))
        ≤ (3 * U) * (2 + v) * Real.exp (-(2 * w)) := by gcongr
      _ = (6 + 3 * v) * (U * Real.exp (-(2 * w))) := by ring
      _ = (6 + 3 * v) * Real.exp (-w) := by
        rw [hU, ← Real.exp_add, show w + -(2 * w) = -w by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hw₀])) (by positivity)
  have hhigh : 8 / Real.sqrt (T : ℝ) ≤ 8 * Real.exp (-(w / 2)) := by
    have ht := Real.sqrt_le_sqrt hTU
    have hsqrt : Real.sqrt U = Real.exp (w / 2) := by
      rw [hU, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [hsqrt] at ht
    calc 8 / Real.sqrt (T : ℝ) ≤ 8 / Real.exp (w / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) ht
      _ = _ := by rw [div_eq_mul_inv, Real.exp_neg]
  have hC : 0 ≤ localCountConst N := localCountConst_nonneg (NeZero.pos N)
  refine hbound.trans ?_
  have hsum := add_le_add hlow hhigh
  calc A * (4 * localCountConst N * (((T : ℝ) + 1) * Real.log (T + 3) * Real.exp (-(2 * w)) +
        8 / Real.sqrt (T : ℝ))) ≤ A * (4 * localCountConst N *
          ((6 + 3 * v) * Real.exp (-(w / 2)) + 8 * Real.exp (-(w / 2)))) := by gcongr
    _ = _ := by rw [show -(w / 2) = -(a / 2) * v / d by rw [hw]; ring]; ring

end

end QH
