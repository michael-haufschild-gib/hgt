import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroHeightTail
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedIdentity

/-! Real-part and height truncation for absolutely summable Cesàro zero kernels. -/

open Complex Finset

noncomputable section

namespace QH.PrimeProgressions

private theorem height_tail_scalars {T : ℝ} (hT : 2 ≤ T) :
    let L := ⌊T⌋₊ - 1
    1 ≤ L ∧ 2 * (Real.log (4 * (L : ℝ)) + 2) / L ≤ 48 * Real.log T / T := by
  let L := ⌊T⌋₊ - 1
  have hfl : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
  have hL : 1 ≤ L := by dsimp [L]; omega
  refine ⟨hL, ?_⟩
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hLdef : (L : ℝ) = ⌊T⌋₊ - 1 := by dsimp [L]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hLT : (L : ℝ) ≤ T := by linarith [Nat.floor_le (by linarith : 0 ≤ T)]
  have hTL : T ≤ 3 * (L : ℝ) := by linarith [Nat.lt_floor_add_one T]
  have hlog : Real.log (4 * (L : ℝ)) ≤ 3 * Real.log T := by
    refine (Real.log_le_log (by positivity) (show 4 * (L : ℝ) ≤ 4 * T by linarith)).trans ?_
    rw [Real.log_mul (by norm_num) (by linarith : T ≠ 0)]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT]
  have hlogT : (1 : ℝ) / 2 ≤ Real.log T :=
    (by linarith [Real.log_two_gt_d9] : (1 : ℝ) / 2 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hT)
  calc 2 * (Real.log (4 * (L : ℝ)) + 2) / L ≤ (14 * Real.log T) / L :=
        div_le_div_of_nonneg_right (by linarith) hLpos.le
    _ ≤ (14 * Real.log T) / (T / 3) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    _ ≤ _ := by
      rw [show 14 * Real.log T / (T / 3) = 42 * Real.log T / T by ring]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- A bound for the reciprocal zero mass controls real-part truncation. A logarithmic bound
in each unit height interval controls the discarded high zeros. -/
theorem normalized_zero_truncation {ι : Type*} (point : ι → ℂ)
    (hre : ∀ q, (point q).re ≤ 1) {A B : ℝ}
    (hs : Summable (fun q => 1 / (‖point q‖ * ‖1 - point q‖)))
    (hsum : (∑' q, 1 / (‖point q‖ * ‖1 - point q‖)) ≤ A) (hB : 0 ≤ B)
    (hcount : ∀ (F : Finset ι) (n : ℕ),
      ((F.filter (fun q => ⌊|(point q).im|⌋₊ = n)).card : ℝ) ≤ B * Real.log ((n : ℝ) + 3))
    {y κ T : ℝ} (hy : 1 ≤ y) (hT : 2 ≤ T) :
    ‖∑' q : ι,
      if 1 - κ < (point q).re ∧ |(point q).im| ≤ T then 0 else QH.zeroKernel y (point q)‖ ≤
        A * y ^ (-κ) + B * (48 * Real.log T / T) := by
  let b (q : ι) := 1 / (‖(point q)‖ * ‖1 - (point q)‖)
  let a (q : ι) := ‖QH.zeroKernel y (point q)‖
  have aye (q : ι) : a q = y ^ ((point q).re - 1) * b q := by
    dsimp only [a, b]
    rw [QH.norm_zeroKernel (zero_lt_one.trans_le hy), div_eq_mul_one_div]
  have hb (q : ι) : 0 ≤ b q := by dsimp [b]; positivity
  have hab (q : ι) : a q ≤ b q := by
    rw [aye]
    exact mul_le_of_le_one_left (hb q)
      (Real.rpow_le_one_of_one_le_of_nonpos hy (sub_nonpos.mpr (hre q)))
  have hsa : Summable a := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hab hs
  let low (q : ι) := if (point q).re ≤ 1 - κ then a q else 0
  have hlow (q : ι) : low q ≤ y ^ (-κ) * b q := by
    dsimp only [low]
    split_ifs with h
    · rw [aye]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hy (by linarith)) (hb q)
    · positivity
  have hSL : Summable low :=
    Summable.of_nonneg_of_le (fun q => by dsimp [low]; split_ifs <;> positivity) hlow (hs.mul_left _)
  have hL : ∑' q, low q ≤ A * y ^ (-κ) := by
    refine (hSL.tsum_le_tsum hlow (hs.mul_left _)).trans ?_
    rw [tsum_mul_left]
    calc y ^ (-κ) * ∑' q, b q ≤ y ^ (-κ) * A :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  let L : ℕ := ⌊T⌋₊ - 1
  let height (q : ι) := ⌊|(point q).im|⌋₊
  let high (q : ι) := if L < height q then a q else 0
  have hL1 : 1 ≤ L := (height_tail_scalars hT).1
  have hhigh (q : ι) (h : L < height q) : a q ≤ (height q : ℝ) ^ (-2 : ℝ) := by
    have hm0 : (0 : ℝ) < height q := by exact_mod_cast (show 0 < height q by omega)
    have hm : (height q : ℝ) ≤ |(point q).im| := Nat.floor_le (abs_nonneg _)
    have h₁ : |(point q).im| ≤ ‖(point q)‖ := abs_im_le_norm _
    have h₂ : |(point q).im| ≤ ‖1 - (point q)‖ := by simpa using abs_im_le_norm (1 - (point q))
    have hprod : (height q : ℝ) ^ 2 ≤ ‖(point q)‖ * ‖1 - (point q)‖ := by
      rw [pow_two]
      exact mul_le_mul (hm.trans h₁) (hm.trans h₂) hm0.le (norm_nonneg _)
    refine (hab q).trans ?_
    dsimp [b]
    rw [Real.rpow_neg hm0.le, Real.rpow_two, ← one_div]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hm0) hprod
  have hH : (∑' q, high q) ≤ B * (48 * Real.log T / T) :=
    (tsum_height_tail_le height a hsa (fun q => norm_nonneg _) hB hcount hL1 hhigh).trans
      (mul_le_mul_of_nonneg_left (height_tail_scalars hT).2 hB)
  have hhigh_nonneg (q : ι) : 0 ≤ high q := by
    dsimp only [high]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hSH : Summable high :=
    Summable.of_nonneg_of_le hhigh_nonneg (fun q => by
      dsimp only [high]
      split_ifs
      · exact le_rfl
      · exact norm_nonneg _) hsa
  let f (q : ι) := if 1 - κ < (point q).re ∧ |(point q).im| ≤ T then 0 else QH.zeroKernel y (point q)
  have hf (q : ι) : ‖f q‖ ≤ low q + high q := by
    by_cases hr : 1 - κ < (point q).re
    · by_cases ht : |(point q).im| ≤ T
      · simpa only [f, hr, ht, and_self, if_true, norm_zero, low, if_neg hr.not_ge, zero_add] using hhigh_nonneg q
      · have hn : ⌊T⌋₊ ≤ height q := Nat.floor_mono (lt_of_not_ge ht).le
        have hT1 : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
        have hk : L < height q := by dsimp [L]; omega
        simp [f, ht, hr, low, high, hk, hr.not_ge, a]
    · simpa only [f, hr, false_and, if_false, low, if_pos (le_of_not_gt hr), a, le_add_iff_nonneg_right]
        using hhigh_nonneg q
  have hSf := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf (hSL.add hSH)
  refine (norm_tsum_le_tsum_norm hSf).trans ((hSf.tsum_le_tsum hf (hSL.add hSH)).trans ?_)
  rw [hSL.tsum_add hSH]
  exact add_le_add hL hH

end QH.PrimeProgressions
