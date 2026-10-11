import GaloisForLFunctions.RHTower.WeilLogShiftLogTransport

/-! Indexed adjacent logarithmic gaps control the transport deficit. -/

namespace RHTower

theorem finiteWeilClusterLogNodes_adjacent_index_bounds (r k : ℕ) (i : Fin (r + 1)) :
    (((k + 2 : ℕ) : ℝ) + (i : ℕ)) *
        (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc) ≤ 1 ∧
      1 ≤ (((k + 2 : ℕ) : ℝ) + (i : ℕ) + 1) *
        (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc) := by
  let x : ℝ := ((k + 2 + (i.succ : ℕ) : ℕ) : ℝ)
  let y : ℝ := ((k + 2 + (i.castSucc : ℕ) : ℕ) : ℝ)
  have hy : 0 < y := by dsimp [y]; positivity
  have hxy : x = y + 1 := by dsimp [x, y]; push_cast; ring
  have hlog : finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc =
      Real.log x - Real.log y := by
    rw [finiteWeilClusterLogNodes_apply, finiteWeilClusterLogNodes_apply]
    dsimp [x, y]
    ring
  have hp : 0 < finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc :=
    sub_pos.mpr (finiteWeilClusterLogNodes_strictMono r k
      (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))
  have hs := finiteWeil_log_gap_scaled y x x y hy (by linarith only [hxy]) le_rfl le_rfl
    (by linarith only [hxy])
  have hd : |x - y| = 1 := by rw [hxy]; norm_num
  rw [← hlog, abs_of_nonneg hp.le, hd] at hs
  have hyid : y = ((k + 2 : ℕ) : ℝ) + (i : ℕ) := by simp [y]
  simpa only [hxy, hyid] using hs

theorem finiteWeilClusterLogNodes_adjacent_deficit_bounds (r k : ℕ) (i : Fin (r + 1)) :
    ((i : ℕ) : ℝ) ≤ ((k + r + 3 : ℕ) : ℝ) *
        (1 - ((k + 2 : ℕ) : ℝ) *
          (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc)) ∧
      ((k + 2 : ℕ) : ℝ) *
        (1 - ((k + 2 : ℕ) : ℝ) *
          (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc)) ≤
        (i : ℕ) + 1 := by
  let g := finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc
  have hp : 0 < g := sub_pos.mpr (finiteWeilClusterLogNodes_strictMono r k
    (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))
  have hl := finiteWeilClusterLogNodes_adjacent_index_bounds r k i
  have hg := finiteWeilClusterLogNodes_gap_comparison r k i.succ i.castSucc
  have hd : |finiteWeilArithmeticNodes r i.succ - finiteWeilArithmeticNodes r i.castSucc| = 1 := by
    simp [finiteWeilArithmeticNodes]
  change (((k + 2 : ℕ) : ℝ) + (i : ℕ)) * g ≤ 1 ∧
    1 ≤ (((k + 2 : ℕ) : ℝ) + (i : ℕ) + 1) * g at hl
  change ((k + 2 : ℕ) : ℝ) * |g| ≤ _ ∧ _ ≤ ((k + r + 3 : ℕ) : ℝ) * |g| at hg
  rw [abs_of_nonneg hp.le, hd] at hg
  have hleft : (i : ℕ) * g ≤ 1 - ((k + 2 : ℕ) : ℝ) * g := by nlinarith only [hl.1]
  have hright : 1 - ((k + 2 : ℕ) : ℝ) * g ≤ ((i : ℕ) + 1) * g := by nlinarith only [hl.2]
  constructor
  · calc
      ((i : ℕ) : ℝ) ≤ (i : ℕ) * (((k + r + 3 : ℕ) : ℝ) * g) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hg.2 (Nat.cast_nonneg (i : ℕ))
      _ = ((k + r + 3 : ℕ) : ℝ) * ((i : ℕ) * g) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hleft (by positivity)
  · calc
      ((k + 2 : ℕ) : ℝ) * (1 - ((k + 2 : ℕ) : ℝ) * g) ≤
          ((k + 2 : ℕ) : ℝ) * (((i : ℕ) + 1) * g) :=
        mul_le_mul_of_nonneg_left hright (by positivity)
      _ = ((i : ℕ) + 1) * (((k + 2 : ℕ) : ℝ) * g) := by ring
      _ ≤ ((i : ℕ) + 1) * 1 := mul_le_mul_of_nonneg_left hg.1 (by positivity)
      _ = _ := by ring

end RHTower
