import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity
import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower

/-!
# Zero counts on the Hausdorff saddle scale

The logarithmic remainder in the Riemann--von Mangoldt formula gives a
uniform lower count in the saddle core and upper counts in adjacent windows.
Multiplicity copies of both signs are included.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

open _root_.RHTower

theorem card_band_eq_twice_count {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((xiCopiesBand a b).card : ℝ) =
      2 * ((xiZeroCount b : ℝ) - (xiZeroCount a : ℝ)) := by
  rw [card_xiCopiesBand_eq_real ha hab,
    xiSymmetricMass_eq_two_mul_xiZeroCount (ha.trans hab),
    xiSymmetricMass_eq_two_mul_xiZeroCount ha]
  push_cast
  ring

/-- A sufficiently wide saddle core contains a fixed multiple of `w log s` copies. -/
theorem exists_saddle_core_card_lower :
    ∃ S : ℝ, 4 ≤ S ∧ ∃ W : ℝ, 1 ≤ W ∧ ∀ s w : ℝ, S ≤ s → W ≤ w → w ≤ s →
      w * Real.log s / 1000 ≤ ((xiCopiesBand (s - w / 10) (s + w / 10)).card : ℝ) := by
  obtain ⟨C, hC, T₀, hT₀, hrem⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨max (2 * T₀) ((4 * Real.pi) ^ 2), ?_, max 1 (160 * Real.pi * C),
    le_max_left _ _, ?_⟩
  · exact (by linarith only [hT₀] : 4 ≤ 2 * T₀).trans (le_max_left _ _)
  intro s w hs hw hws
  have hsT := (le_max_left _ _).trans hs
  have hsπ := (le_max_right _ _).trans hs
  have hw1 : 1 ≤ w := (le_max_left _ _).trans hw
  have hwC : 160 * Real.pi * C ≤ w := (le_max_right _ _).trans hw
  have hs0 : 0 < s := by linarith only [hsT, hT₀]
  have ha0 : 0 < s - w / 10 := by linarith only [hs0, hws]
  have hb0 : 0 < s + w / 10 := by linarith only [hs0, hw1]
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith only [hsT, hT₀])
  have ha := abs_le.mp (hrem (s - w / 10) (by linarith only [hsT, hws]))
  have hb := abs_le.mp (hrem (s + w / 10) (by linarith only [hsT, hw1, hT₀]))
  have hlogπ : 2 * Real.log (4 * Real.pi) ≤ Real.log s := by
    have h := Real.log_le_log (by positivity) hsπ
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hlog4π : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [show (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hloghalf := Real.log_le_log (by positivity : 0 < s / 2)
    (show s / 2 ≤ s - w / 10 by linarith only [hws])
  rw [Real.log_div hs0.ne' (by norm_num)] at hloghalf
  have hhalf : Real.log s / 2 ≤ Real.log (s - w / 10) - Real.log (2 * Real.pi) := by
    linarith only [hloghalf, hlogπ, hlog4π]
  have hlog2 : Real.log 2 ≤ Real.log s :=
    Real.log_le_log (by norm_num) (by linarith only [hsT, hT₀])
  have hloga : Real.log (s - w / 10) ≤ 2 * Real.log s := by
    have h := Real.log_le_log ha0 (show s - w / 10 ≤ s by linarith only [hw1])
    linarith only [h, hlogs]
  have hlogb : Real.log (s + w / 10) ≤ 2 * Real.log s := by
    have h := Real.log_le_log hb0 (show s + w / 10 ≤ 2 * s by linarith only [hws, hs0])
    rw [Real.log_mul (by norm_num) hs0.ne'] at h
    linarith only [h, hlog2]
  have hmain := routeKSmoothRVMCount_sub_ge ha0
    (show s - w / 10 ≤ s + w / 10 by linarith only [hw1])
  have hmain' : w * Real.log s / (20 * Real.pi) ≤
      routeKSmoothRVMCount (s + w / 10) - routeKSmoothRVMCount (s - w / 10) := by
    have h := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ w / 5 by linarith only [hw1])
    have h' := div_le_div_of_nonneg_right h (show 0 ≤ 2 * Real.pi by positivity)
    have heq : (w / 5 * (Real.log s / 2)) / (2 * Real.pi) =
        w * Real.log s / (20 * Real.pi) := by ring
    rw [heq] at h'
    exact h'.trans (by convert hmain using 1 <;> ring)
  have hcost : 4 * C * Real.log s ≤ w * Real.log s / (40 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 40 * Real.pi)]
    have h := mul_le_mul_of_nonneg_right hwC hlogs
    nlinarith only [h]
  have hca := mul_le_mul_of_nonneg_left hloga hC.le
  have hcb := mul_le_mul_of_nonneg_left hlogb hC.le
  have hcount : w * Real.log s / (40 * Real.pi) ≤
      (xiZeroCount (s + w / 10) : ℝ) - (xiZeroCount (s - w / 10) : ℝ) := by
    have heq : w * Real.log s / (20 * Real.pi) =
        2 * (w * Real.log s / (40 * Real.pi)) := by ring
    rw [heq] at hmain'
    linarith only [hmain', hcost, hca, hcb, ha.2, hb.1]
  rw [card_band_eq_twice_count ha0.le (by linarith only [hw1])]
  have hsmall : w * Real.log s / 1000 ≤ 2 * (w * Real.log s / (40 * Real.pi)) := by
    have hden : 40 * Real.pi ≤ 2000 := by linarith only [Real.pi_lt_four]
    have h := div_le_div_of_nonneg_left (mul_nonneg (by linarith only [hw1]) hlogs)
      (show 0 < 40 * Real.pi by positivity) hden
    linarith only [h]
  linarith only [hsmall, hcount]

/-- Every window of length at most `4w` near height `s` has `O(w log s)` copies. -/
theorem exists_saddle_window_card_upper :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ S : ℝ, 16 ≤ S ∧ ∀ s w a b : ℝ,
      S ≤ s → 1 ≤ w → s / 16 ≤ a → a ≤ b → b ≤ 8 * s → b - a ≤ 4 * w →
      ((xiCopiesBand a b).card : ℝ) ≤ C * w * Real.log s := by
  obtain ⟨C, hC, T₀, hT₀, hceil⟩ := exists_xiZeroCount_window_le
  refine ⟨16 + 8 * C, by linarith only [hC], 16 * T₀,
    by linarith only [hT₀], ?_⟩
  intro s w a b hs hw ha hab hb hlen
  have hs0 : 0 < s := by linarith only [hs, hT₀]
  have ha0 : 0 < a := by linarith only [ha, hs0]
  have hb0 : 0 < b := ha0.trans_le hab
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith only [hs, hT₀])
  have hlog8 : Real.log 8 ≤ Real.log s :=
    Real.log_le_log (by norm_num) (by linarith only [hs, hT₀])
  have hlogb : Real.log b ≤ 2 * Real.log s := by
    have h := Real.log_le_log hb0 hb
    rw [Real.log_mul (by norm_num) hs0.ne'] at h
    linarith only [h, hlog8]
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith only [ha, hs, hT₀, hab])
  have hN := hceil a (by linarith only [ha, hs]) (b - a) (sub_nonneg.mpr hab)
  rw [add_sub_cancel] at hN
  have hden : (b - a) / (2 * Real.pi) ≤ 4 * w := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi)]
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ 2 * Real.pi by linarith only [Real.pi_gt_three])
      (show 0 ≤ 4 * w by linarith only [hw])
    linarith only [h, hlen]
  have hm := mul_le_mul hden hlogb hlogb0 (show 0 ≤ 4 * w by linarith only [hw])
  have hc := mul_le_mul_of_nonneg_left hlogb (show 0 ≤ 2 * C by positivity)
  have hwc := mul_le_mul_of_nonneg_left hw (show 0 ≤ 4 * C * Real.log s by positivity)
  rw [card_band_eq_twice_count ha0.le hab]
  nlinarith only [hN, hm, hc, hwc]

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
