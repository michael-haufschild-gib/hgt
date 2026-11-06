import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.TwoSidedZetaCount

/-!
# Zero counts on the Hausdorff saddle scale

The explicit two-sided zero count gives a uniform lower count in the saddle core and upper counts in
adjacent windows, with absolute constants. Multiplicity copies of both signs are included.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

open _root_.RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry

theorem card_band_eq_twice_count {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((xiCopiesBand a b).card : ℝ) =
      2 * ((xiZeroCount b : ℝ) - (xiZeroCount a : ℝ)) := by
  rw [card_xiCopiesBand_eq_real ha hab,
    xiSymmetricMass_eq_two_mul_xiZeroCount (ha.trans hab),
    xiSymmetricMass_eq_two_mul_xiZeroCount ha]
  push_cast
  ring

/-- `log s ≥ 6` above height `403`. -/
private theorem six_le_log {s : ℝ} (hs : 500 ≤ s) : 6 ≤ Real.log s := by
  have hs0 : 0 < s := by linarith only [hs]
  rw [Real.le_log_iff_exp_le hs0]
  have he : Real.exp 6 = Real.exp 1 ^ 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have h2 : Real.exp 1 ^ 6 ≤ (2.72 : ℝ) ^ 6 := pow_le_pow_left₀ h0.le (by linarith only [h1]) 6
  have h3 : (2.72 : ℝ) ^ 6 ≤ 500 := by norm_num
  rw [he]
  linarith only [h2, h3, hs]

/-- A sufficiently wide saddle core contains a fixed multiple of `w log s` copies. -/
theorem saddle_core_card_lower {s w : ℝ} (hw : 200000 ≤ w) (hws : w ≤ s) :
    w * Real.log s / 1000 ≤ ((xiCopiesBand (s - w / 10) (s + w / 10)).card : ℝ) := by
  have hs : 200000 ≤ s := hw.trans hws
  have hs0 : 0 < s := by linarith only [hs]
  have hw0 : 0 < w := by linarith only [hw]
  have ha20 : 20 ≤ s - w / 10 := by linarith only [hs, hws]
  have ha0 : 0 < s - w / 10 := by linarith only [ha20]
  have hab : s - w / 10 + 3 ≤ s + w / 10 := by linarith only [hw]
  have hlow := le_xiZeroCount_window ha20 hab
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log s := ⟨_, rfl⟩
  have hℓ6 : 6 ≤ ℓ := by rw [hℓ]; exact six_le_log (by linarith only [hs])
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hπu := Real.pi_lt_d2
  have h2π : 0 < 2 * Real.pi := by positivity
  -- The main density at the lower endpoint.
  have hbase : s / 7 ≤ (s - w / 10) / (2 * Real.pi) := by
    rw [le_div_iff₀ h2π]
    have h1 : s / 7 * (2 * Real.pi) ≤ s / 7 * 6.3 :=
      mul_le_mul_of_nonneg_left (by linarith only [hπu]) (by positivity)
    linarith only [h1, hs, hws]
  have hlog7 : Real.log 7 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h2 := Real.exp_one_gt_d9
    rw [h1]
    nlinarith only [h2]
  have hlogbase : ℓ - 2 ≤ Real.log ((s - w / 10) / (2 * Real.pi)) := by
    have h1 := Real.log_le_log (by positivity) hbase
    rw [Real.log_div hs0.ne' (by norm_num), ← hℓ] at h1
    linarith only [h1, hlog7]
  have h6a : 6 / (s - w / 10) ≤ 1 := by
    rw [div_le_one ha0]
    linarith only [ha20]
  have hD : ℓ / (4 * Real.pi) ≤
      (Real.log ((s - w / 10) / (2 * Real.pi)) - 6 / (s - w / 10)) / (2 * Real.pi) := by
    rw [le_div_iff₀ h2π]
    have he : ℓ / (4 * Real.pi) * (2 * Real.pi) = ℓ / 2 := by
      field_simp
      ring
    rw [he]
    linarith only [hlogbase, h6a, hℓ6]
  have hlen : w / 10 ≤ s + w / 10 - (s - w / 10) - 2 := by linarith only [hw]
  have hmain := mul_le_mul hlen hD (by positivity) (by linarith only [hw])
  have hlogb : Real.log (s + w / 10) ≤ 2 * ℓ := by
    have h1 := Real.log_le_log (by positivity) (show s + w / 10 ≤ s * s by nlinarith only [hs, hws])
    rw [Real.log_mul hs0.ne' hs0.ne', ← hℓ] at h1
    linarith only [h1]
  have hmain' : w / 10 * (ℓ / (4 * Real.pi)) = w * ℓ / (40 * Real.pi) := by
    field_simp
    ring
  have hden : w * ℓ / 126 ≤ w * ℓ / (40 * Real.pi) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hπu])
  rw [card_band_eq_twice_count ha0.le (by linarith only [hw]), ← hℓ]
  have hfinal : w * ℓ / 1000 ≤ 2 * (w * ℓ / 126 - 200 * (2 * ℓ) - 1) := by
    have h1 : 0 ≤ ℓ * (w - 200000) := mul_nonneg (by linarith only [hℓ6]) (by linarith only [hw])
    nlinarith only [h1, hℓ6]
  linarith only [hfinal, hden, hmain, hmain', hlow, hlogb]

/-- Every window of length at most `4w` near height `s` has `O(w log s)` copies. -/
theorem saddle_window_card_upper {s w a b : ℝ} (hs : 200 ≤ s) (hw : 1 ≤ w) (ha : s / 16 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 8 * s) (hlen : b - a ≤ 4 * w) :
    ((xiCopiesBand a b).card : ℝ) ≤ 1000 * w * Real.log s := by
  have hs0 : 0 < s := by linarith only [hs]
  have ha10 : 10 ≤ a := by linarith only [hs, ha]
  have ha0 : 0 < a := by linarith only [ha10]
  have hup := xiZeroCount_window_le ha10 hab
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log s := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le hs0]
    linarith only [hs, Real.exp_one_lt_d9]
  have hb2 : Real.log (b + 2) ≤ 2 * ℓ := by
    have h1 := Real.log_le_log (by linarith only [ha0, hab]) (show b + 2 ≤ s * s by nlinarith only [hb, hs])
    rw [Real.log_mul hs0.ne' hs0.ne', ← hℓ] at h1
    linarith only [h1]
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have h2π : 0 < 2 * Real.pi := by positivity
  have hlogdiv : Real.log ((b + 2) / (2 * Real.pi)) ≤ Real.log (b + 2) :=
    Real.log_le_log (div_pos (by linarith only [ha0, hab]) h2π)
      (div_le_self (by linarith only [ha0, hab]) (by linarith only [hπ3]))
  have h6 : 6 / (a - 2) ≤ 1 := by
    rw [div_le_one (by linarith only [ha10])]
    linarith only [ha10]
  have hD : (Real.log ((b + 2) / (2 * Real.pi)) + 6 / (a - 2)) / (2 * Real.pi) ≤ ℓ / 2 := by
    rw [div_le_iff₀ h2π]
    have h1 : ℓ / 2 * (2 * Real.pi) = ℓ * Real.pi := by ring
    rw [h1]
    nlinarith only [hlogdiv, h6, hb2, hℓ1, hπ3]
  have hprod : (b - a + 3) * ((Real.log ((b + 2) / (2 * Real.pi)) + 6 / (a - 2)) / (2 * Real.pi)) ≤
      7 * w * (ℓ / 2) := by
    refine (mul_le_mul_of_nonneg_left hD (by linarith only [hab])).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith only [hlen, hw]) (by linarith only [hℓ1])
  rw [card_band_eq_twice_count ha0.le hab, ← hℓ]
  have hwℓ : 0 ≤ (w - 1) * ℓ := mul_nonneg (by linarith only [hw]) (by linarith only [hℓ1])
  nlinarith only [hup, hprod, hb2, hwℓ, hℓ1]

/-- Radial shells have at most a linear factor in their shell index. -/
theorem radial_shell_card_upper :
    ∀ s w : ℝ,
      200 ≤ s → 1 ≤ w → w ≤ s → ∀ n : ℕ, ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, s / 4 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * s ∧
        ⌊|( |(q.1 : ℂ).im| - s)| / w⌋₊ = n) →
      (F.card : ℝ) ≤ 1000 * ((n : ℝ) + 1) * w * Real.log s := by
  classical
  intro s w hs hw hws n F hF
  have hs0 : 0 < s := by linarith only [hs]
  have hw0 : 0 < w := by linarith only [hw]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hW : 1 ≤ ((n : ℝ) + 1) * w := by
    nlinarith only [mul_nonneg hn0 hw0.le, hw]
  by_cases hF0 : F = ∅
  · rw [hF0]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith only [hs]))
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hF0
  obtain ⟨hlo, hhi, hindex⟩ := hF q₀ hq₀
  have hnlo := Nat.floor_le (div_nonneg (abs_nonneg (|(q₀.1 : ℂ).im| - s)) hw0.le)
  rw [hindex, le_div_iff₀ hw0] at hnlo
  have hd : |( |(q₀.1 : ℂ).im| - s)| ≤ 3 * s := by
    apply abs_le.mpr
    constructor <;> linarith only [hlo, hhi, hs0]
  let a := max (s / 8) (s - ((n : ℝ) + 1) * w - 1)
  let b := s + ((n : ℝ) + 1) * w
  have ha : s / 16 ≤ a := (by linarith only [hs0] : s / 16 ≤ s / 8).trans (le_max_left _ _)
  have hab : a ≤ b := by
    apply max_le
    · dsimp [b]
      linarith only [hs0, hW]
    · dsimp [b]
      linarith only [hW]
  have hb : b ≤ 8 * s := by
    dsimp [b]
    nlinarith only [hnlo, hd, hws, hs0]
  have hlen : b - a ≤ 4 * (((n : ℝ) + 1) * w) := by
    have h := le_max_right (s / 8) (s - ((n : ℝ) + 1) * w - 1)
    change s - ((n : ℝ) + 1) * w - 1 ≤ a at h
    dsimp [b]
    linarith only [h, hW]
  have hsub : F ⊆ xiCopiesBand a b := by
    intro q hq
    obtain ⟨hlo, _, hi⟩ := hF q hq
    have ht := Nat.lt_floor_add_one (|( |(q.1 : ℂ).im| - s)| / w)
    rw [hi, div_lt_iff₀ hw0] at ht
    have hdist := abs_lt.mp ht
    apply mem_xiCopiesBand.mpr
    constructor
    · apply max_lt
      · linarith only [hlo, hs0]
      · linarith only [hdist.1]
    · dsimp [b]
      linarith only [hdist.2]
  have hc : (F.card : ℝ) ≤ ((xiCopiesBand a b).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbound := saddle_window_card_upper hs hW ha hab hb hlen
  calc
    _ ≤ 1000 * (((n : ℝ) + 1) * w) * Real.log s := hc.trans hbound
    _ = _ := by ring

/-- The total number of copies below height `T` is at most `2T log T`, from height `2000`. -/
theorem total_card_upper {T : ℝ} (hT : 2000 ≤ T) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, |(q.1 : ℂ).im| ≤ T) : (F.card : ℝ) ≤ 2 * T * Real.log T := by
  have hT0 : 0 < T := by linarith only [hT]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log T := ⟨_, rfl⟩
  have hℓ6 : 6 ≤ ℓ := by rw [hℓ]; exact six_le_log (by linarith only [hT])
  have hc := card_le_xiSymmetricMass_of_forall_abs_im_le hT0.le hF
  have hm : (xiSymmetricMass T : ℝ) = 2 * (xiZeroCount T : ℝ) := by
    rw [xiSymmetricMass_eq_two_mul_xiZeroCount hT0.le]
    push_cast
    ring
  have hup := xiZeroCount_le_explicit (by linarith only [hT] : 10 ≤ T)
  have hb2 : Real.log (T + 2) ≤ ℓ + 1 := by
    have h1 := Real.log_le_log (by positivity) (show T + 2 ≤ 2 * T by linarith only [hT])
    rw [Real.log_mul (by norm_num) hT0.ne', ← hℓ] at h1
    have h2 := Real.log_two_lt_d9
    linarith only [h1, h2]
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have h2π : 0 < 2 * Real.pi := by positivity
  have hlogdiv : Real.log ((T + 2) / (2 * Real.pi)) ≤ Real.log (T + 2) :=
    Real.log_le_log (div_pos (by positivity) h2π)
      (div_le_self (by positivity) (by linarith only [hπ3]))
  have hD : (Real.log ((T + 2) / (2 * Real.pi)) + 6 / 4) / (2 * Real.pi) ≤ ℓ / 3 := by
    rw [div_le_iff₀ h2π]
    have h1 : ℓ / 3 * (2 * Real.pi) = ℓ * (2 * Real.pi / 3) := by ring
    rw [h1]
    nlinarith only [hlogdiv, hb2, hℓ6, hπ3]
  have hprod := mul_le_mul_of_nonneg_left hD hT0.le
  rw [← hℓ]
  have hT1 : 0 ≤ (T - 2000) * ℓ := mul_nonneg (by linarith only [hT]) (by linarith only [hℓ6])
  nlinarith only [hc, hm, hup, hprod, hb2, hT1, hℓ6]

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
