import GaloisForLFunctions.HTGeometry.SecondCenteredModularAbel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Full logarithmic half-order response of a finite period

For two zero-mean finite channels with their exact discrete primitives, the
response to the original logarithmic coefficient has leading term equal to
the first primitive's period sum. Every fixed-phase half-order gap has the
same limiting normalization. A coarse uniform clock bound controls the
logarithmic shift remainder; no numerical approximation is used.

The actual arithmetic channels and their zero-mean identities are supplied
in `RoutePTwoPrimePacketTimeResponse`. This finite-period limit makes no
claim about a growing packet or the complete Route-P history floor.
-/

noncomputable section
open Finset Filter Topology HTGeometry
namespace RHTower

private theorem sqrt_shift_ratio (a : ℕ) :
    Tendsto (fun B : ℕ => Real.sqrt (B + a : ℕ) / Real.sqrt B) atTop (𝓝 1) := by
  have hi : Tendsto (fun B : ℕ => (B : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
    (hi.const_mul (a : ℝ))).sqrt
  simp only [mul_zero, add_zero, Real.sqrt_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with B hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  rw [← Real.sqrt_div (Nat.cast_nonneg (B + a))]
  congr 1
  push_cast
  field_simp

private theorem sqrt_pair_ratio (i j a b : ℕ) :
    Tendsto (fun B : ℕ =>
      (Real.sqrt (B + i : ℕ) + Real.sqrt (B + j : ℕ)) /
        (Real.sqrt (B + a : ℕ) + Real.sqrt (B + b : ℕ))) atTop (𝓝 1) := by
  have h := ((sqrt_shift_ratio i).add (sqrt_shift_ratio j)).div
    ((sqrt_shift_ratio a).add (sqrt_shift_ratio b)) (by norm_num : (1 : ℝ) + 1 ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with B hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hs : Real.sqrt (B : ℝ) ≠ 0 := (Real.sqrt_pos.2 hB0).ne'
  have hd : Real.sqrt (B + a : ℕ) + Real.sqrt (B + b : ℕ) ≠ 0 := by
    have ha : (0 : ℝ) < (B + a : ℕ) := by exact_mod_cast (show 0 < B + a by omega)
    exact (add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 ha) (Real.sqrt_nonneg _)).ne'
  simp only [Pi.div_apply, Nat.cast_add] at hd ⊢
  field_simp

private theorem clock_gap_positive (B k : ℕ) :
    0 < halfOrderAbelStep B k - halfOrderAbelStep B (k + 1) := by
  rw [halfOrderAbelStep_gap_eq]
  positivity

/-- Every fixed phase has the same limiting half-order gap as the period origin. -/
theorem routeP_halfOrder_gap_ratio (k : ℕ) :
    Tendsto (fun B : ℕ =>
      (halfOrderAbelStep B k - halfOrderAbelStep B (k + 1)) /
        (halfOrderAbelStep B 0 - halfOrderAbelStep B 1)) atTop (𝓝 1) := by
  have h := ((sqrt_pair_ratio 0 1 k (k + 1)).mul
    (sqrt_pair_ratio 1 2 (k + 1) (k + 2))).mul
      (sqrt_pair_ratio 0 2 k (k + 2))
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [] with B
  simp only [halfOrderAbelStep_gap_eq, Nat.add_zero, Nat.add_assoc]
  field_simp

private theorem finite_abel (u P w : ℕ → ℝ) (hzero : P 0 = 0)
    (hstep : ∀ k, P (k + 1) - P k = u k) (N : ℕ) :
    (∑ k ∈ range N, u k * w k) =
      (∑ k ∈ range N, P (k + 1) * (w k - w (k + 1))) + P N * w N := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have h := congrArg (fun x : ℝ => x * w N) (hstep N)
    nlinarith only [h]

/-- Full-period response is governed by the exact primitive mean. -/
theorem routeP_finite_halfOrder_response_limit (u P : ℕ → ℝ) (N : ℕ)
    (hzero : P 0 = 0) (hstep : ∀ k, P (k + 1) - P k = u k) (hperiod : P N = 0) :
    Tendsto (fun B : ℕ => (∑ k ∈ range N, u k * halfOrderAbelStep B k) /
      (halfOrderAbelStep B 0 - halfOrderAbelStep B 1)) atTop
        (𝓝 (∑ k ∈ range N, P (k + 1))) := by
  have h := tendsto_finsetSum (range N) (fun k _ =>
    (routeP_halfOrder_gap_ratio k).const_mul (P (k + 1)))
  simp only [mul_one] at h
  convert h using 1
  ext B
  rw [finite_abel u P _ hzero hstep N, hperiod, zero_mul, add_zero, sum_div]
  apply sum_congr rfl
  intro k _
  ring

private theorem clock_over_gap_bound {B : ℕ} (hB : 1 ≤ B) (k : ℕ) :
    halfOrderAbelStep B k / (halfOrderAbelStep B 0 - halfOrderAbelStep B 1) ≤
      6 * (B : ℝ) := by
  have hg := clock_gap_positive B 0
  have hw := halfOrderAbelStep_antitone B (Nat.zero_le k)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have ha := Real.sqrt_nonneg (B : ℝ)
  have hb := Real.sqrt_nonneg (B + 1 : ℕ)
  have hc := Real.sqrt_nonneg (B + 2 : ℕ)
  have hab : Real.sqrt (B : ℝ) ≤ Real.sqrt (B + 2 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show B ≤ B + 2 by omega))
  have hbc : Real.sqrt (B + 1 : ℕ) ≤ Real.sqrt (B + 2 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show B + 1 ≤ B + 2 by omega))
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (B + 2))
  have hunit : halfOrderAbelStep B 0 *
      (Real.sqrt B + Real.sqrt (B + 1 : ℕ)) = 1 := by
    have hs0 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) B)
    have hs1 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (B + 1))
    simp only [halfOrderAbelStep, Nat.add_zero]
    push_cast at hs1 ⊢
    nlinarith only [hs0, hs1]
  have he : halfOrderAbelStep B 0 / (halfOrderAbelStep B 0 - halfOrderAbelStep B 1) =
      (Real.sqrt (B + 1 : ℕ) + Real.sqrt (B + 2 : ℕ)) *
        (Real.sqrt B + Real.sqrt (B + 2 : ℕ)) / 2 := by
    rw [show halfOrderAbelStep B 1 = halfOrderAbelStep B (0 + 1) by rfl,
      halfOrderAbelStep_gap_eq]
    simp only [Nat.add_zero]
    have h := congrArg (fun x : ℝ => x *
      (Real.sqrt (B + 1 : ℕ) + Real.sqrt (B + 2 : ℕ)) *
      (Real.sqrt B + Real.sqrt (B + 2 : ℕ)) / 2) hunit
    field_simp at h ⊢
    nlinarith only [h]
  calc
    _ ≤ halfOrderAbelStep B 0 / (halfOrderAbelStep B 0 - halfOrderAbelStep B 1) :=
      div_le_div_of_nonneg_right hw hg.le
    _ = _ := he
    _ ≤ (2 * Real.sqrt (B + 2 : ℕ)) * (2 * Real.sqrt (B + 2 : ℕ)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul (by linarith) (by linarith) (add_nonneg ha hc) (by positivity)
    _ ≤ 6 * (B : ℝ) := by
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
      push_cast at hsq ⊢
      nlinarith only [hsq, hB1]

private theorem log_shift_clock_bound {B : ℕ} (hB : 1 ≤ B) (k : ℕ) :
    0 ≤ (Real.log (B + k : ℕ) - Real.log B) * halfOrderAbelStep B k /
      (halfOrderAbelStep B 0 - halfOrderAbelStep B 1) ∧
    (Real.log (B + k : ℕ) - Real.log B) * halfOrderAbelStep B k /
      (halfOrderAbelStep B 0 - halfOrderAbelStep B 1) ≤ 6 * (k : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hBk0 : (0 : ℝ) < (B + k : ℕ) := by exact_mod_cast (show 0 < B + k by omega)
  have hdiff0 : 0 ≤ Real.log (B + k : ℕ) - Real.log B := sub_nonneg.mpr
    (Real.log_le_log hB0 (by exact_mod_cast Nat.le_add_right B k))
  have hdiff : Real.log (B + k : ℕ) - Real.log B ≤ (k : ℝ) / B := by
    rw [← Real.log_div hBk0.ne' hB0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hBk0 hB0)
    have he : ((B + k : ℕ) : ℝ) / B - 1 = (k : ℝ) / B := by
      push_cast
      field_simp
      ring
    exact h.trans_eq he
  have hg := clock_gap_positive B 0
  have hw0 := halfOrderAbelStep_nonneg B k
  refine ⟨div_nonneg (mul_nonneg hdiff0 hw0) hg.le, ?_⟩
  rw [mul_div_assoc]
  calc
    _ ≤ ((k : ℝ) / B) * (6 * (B : ℝ)) :=
      mul_le_mul hdiff (clock_over_gap_bound hB k)
        (div_nonneg hw0 hg.le) (div_nonneg (Nat.cast_nonneg k) hB0.le)
    _ = 6 * (k : ℝ) := by field_simp

private theorem inverse_log_limit :
    Tendsto (fun B : ℕ => (Real.log B)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem log_shift_clock_limit (k : ℕ) :
    Tendsto (fun B : ℕ =>
      (Real.log (B + k : ℕ) - Real.log B) * halfOrderAbelStep B k /
        (halfOrderAbelStep B 0 - halfOrderAbelStep B 1) / Real.log B) atTop (𝓝 0) := by
  have hbound := inverse_log_limit.const_mul (6 * (k : ℝ))
  simp only [mul_zero] at hbound
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with B hB
    exact div_nonneg (log_shift_clock_bound (by omega) k).1
      (Real.log_pos (by exact_mod_cast (show 1 < B by omega))).le
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with B hB
    simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right
      (log_shift_clock_bound (by omega) k).2
      (Real.log_pos (by exact_mod_cast (show 1 < B by omega))).le

/-- The original logarithm and its fixed offset do not change the leading full-period
primitive mean. Both zero-mean channels and all original time coefficients are retained. -/
theorem routeP_finite_log_halfOrder_response_limit (u v P Q : ℕ → ℝ) (N : ℕ)
    (hP0 : P 0 = 0) (hPstep : ∀ k, P (k + 1) - P k = u k) (hPN : P N = 0)
    (hQ0 : Q 0 = 0) (hQstep : ∀ k, Q (k + 1) - Q k = v k) (hQN : Q N = 0) :
    Tendsto (fun B : ℕ =>
      (∑ k ∈ range N, (Real.log (B + k : ℕ) * u k - v k) * halfOrderAbelStep B k) /
        (Real.log B * (halfOrderAbelStep B 0 - halfOrderAbelStep B 1))) atTop
      (𝓝 (∑ k ∈ range N, P (k + 1))) := by
  have hU := routeP_finite_halfOrder_response_limit u P N hP0 hPstep hPN
  have hV := routeP_finite_halfOrder_response_limit v Q N hQ0 hQstep hQN
  have hR := tendsto_finsetSum (range N) (fun k _ => (log_shift_clock_limit k).const_mul (u k))
  simp only [mul_zero, sum_const_zero] at hR
  have h := (hU.sub (hV.mul inverse_log_limit)).add hR
  simp only [mul_zero, sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with B hB
  have hlog : Real.log (B : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega))).ne'
  have hgap := (clock_gap_positive B 0).ne'
  simp only [sum_div, sum_mul,
    ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  field_simp
  ring

end RHTower
