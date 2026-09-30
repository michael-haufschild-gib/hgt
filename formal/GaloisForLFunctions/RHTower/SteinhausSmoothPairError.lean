import GaloisForLFunctions.RHTower.SteinhausEulerRoughCount
import GaloisForLFunctions.RHTower.SteinhausEulerSmoothSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open Filter
open scoped Topology

noncomputable section
namespace RHTower

private theorem inv_le_half_product {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (had : a ≤ d) (hbd : b ≤ d) :
    d⁻¹ ≤ a ^ (-(1 / 2 : ℝ)) * b ^ (-(1 / 2 : ℝ)) := by
  have hd := ha.trans_le had
  calc
    d⁻¹ = d ^ (-(1 / 2 : ℝ)) * d ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hd]
      norm_num [Real.rpow_neg_one]
    _ ≤ _ := mul_le_mul
      (Real.rpow_le_rpow_of_nonpos ha had (by norm_num))
      (Real.rpow_le_rpow_of_nonpos hb hbd (by norm_num))
      (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg ha.le _)

/-- Absolute summability of the actual smooth-pair majorant at the critical line. -/
theorem summable_steinhausSmoothPair_majorant (y : ℕ) :
    Summable (fun ac : Nat.smoothNumbers y × Nat.smoothNumbers y =>
      (ac.1 : ℝ) ^ (-(1 / 2 : ℝ)) * (ac.2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have h := summable_smoothNumbers_neg_rpow y (σ := 1 / 2) (by norm_num)
  exact h.mul_of_nonneg h (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The literal rough-count error is dominated by a summable smooth-pair majorant. -/
theorem abs_roughCount_smoothPair_error_le (y N : ℕ) (a c : Nat.smoothNumbers y) :
    |(roughCount (Nat.primesBelow y) ((N : ℝ) / (max (a : ℕ) (c : ℕ) : ℕ)) : ℝ) / N -
      (steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹ /
        (max (a : ℕ) (c : ℕ) : ℕ)| ≤
      (1 + |(steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹|) *
        ((a : ℝ) ^ (-(1 / 2 : ℝ)) * (c : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let d : ℝ := (max (a : ℕ) (c : ℕ) : ℕ)
  let α : ℝ := (steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹
  let r : ℝ := (roughCount (Nat.primesBelow y) ((N : ℝ) / d) : ℝ) / N
  have ha : 0 < (a : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers a.property)
  have hc : 0 < (c : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers c.property)
  have had : (a : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast le_max_left (a : ℕ) (c : ℕ)
  have hcd : (c : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast le_max_right (a : ℕ) (c : ℕ)
  have hd : 0 < d := ha.trans_le had
  have hr : 0 ≤ r := by positivity
  have hrle : r ≤ 1 / d := by
    by_cases hN : N = 0
    · simp only [r, hN, Nat.cast_zero, div_zero]
      positivity
    · exact roughCount_scaled_div_le (Nat.primesBelow y)
        (by exact_mod_cast Nat.pos_of_ne_zero hN) hd
  change |r - α / d| ≤ _
  calc
    |r - α / d| ≤ |r| + |α / d| := abs_sub _ _
    _ = r + |α| / d := by rw [abs_of_nonneg hr, abs_div, abs_of_pos hd]
    _ ≤ 1 / d + |α| / d := by linarith
    _ = (1 + |α|) * d⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_le_half_product ha hc had hcd) (by positivity)

/-- Deterministic total pair error between the arithmetic kernel and its limiting maximum kernel. -/
def steinhausSmoothPairCountError (y N : ℕ) : ℝ :=
  ∑' ac : Nat.smoothNumbers y × Nat.smoothNumbers y,
    |(roughCount (Nat.primesBelow y) ((N : ℝ) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) : ℝ) / N -
      (steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹ /
        (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)|

/-- Every finite arithmetic cutoff has an absolutely summable coefficient-error series. -/
theorem summable_steinhausSmoothPair_countError (y N : ℕ) :
    Summable (fun ac : Nat.smoothNumbers y × Nat.smoothNumbers y =>
      |(roughCount (Nat.primesBelow y) ((N : ℝ) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) : ℝ) / N -
        (steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹ /
          (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)|) := by
  exact ((summable_steinhausSmoothPair_majorant y).mul_left
    (1 + |(steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹|)).of_nonneg_of_le
      (fun _ => abs_nonneg _) (fun ac => abs_roughCount_smoothPair_error_le y N ac.1 ac.2)

theorem steinhausSmoothPairCountError_nonneg (y N : ℕ) :
    0 ≤ steinhausSmoothPairCountError y N := tsum_nonneg (fun _ => abs_nonneg _)

/-- The deterministic error vanishes at fixed prime cutoff, uniformly over all Steinhaus phases. -/
theorem tendsto_steinhausSmoothPairCountError (y : ℕ) :
    Tendsto (steinhausSmoothPairCountError y) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_steinhausSmoothPair_majorant y).mul_left
      (1 + |(steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹|))
    (fun ac : Nat.smoothNumbers y × Nat.smoothNumbers y => by
      have hc : Tendsto (fun _ : ℕ =>
          (steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹ /
            (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) atTop
          (𝓝 ((steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹ /
            (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ))) := tendsto_const_nhds
      simpa only [sub_self, abs_zero] using
        ((tendsto_roughCount_smoothPair_div y ac.1 ac.2).sub hc).abs)
    (Filter.Eventually.of_forall (fun N ac => by
      simpa only [Real.norm_eq_abs, abs_abs] using
        abs_roughCount_smoothPair_error_le y N ac.1 ac.2))
  unfold steinhausSmoothPairCountError
  simpa only [tsum_zero] using h

end RHTower
