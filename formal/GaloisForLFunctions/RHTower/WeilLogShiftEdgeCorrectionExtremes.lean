import GaloisForLFunctions.RHTower.WeilLogShiftEdgeLogCorrection
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialLimit

/-! Edgewise extremes tend to zero and one despite concentration of transport mass at one half. -/

open Filter Topology

namespace RHTower

theorem finiteWeilCanonicalEdgeLogCorrection_first_bound (r k : ℕ) :
    finiteWeilCanonicalEdgeLogCorrection r k 0 ≤ 1 / ((r + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hu := (finiteWeilClusterLogNodes_adjacent_deficit_bounds r k (0 : Fin (r + 1))).2
  simp only [Fin.val_zero, Nat.cast_zero, zero_add] at hu
  have hid : finiteWeilCanonicalEdgeLogCorrection r k 0 =
      (((k + 2 : ℕ) : ℝ) * (1 - ((k + 2 : ℕ) : ℝ) *
        (finiteWeilClusterLogNodes r k (0 : Fin (r + 1)).succ -
          finiteWeilClusterLogNodes r k (0 : Fin (r + 1)).castSucc))) / ((r + 1 : ℕ) : ℝ) := by
    unfold finiteWeilCanonicalEdgeLogCorrection
    ring
  rw [hid]
  exact div_le_div_of_nonneg_right hu hn.le

theorem finiteWeilCanonicalEdgeLogCorrection_last_bound (r k : ℕ)
    (hwidth : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalEdgeLogCorrection r k (Fin.last r) - 1| ≤ 2 / ((r + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hu := (finiteWeilCanonicalEdgeLogCorrection_mem_Icc r k (Fin.last r)).2
  have hl := (abs_le.mp (finiteWeilCanonicalEdgeLogCorrection_scaled_index_bound r k (Fin.last r) hwidth)).1
  simp only [Fin.val_last] at hl
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  apply (le_div_iff₀ hn).mpr
  have hr : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by simp only [Nat.cast_add, Nat.cast_one]
  nlinarith only [hl, hr]

theorem finiteWeil_edge_correction_reciprocal_error (r : ℕ) :
    2 / ((r + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hS : (1 : ℝ) ≤ Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
    have hs0 := Real.sqrt_nonneg ((((r + 1 : ℕ) : ℝ) + 1) / 2)
    have hs2 := Real.sq_sqrt (show 0 ≤ (((r + 1 : ℕ) : ℝ) + 1) / 2 by positivity)
    nlinarith only [hs0, hs2, hn1]
  have h := div_le_div_of_nonneg_right hS hn.le
  calc
    _ = 2 * (1 / ((r + 1 : ℕ) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

theorem tendsto_finiteWeilCanonicalEdgeLogCorrection_first_zero (k : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeLogCorrection r (k r) 0) atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero (g := fun r : ℕ =>
    2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)))
  · intro r
    exact (finiteWeilCanonicalEdgeLogCorrection_mem_Icc r (k r) 0).1
  · intro r
    calc
      _ ≤ 1 / ((r + 1 : ℕ) : ℝ) := finiteWeilCanonicalEdgeLogCorrection_first_bound r (k r)
      _ ≤ 2 / ((r + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ _ := finiteWeil_edge_correction_reciprocal_error r
  · exact tendsto_finiteWeil_midpoint_binomial_error

theorem tendsto_finiteWeilCanonicalEdgeLogCorrection_last_one (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeLogCorrection r (2 * (r + 1) ^ 2 + t r) (Fin.last r))
      atTop (𝓝 (1 : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (g := fun r : ℕ =>
    2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)))
  · intro r
    exact abs_nonneg _
  · intro r
    have hw : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * (r + 1) ^ 2 + t r + 2 : ℕ) : ℝ) := by
      push_cast
      have ht : (0 : ℝ) ≤ (t r : ℝ) := Nat.cast_nonneg _
      nlinarith only [ht, sq_nonneg ((r : ℝ) + 1)]
    exact (finiteWeilCanonicalEdgeLogCorrection_last_bound r _ hw).trans
      (finiteWeil_edge_correction_reciprocal_error r)
  · exact tendsto_finiteWeil_midpoint_binomial_error

end RHTower
