import GaloisForLFunctions.RHTower.PaperCircleObservationHistory

/-! # Quantitative evidence in every native dyadic cell

The source posterior-denominator theorem applies to every observation history.
A canonical comparison form pays its spatial and history-domination requirements;
the cell's first grid point pays admissibility with its actual observed energy.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleObservationCell (l : ℕ) (i : Fin (2^l)) : Node := ⟨l, i⟩

theorem paperCircleObservationCell_ok (l r : ℕ) (i : Fin (2^l)) :
    (paperCircleObservationCell l i).ok (l+r+10) :=
  ⟨i.isLt, by change l ≤ l+r+10; omega⟩

theorem paperCircleObservationCell_scale (l r : ℕ) (i : Fin (2^l)) :
    1000 * (paperCircleObservationCell l i).invlen ≤ (2:ℝ)^(l+r+10) := by
  change 1000 * (2:ℝ)^l ≤ _
  rw [pow_add, pow_add]
  have h : 1 ≤ (2:ℝ)^r := one_le_pow₀ (by norm_num)
  have hp : 0 < (2:ℝ)^l := pow_pos (by norm_num) _
  norm_num
  nlinarith

def paperCircleHistoryComparisonForm (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) : Thermal.Form (l+r+10) :=
  Thermal.S (l+r+10) (1000 * (paperCircleObservationCell l i).invlen) +
    (2:ℝ) • Thermal.mixForm (paperCircleObservationProfile a (l+r+10) k s)

def paperCircleHistoryCellEvidence (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) : ℝ :=
  expU (Thermal.prefixE (paperCircleObservationProfile a (l+r+10) k s)
    (paperCircleObservationCell l i))

/-- Every source premise is supplied by the native construction and the actual energy at the cell start. -/
theorem paperCircleHistoryCellEvidence_lower (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    Real.exp (-(2 * Thermal.sumE (paperCircleObservationProfile a (l+r+10) k s)
      ((paperCircleObservationCell l i).start (l+r+10))) -
        Thermal.F (paperCircleHistoryComparisonForm a l r k i s)) / 4 ≤
      paperCircleHistoryCellEvidence a l r k i s := by
  have hp := paperCircleObservationCell_ok l r i
  have hn := paperCircleObservationProfile_nonneg a (l+r+10) k s
  apply Thermal.posterior_denominator hp
  · exact le_add_of_nonneg_right (fun x =>
      mul_nonneg (by norm_num) (Thermal.mix_nonneg hn x))
  · exact paperCircleObservationCell_scale l r i
  · exact ⟨_, Node.start_mem hp.1 hp.2, le_rfl⟩
  · exact hn
  · exact le_add_of_nonneg_left (Thermal.S_nonneg _ _)

theorem paperCircleHistoryCellEvidence_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    0 < paperCircleHistoryCellEvidence a l r k i s :=
  lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num))
    (paperCircleHistoryCellEvidence_lower a l r k i s)

theorem paperCircleHistoryCellEvidence_le (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    paperCircleHistoryCellEvidence a l r k i s ≤ paperCircleHistoryEvidence a (l+r+10) k s := by
  apply expU_mono
  intro x
  unfold Thermal.prefixE
  split_ifs
  · exact le_rfl
  · exact (paperCircleHistoryLikelihood_pos a (l+r+10) k s x).le

/-- Exact posterior probability of the cell: localized evidence divided by total evidence. -/
theorem paperCircleHistoryPosterior_cell (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    (paperCircleHistoryPosterior a (l+r+10) k s).prob
      (fun x => x ∈ (paperCircleObservationCell l i).block (l+r+10)) =
        paperCircleHistoryCellEvidence a l r k i s / paperCircleHistoryEvidence a (l+r+10) k s := by
  classical
  rw [Law.prob_eq]
  simp only [paperCircleHistoryPosterior_apply, paperCircleHistoryCellEvidence,
    expU, smul_eq_mul, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  unfold Thermal.prefixE
  split_ifs <;> simp [paperCircleHistoryLikelihood]

theorem paperCircleHistoryPosterior_cell_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    0 < (paperCircleHistoryPosterior a (l+r+10) k s).prob
      (fun x => x ∈ (paperCircleObservationCell l i).block (l+r+10)) := by
  rw [paperCircleHistoryPosterior_cell]
  exact div_pos (paperCircleHistoryCellEvidence_pos a l r k i s)
    (paperCircleHistoryEvidence_pos a (l+r+10) k s)

/-- A quantitative mass guarantee for every cell, with no feasibility assumption on the history. -/
theorem paperCircleHistoryPosterior_cell_lower (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    Real.exp (-(2 * Thermal.sumE (paperCircleObservationProfile a (l+r+10) k s)
      ((paperCircleObservationCell l i).start (l+r+10))) -
        Thermal.F (paperCircleHistoryComparisonForm a l r k i s)) / 4 ≤
      (paperCircleHistoryPosterior a (l+r+10) k s).prob
        (fun x => x ∈ (paperCircleObservationCell l i).block (l+r+10)) := by
  rw [paperCircleHistoryPosterior_cell]
  apply (paperCircleHistoryCellEvidence_lower a l r k i s).trans
  apply (le_div_iff₀ (paperCircleHistoryEvidence_pos a (l+r+10) k s)).mpr
  exact mul_le_of_le_one_right (paperCircleHistoryCellEvidence_pos a l r k i s).le
    (paperCircleHistoryEvidence_le_one a (l+r+10) k s)

end
end RHTower
