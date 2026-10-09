import GaloisForLFunctions.RHTower.PaperCircleCellPosterior
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Procedure.Deficit

/-! # Information budgets for splitting an actual native posterior

The source actor is identified with the history posterior conditioned on a cell.
Its dyadic split obeys an exact conditional entropy identity and spends entropy
deficit at a rate controlled by its observable Fisher information.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleHistoryCellScene (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) : Scene (l+r+10) :=
  { here := paperCircleObservationCell l i
    wage := paperCircleHistoryLikelihood a (l+r+10) k s
    fund := Fund.initial (l+r+10)
    live := true
    norm := paperCircleHistoryCellEvidence a l r k i s / (paperCircleObservationCell l i).len }

theorem paperCircleHistoryCellScene_mass (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    (paperCircleHistoryCellScene a l r k i s).mass =
      paperCircleHistoryCellEvidence a l r k i s / (paperCircleObservationCell l i).len :=
  paperCircleHistoryCellEvidence_avg a l r k i s

theorem paperCircleHistoryCellScene_mass_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    0 < (paperCircleHistoryCellScene a l r k i s).mass := by
  rw [paperCircleHistoryCellScene_mass]
  exact div_pos (paperCircleHistoryCellEvidence_pos a l r k i s) (paperCircleObservationCell l i).len_pos

theorem paperCircleHistoryCellScene_norm (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    (paperCircleHistoryCellScene a l r k i s).norm =
      (paperCircleHistoryCellScene a l r k i s).mass :=
  (paperCircleHistoryCellScene_mass a l r k i s).symm

private theorem cell_wage_nonneg (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    0 ≤ (paperCircleHistoryCellScene a l r k i s).wage :=
  fun x => (paperCircleHistoryLikelihood_pos a (l+r+10) k s x).le

theorem paperCircleHistoryCellScene_actor (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    (paperCircleHistoryCellScene a l r k i s).actor = paperCircleHistoryCellPosterior a l r k i s := by
  apply Law.ext
  intro x
  rw [Scene.actor_def (paperCircleObservationCell_ok l r i) (cell_wage_nonneg a l r k i s)
    (paperCircleHistoryCellScene_mass_pos a l r k i s) x, Thermal.wt]
  change (paperCircleObservationCell l i).dice (l+r+10) x *
    paperCircleHistoryLikelihood a (l+r+10) k s x /
      (paperCircleObservationCell l i).avg (paperCircleHistoryLikelihood a (l+r+10) k s) = _
  rw [paperCircleHistoryCellEvidence_avg, paperCircleHistoryCellPosterior_density]
  field_simp [(paperCircleObservationCell l i).len_pos.ne',
    (paperCircleHistoryCellEvidence_pos a l r k i s).ne']

theorem paperCircleHistoryCellScene_split_law (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    (Fork.step (paperCircleHistoryCellScene a l r k i s)).TrueLaw :=
  Fork.step_true i.isLt (by change l < l+r+10; omega) (cell_wage_nonneg a l r k i s)
    (paperCircleHistoryCellScene_mass_pos a l r k i s)

private theorem cell_levels (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    levels (paperCircleHistoryCellScene a l r k i s) = (r+10 : ℕ) * Real.log 2 := by
  change ((l+r+10-l : ℕ) : ℝ) * Real.log 2 = _
  congr 2
  omega

theorem paperCircleHistoryCellPosterior_entropy_le (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    (paperCircleHistoryCellPosterior a l r k i s).entropy ≤ (r+10 : ℕ) * Real.log 2 := by
  have h := cap_entropy (paperCircleHistoryCellScene a l r k i s)
    (paperCircleObservationCell_ok l r i) (cell_wage_nonneg a l r k i s)
    (paperCircleHistoryCellScene_mass_pos a l r k i s)
  rwa [paperCircleHistoryCellScene_actor, cell_levels] at h

def paperCircleHistorySplitFisher (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) : ℝ :=
  fisher (paperCircleHistoryCellScene a l r k i s)
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))

def paperCircleHistorySplitEntropy (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) : ℝ :=
  ((paperCircleHistoryCellPosterior a l r k i s).withNext
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Hcond
      (fun v => decide (v.1 ∈ (paperCircleObservationCell l i).R.block (l+r+10))) Prod.snd

private theorem sideH_eq_native (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    sideH (Fork.step (paperCircleHistoryCellScene a l r k i s))
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) =
        paperCircleHistorySplitEntropy a l r k i s t := by
  unfold sideH Fork.step
  simp only [paperCircleHistoryCellScene_actor]
  rfl

/-- Conditional entropy splits exactly between the selected child and its observed branch bit. -/
theorem paperCircleHistorySplit_entropy_balance (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    (Fork.step (paperCircleHistoryCellScene a l r k i s)).probs.Ex
      (fun b => ((paperCircleHistoryCellScene a l r k i s).smaller b).actor.privateH
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))) +
      paperCircleHistorySplitEntropy a l r k i s t =
        (paperCircleHistoryCellPosterior a l r k i s).privateH
          (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) := by
  have h := conditioned_balance (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))
    _ (paperCircleHistoryCellScene_split_law a l r k i s)
  rw [sideH_eq_native] at h
  change _ + _ = (paperCircleHistoryCellScene a l r k i s).actor.privateH _ at h
  rwa [paperCircleHistoryCellScene_actor] at h

/-- The branch information visible through a native observation pays for its Fisher signal. -/
theorem paperCircleHistorySplit_fisher_entropy (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitFisher a l r k i s t ≤
      4 * (Real.log 2 - paperCircleHistorySplitEntropy a l r k i s t) := by
  have hn := paperCircleHistoryCellScene_norm a l r k i s
  have hm := paperCircleHistoryCellScene_mass_pos a l r k i s
  have h := bit_def (paperCircleHistoryCellScene a l r k i s)
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) i.isLt
    (by change l < l+r+10; omega) (cell_wage_nonneg a l r k i s) hm (hn.symm ▸ hm)
  rwa [hn, div_self hm.ne', one_mul, sideH_eq_native] at h

theorem paperCircleHistorySplit_fisher_nonneg (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    0 ≤ paperCircleHistorySplitFisher a l r k i s t := by
  apply Finset.sum_nonneg
  intro x _
  apply div_nonneg (sq_nonneg _)
  rw [hist_source _ _ (paperCircleObservationCell_ok l r i) (cell_wage_nonneg a l r k i s),
    paperCircleHistoryCellScene_norm, div_self (paperCircleHistoryCellScene_mass_pos a l r k i s).ne',
    one_mul]
  exact Law.nonneg _ _

theorem paperCircleHistorySplit_fisher_bound (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitFisher a l r k i s t ≤ 4 * Real.log 2 := by
  have h := paperCircleHistorySplit_fisher_entropy a l r k i s t
  have hn : 0 ≤ paperCircleHistorySplitEntropy a l r k i s t := Law.Hcond_nonneg _ _ _
  linarith

/-- Expected remaining deficit plus the Fisher expenditure cannot exceed the parent's deficit. -/
theorem paperCircleHistorySplit_deficit_budget (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    (Fork.step (paperCircleHistoryCellScene a l r k i s)).probs.Ex
      (fun b => deficit ((paperCircleHistoryCellScene a l r k i s).smaller b)
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))) +
      paperCircleHistorySplitFisher a l r k i s t / 4 ≤
        (r+10 : ℕ) * Real.log 2 - (paperCircleHistoryCellPosterior a l r k i s).privateH
          (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) := by
  have hn := paperCircleHistoryCellScene_norm a l r k i s
  have hm := paperCircleHistoryCellScene_mass_pos a l r k i s
  have h := space_deficit (paperCircleHistoryCellScene a l r k i s)
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) i.isLt
    (by change l < l+r+10; omega) (cell_wage_nonneg a l r k i s) hm (hn.symm ▸ hm)
  rw [hn, div_self hm.ne', mul_one, deficit, cell_levels, paperCircleHistoryCellScene_actor] at h
  unfold paperCircleHistorySplitFisher
  convert h using 1
  ring

end
end RHTower
