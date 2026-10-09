import GaloisForLFunctions.RHTower.PaperCirclePosteriorSplitInformation
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Plateau.Features

/-! # Strict Fisher range and the exact overlap of native child observations

Both children retain positive observation mass at every output. Their overlap is
exactly the gap between the native split Fisher information and one. This sharpens
the source range estimate and gives an explicit positive measure of the remaining
ambiguity between the two children.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

private lemma positive_hist {M : ℕ} (c : Scene M) (hp : c.here.ok M)
    (hw : ∀ x, 0 < c.wage x) (hn : 0 < c.norm) (A : Thermal.Form M) (z : Grid M) :
    0 < hist c (Thermal.channel A) z := by
  unfold hist
  apply Finset.sum_pos'
  · intro x _
    exact mul_nonneg (Thermal.wt_nonneg _ (fun x => (hw x).le) hn.le x)
      (Thermal.ch_pos A x z).le
  · refine ⟨c.here.start M, Finset.mem_univ _, ?_⟩
    apply mul_pos _ (Thermal.ch_pos A _ z)
    exact div_pos (mul_pos ((Node.dice_positive hp).mpr (Node.start_mem hp.1 hp.2))
      (hw _)) hn

theorem paperCircleHistorySplit_hist_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z : Grid (l+r+10)) :
    0 < hist (paperCircleHistoryCellScene a l r k i s)
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z := by
  apply positive_hist _ (paperCircleObservationCell_ok l r i)
    (paperCircleHistoryLikelihood_pos a (l+r+10) k s)
  rw [paperCircleHistoryCellScene_norm]
  exact paperCircleHistoryCellScene_mass_pos a l r k i s

theorem paperCircleHistorySplit_child_hist_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (b : Bool) (z : Grid (l+r+10)) :
    0 < hist ((paperCircleHistoryCellScene a l r k i s).smaller b)
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z := by
  apply positive_hist _ (Node.child_ok (paperCircleObservationCell l i) i.isLt
    (by change l < l+r+10; omega) b)
    (paperCircleHistoryLikelihood_pos a (l+r+10) k s)
  change 0 < (paperCircleHistoryCellScene a l r k i s).norm
  rw [paperCircleHistoryCellScene_norm]
  exact paperCircleHistoryCellScene_mass_pos a l r k i s

theorem paperCircleHistorySplit_hist_total (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    (∑ z, hist (paperCircleHistoryCellScene a l r k i s)
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z) = 1 := by
  rw [total_hist _ (paperCircleObservationCell_ok l r i), share,
    paperCircleHistoryCellScene_norm,
    div_self (paperCircleHistoryCellScene_mass_pos a l r k i s).ne']

/-- The source range theorem sharpens the earlier entropy-only bound. -/
theorem paperCircleHistorySplit_fisher_le_one (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitFisher a l r k i s t ≤ 1 := by
  have hn : 0 ≤ (paperCircleHistoryCellScene a l r k i s).norm := by
    rw [paperCircleHistoryCellScene_norm]
    exact (paperCircleHistoryCellScene_mass_pos a l r k i s).le
  have h := (fisher_range (paperCircleHistoryCellScene a l r k i s) i.isLt
    (by change l < l+r+10; omega)
    (fun x => (paperCircleHistoryLikelihood_pos a (l+r+10) k s x).le) hn
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).2
  unfold paperCircleHistorySplitFisher
  simpa only [share, paperCircleHistoryCellScene_norm,
    div_self (paperCircleHistoryCellScene_mass_pos a l r k i s).ne'] using h

/-- Normalized overlap of the two child observation profiles. -/
def paperCircleHistorySplitOverlap (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) : ℝ :=
  let c := paperCircleHistoryCellScene a l r k i s
  let K := Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)
  ∑ z, hist (c.smaller false) K z * hist (c.smaller true) K z / hist c K z

/-- The entire missing Fisher information is accounted for by child overlap. -/
theorem paperCircleHistorySplit_fisher_add_overlap (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitFisher a l r k i s t +
      paperCircleHistorySplitOverlap a l r k i s t = 1 := by
  unfold paperCircleHistorySplitFisher paperCircleHistorySplitOverlap fisher
  rw [← Finset.sum_add_distrib, ← paperCircleHistorySplit_hist_total a l r k i s t]
  apply Finset.sum_congr rfl
  intro z _
  have hp := paperCircleHistorySplit_hist_pos a l r k i s t z
  have hs := hist_split (paperCircleHistoryCellScene a l r k i s) i.isLt
    (by change l < l+r+10; omega)
    (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z
  have hs2 := congrArg (fun x : ℝ => x^2) hs
  unfold diff
  field_simp [hp.ne']
  nlinarith [hs2]

theorem paperCircleHistorySplitOverlap_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    0 < paperCircleHistorySplitOverlap a l r k i s t := by
  have h (z : Grid (l+r+10)) :
      0 < hist ((paperCircleHistoryCellScene a l r k i s).smaller false)
          (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z *
        hist ((paperCircleHistoryCellScene a l r k i s).smaller true)
          (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z /
        hist (paperCircleHistoryCellScene a l r k i s)
          (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z :=
    div_pos (mul_pos (paperCircleHistorySplit_child_hist_pos a l r k i s t false z)
      (paperCircleHistorySplit_child_hist_pos a l r k i s t true z))
      (paperCircleHistorySplit_hist_pos a l r k i s t z)
  exact Finset.sum_pos' (fun z _ => (h z).le) ⟨0, Finset.mem_univ _, h 0⟩

/-- Native positive observation kernels never attain perfect child separation. -/
theorem paperCircleHistorySplit_fisher_lt_one (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitFisher a l r k i s t < 1 := by
  linarith [paperCircleHistorySplit_fisher_add_overlap a l r k i s t,
    paperCircleHistorySplitOverlap_pos a l r k i s t]

theorem paperCircleHistorySplitOverlap_le_one (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitOverlap a l r k i s t ≤ 1 := by
  linarith [paperCircleHistorySplit_fisher_add_overlap a l r k i s t,
    paperCircleHistorySplit_fisher_nonneg a l r k i s t]

end
end RHTower
