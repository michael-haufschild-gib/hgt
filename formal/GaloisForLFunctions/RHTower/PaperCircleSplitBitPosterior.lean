import GaloisForLFunctions.RHTower.PaperCircleSplitFisherOverlap

/-! # The actual posterior branch bit after a native observation

The child histogram ratios form a strictly positive binary probability law. Its
joint-law identity identifies it as the posterior of the cell's branch bit given
the next native observation. The source Fisher information is its mean squared
contrast, and the overlap is four times its mean binary variance.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleHistorySplitBitPosterior (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) : Law Bool := by
  let c := paperCircleHistoryCellScene a l r k i s
  let K := Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)
  refine ⟨fun b => hist (c.smaller b) K z / (2 * hist c K z), ?_, ?_⟩
  · intro b
    exact (div_pos (paperCircleHistorySplit_child_hist_pos a l r k i s t b z)
      (mul_pos (by norm_num) (paperCircleHistorySplit_hist_pos a l r k i s t z))).le
  · rw [Fintype.sum_bool, ← add_div]
    have h := hist_split c i.isLt (by change l < l+r+10; omega) K z
    rw [add_comm, h]
    exact div_self (mul_pos (by norm_num : (0 : ℝ) < 2)
      (paperCircleHistorySplit_hist_pos a l r k i s t z)).ne'

theorem paperCircleHistorySplitBitPosterior_apply (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) (b : Bool) :
    paperCircleHistorySplitBitPosterior a l r k i s t z b =
      hist ((paperCircleHistoryCellScene a l r k i s).smaller b)
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z /
      (2 * hist (paperCircleHistoryCellScene a l r k i s)
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z) := rfl

theorem paperCircleHistorySplitBitPosterior_pos (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) (b : Bool) :
    0 < paperCircleHistorySplitBitPosterior a l r k i s t z b :=
  div_pos (paperCircleHistorySplit_child_hist_pos a l r k i s t b z)
    (mul_pos (by norm_num) (paperCircleHistorySplit_hist_pos a l r k i s t z))

theorem paperCircleHistorySplitBitPosterior_lt_one (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) (b : Bool) :
    paperCircleHistorySplitBitPosterior a l r k i s t z b < 1 := by
  have ht := (paperCircleHistorySplitBitPosterior a l r k i s t z).total
  simp only [Fintype.sum_bool] at ht
  have h0 := paperCircleHistorySplitBitPosterior_pos a l r k i s t z false
  have h1 := paperCircleHistorySplitBitPosterior_pos a l r k i s t z true
  cases b <;> linarith

private lemma native_hist (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (t : ℝ≥0) (z : Grid (l+r+10)) :
    hist (paperCircleHistoryCellScene a l r k i s)
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)) z =
    ((paperCircleHistoryCellPosterior a l r k i s).through
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))) z := by
  rw [hist_source _ _ (paperCircleObservationCell_ok l r i)
    (fun x => (paperCircleHistoryLikelihood_pos a (l+r+10) k s x).le),
    paperCircleHistoryCellScene_norm,
    div_self (paperCircleHistoryCellScene_mass_pos a l r k i s).ne', one_mul,
    paperCircleHistoryCellScene_actor]

/-- Observation mass times posterior bit probability is the actual joint mass. -/
theorem paperCircleHistorySplitBitPosterior_joint (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0)
    (z : Grid (l+r+10)) (b : Bool) :
    ((paperCircleHistoryCellPosterior a l r k i s).through
      (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))) z *
      paperCircleHistorySplitBitPosterior a l r k i s t z b =
    (paperCircleHistoryCellPosterior a l r k i s).Ex (fun x =>
      if decide (x ∈ (paperCircleObservationCell l i).R.block (l+r+10)) = b then
        Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t) x z else 0) := by
  let c := paperCircleHistoryCellScene a l r k i s
  let K := Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t)
  have hp := paperCircleObservationCell_ok l r i
  have hd : c.here.lev < l+r+10 := by change l < l+r+10; omega
  have hw : 0 ≤ c.wage := fun x => (paperCircleHistoryLikelihood_pos a (l+r+10) k s x).le
  have hm : 0 < c.mass := paperCircleHistoryCellScene_mass_pos a l r k i s
  have hn : c.norm = c.mass := paperCircleHistoryCellScene_norm a l r k i s
  have ht : (Fork.step c).TrueLaw := paperCircleHistoryCellScene_split_law a l r k i s
  have hc := hist_source K (c.smaller b) (Node.child_ok c.here hp.1 hd b) hw z
  change hist (c.smaller b) K z =
    ((c.smaller b).mass / c.norm) * (c.smaller b).actor.through K z at hc
  rw [hn, Fork.step_mass ht b] at hc
  have he : c.actor.Ex (fun x => if (Fork.step c).bit x = b then K x z else 0) =
      (Fork.step c).probs b * (c.smaller b).actor.through K z := by
    rw [Law.through_apply]
    unfold Law.Ex
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hb := Fork.local_law ht b x
    change (Fork.step c).probs b * (c.smaller b).actor x =
      (if (Fork.step c).bit x = b then c.actor x else 0) at hb
    dsimp only
    rw [← mul_assoc, hb]
    split_ifs <;> ring
  rw [← paperCircleHistoryCellScene_actor a l r k i s]
  change c.actor.through K z * (hist (c.smaller b) K z / (2 * hist c K z)) =
    c.actor.Ex (fun x => if (Fork.step c).bit x = b then K x z else 0)
  have hpar : hist c K z = c.actor.through K z := by
    rw [hist_source K c hp hw z, hn, div_self hm.ne', one_mul]
  rw [← hpar, he, hc]
  have hz : 0 < hist c K z := paperCircleHistorySplit_hist_pos a l r k i s t z
  field_simp [hm.ne', hz.ne']

/-- The source Fisher signal is exactly the mean squared posterior branch contrast. -/
theorem paperCircleHistorySplit_fisher_posterior_contrast (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitFisher a l r k i s t =
      ((paperCircleHistoryCellPosterior a l r k i s).through
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex
        (fun z => (paperCircleHistorySplitBitPosterior a l r k i s t z false -
          paperCircleHistorySplitBitPosterior a l r k i s t z true)^2) := by
  unfold paperCircleHistorySplitFisher fisher Law.Ex
  apply Finset.sum_congr rfl
  intro z _
  rw [← native_hist a l r k i s t z]
  simp only [paperCircleHistorySplitBitPosterior_apply]
  unfold diff
  field_simp [(paperCircleHistorySplit_hist_pos a l r k i s t z).ne']

/-- The remaining overlap is four times the mean posterior Bernoulli variance. -/
theorem paperCircleHistorySplit_overlap_posterior_variance (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) (t : ℝ≥0) :
    paperCircleHistorySplitOverlap a l r k i s t =
      4 * ((paperCircleHistoryCellPosterior a l r k i s).through
        (Thermal.channel (paperCircleLocalizedForm a (l+r+10) k t))).Ex
        (fun z => paperCircleHistorySplitBitPosterior a l r k i s t z false *
          paperCircleHistorySplitBitPosterior a l r k i s t z true) := by
  unfold paperCircleHistorySplitOverlap Law.Ex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [← native_hist a l r k i s t z]
  simp only [paperCircleHistorySplitBitPosterior_apply]
  field_simp [(paperCircleHistorySplit_hist_pos a l r k i s t z).ne']
  ring

end
end RHTower
