import GaloisForLFunctions.RHTower.PaperWoldCompositeIdeal
import GaloisForLFunctions.HTGeometry.CompactObserverTraceBlindness

/-! # Literal finite cutoffs of the bounded critical composite operator

All finite observations have zero paper ideal cost. Their uniformly bounded
operators converge on every history, but stay a fixed norm distance from the
complete noncompact arithmetic operator.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal

private abbrev compositeCutoffProjection (N : ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  coordTruncation (Finset.range N)

private theorem compositeCutoffProjection_apply (N : ℕ) (f : PaperWoldHistory) (n : ℕ) :
    compositeCutoffProjection N f n = if n < N then f n else 0 := by
  rw [compositeCutoffProjection, coordTruncation_apply]
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single,
    Finset.mem_range]

private theorem compositeCutoffProjection_single (N j : ℕ) :
    compositeCutoffProjection N (lp.single 2 j (1 : ℂ)) =
      if j < N then lp.single 2 j (1 : ℂ) else 0 := by
  apply lp.ext
  funext n
  by_cases hj : j < N
  · rw [if_pos hj, compositeCutoffProjection_apply]
    by_cases hn : n < N
    · rw [if_pos hn]
    · rw [if_neg hn, lp.single_apply_ne _ _ _ (by omega : n ≠ j)]
  · rw [if_neg hj, compositeCutoffProjection_apply]
    by_cases hn : n < N
    · rw [if_pos hn, lp.single_apply_ne _ _ _ (by omega : n ≠ j)]
      rfl
    · rw [if_neg hn]
      rfl

private theorem compositeCutoffProjection_tendsto (f : PaperWoldHistory) :
    Tendsto (fun N => compositeCutoffProjection N f) atTop (𝓝 f) := by
  simpa only [compositeCutoffProjection, coordTruncation_apply] using
    (lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) f).tendsto_sum_nat

/-- The literal square cutoff, with original entries on all retained composite coordinates. -/
def paperWoldCriticalCompositeCutoff (N : ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  compositeCutoffProjection N ∘L (paperWoldCriticalCompositeOperator ∘L compositeCutoffProjection N)

theorem paperWoldCriticalCompositeCutoff_single (N n j : ℕ) :
    paperWoldCriticalCompositeCutoff N (lp.single 2 j (1 : ℂ)) n =
      if n < N ∧ j < N then paperWoldCompositeEntry (1 / 2) n j else 0 := by
  simp only [paperWoldCriticalCompositeCutoff, ContinuousLinearMap.comp_apply,
    compositeCutoffProjection_single]
  by_cases hj : j < N
  · rw [if_pos hj, compositeCutoffProjection_apply, paperWoldCriticalCompositeOperator_single]
    simp only [hj, and_true]
  · simp only [hj, if_false, map_zero, lp.coeFn_zero, Pi.zero_apply, and_false]

theorem paperWoldCriticalCompositeCutoff_compact (N : ℕ) :
    IsCompactOperator (paperWoldCriticalCompositeCutoff N) := by
  have hP : IsCompactOperator (compositeCutoffProjection N) :=
    (memSchattenClass_one_sum_rankOne (Finset.range N) lpBasisVec lpBasisVec).isCompactOperator one_pos
  exact hP.comp_clm (paperWoldCriticalCompositeOperator ∘L compositeCutoffProjection N)

theorem paperWoldCriticalCompositeCutoff_norm_le (N : ℕ) :
    ‖paperWoldCriticalCompositeCutoff N‖ ≤ 5 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  exact (norm_coordTruncation_apply_le _ _).trans
    ((paperWoldCriticalCompositeOperator.le_opNorm _).trans
      (mul_le_mul paperWoldCriticalCompositeOperator_norm_le
        (norm_coordTruncation_apply_le _ _) (norm_nonneg _) (by norm_num)))

theorem paperWoldCriticalCompositeCutoff_traceCost (N : ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCriticalCompositeCutoff N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldCriticalCompositeCutoff_compact N)

theorem paperWoldCriticalCompositeCutoff_norm_gap (N : ℕ) :
    (1 / 24 : ℝ) ≤ ‖paperWoldCriticalCompositeOperator - paperWoldCriticalCompositeCutoff N‖ :=
  paperWoldCriticalCompositeOperator_norm_sub_compact_floor
    ⟨paperWoldCriticalCompositeCutoff N, paperWoldCriticalCompositeCutoff_compact N⟩

/-- Complete vectorwise convergence coexists with a fixed operator-norm gap and an ideal-cost jump. -/
theorem paperWoldCriticalCompositeCutoff_strong_tendsto (f : PaperWoldHistory) :
    Tendsto (fun N => paperWoldCriticalCompositeCutoff N f) atTop
      (𝓝 (paperWoldCriticalCompositeOperator f)) := by
  have hp (x : PaperWoldHistory) :
      Tendsto (fun N => ‖compositeCutoffProjection N x - x‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((compositeCutoffProjection_tendsto x).sub (tendsto_const_nhds (x := x))).norm
  have hbound (N : ℕ) :
      ‖paperWoldCriticalCompositeCutoff N f - paperWoldCriticalCompositeOperator f‖ ≤
        5 * ‖compositeCutoffProjection N f - f‖ +
          ‖compositeCutoffProjection N (paperWoldCriticalCompositeOperator f) -
            paperWoldCriticalCompositeOperator f‖ := by
    apply (norm_sub_le_norm_sub_add_norm_sub _
      (compositeCutoffProjection N (paperWoldCriticalCompositeOperator f)) _).trans
    apply add_le_add _ le_rfl
    change ‖compositeCutoffProjection N (paperWoldCriticalCompositeOperator (compositeCutoffProjection N f)) -
      compositeCutoffProjection N (paperWoldCriticalCompositeOperator f)‖ ≤ _
    rw [← map_sub, ← map_sub]
    exact (norm_coordTruncation_apply_le _ _).trans
      ((paperWoldCriticalCompositeOperator.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right paperWoldCriticalCompositeOperator_norm_le (norm_nonneg _)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _) hbound
  simpa only [mul_zero, add_zero] using
    ((hp f).const_mul 5).add (hp (paperWoldCriticalCompositeOperator f))

end
end RHTower
