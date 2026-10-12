import GaloisForLFunctions.RHTower.PaperHeatSliceOperator

/-!
# Exact height cutoffs retain the entire heat-slice defect

At positive heat time a single cutoff retains every Taylor order and radius.
These are continuum multipliers; restricting their height support does not turn
them into finite-rank operators.
-/

namespace RHTower.PaperHeatSlice
noncomputable section
open MeasureTheory Set Filter
open RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open scoped Topology ENNReal NNReal

def cutoffMass (lam : ℝ≥0) (r : Radius) (R : ℝ) : ℝ → ℝ :=
  (Icc (-R) R).indicator (mass lam r)

theorem norm_cutoffMass_le (lam : ℝ≥0) (r : Radius) (R t : ℝ) :
    ‖(cutoffMass lam r R t : ℂ)‖ ≤ massBudget lam r := by
  by_cases ht : t ∈ Icc (-R) R
  · simpa only [cutoffMass, indicator_of_mem ht] using norm_complex_mass_le lam r t
  · simpa only [cutoffMass, indicator_of_notMem ht, Complex.ofReal_zero, norm_zero]
      using massBudget_nonneg lam r

def cutoffOperator (lam : ℝ≥0) (r : Radius) (R : ℝ) : HeightSpace →L[ℂ] HeightSpace :=
  lpBoundedMulCLM (Complex.measurable_ofReal.comp
    ((continuous_mass lam r).measurable.indicator measurableSet_Icc))
      (massBudget_nonneg lam r) (norm_cutoffMass_le lam r R)

theorem cutoffOperator_apply_ae (lam : ℝ≥0) (r : Radius) (R : ℝ) (f : HeightSpace) :
    (cutoffOperator lam r R f : ℝ → ℂ) =ᵐ[volume]
      fun t => (cutoffMass lam r R t : ℂ) * f t := lpBoundedMulCLM_coeFn _ _ _ f

/-- A common compact support for the all-order defect at every Taylor radius. -/
theorem exists_common_compact_support (lam : Radius) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ r : Radius,
      Function.support (mass ⟨lam, lam.property.le⟩ r) ⊆ Icc (-T) T := by
  obtain ⟨T, hT⟩ := exists_mass_support lam
  refine ⟨|T|, abs_nonneg T, fun r t ht => ?_⟩
  by_contra hout
  have htbig : T ≤ |t| := by
    have : ¬ |t| ≤ |T| := by simpa only [abs_le, mem_Icc] using hout
    exact (le_abs_self T).trans (not_le.mp this).le
  exact ht (hT r t htbig)

theorem hasCompactSupport_mass (lam : Radius) (r : Radius) :
    HasCompactSupport (mass ⟨lam, lam.property.le⟩ r) := by
  obtain ⟨T, _, hT⟩ := exists_common_compact_support lam
  exact HasCompactSupport.intro isCompact_Icc fun t ht =>
    Function.notMem_support.mp (fun h => ht (hT r h))

/-- Cutoff equality is uniform over the complete Taylor series and its positive radius. -/
theorem exists_cutoffMass_eq (lam : Radius) :
    ∃ T : ℝ, ∀ R : ℝ, T ≤ R → ∀ r : Radius,
      cutoffMass ⟨lam, lam.property.le⟩ r R = mass ⟨lam, lam.property.le⟩ r := by
  obtain ⟨T, _, hT⟩ := exists_common_compact_support lam
  refine ⟨T, fun R hR r => ?_⟩
  funext t
  by_cases ht : t ∈ Icc (-R) R
  · exact indicator_of_mem ht _
  · rw [cutoffMass, indicator_of_notMem ht]
    symm
    apply Function.notMem_support.mp
    intro h
    have hm := hT r h
    exact ht ⟨by linarith [hm.1], hm.2.trans hR⟩

/-- Literal continuum operators eventually agree exactly, rather than merely in a limit. -/
theorem exists_cutoffOperator_eq (lam : Radius) :
    ∃ T : ℝ, ∀ R : ℝ, T ≤ R → ∀ r : Radius,
      cutoffOperator ⟨lam, lam.property.le⟩ r R = massOperator ⟨lam, lam.property.le⟩ r := by
  obtain ⟨T, hT⟩ := exists_cutoffMass_eq lam
  refine ⟨T, fun R hR r => ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [cutoffOperator_apply_ae _ r R f, massOperator_apply_ae _ r f] with t ht hs
  rw [ht, hs, hT R hR r]

/-- Large height windows have the exact same ideal cost as the full continuum source. -/
theorem exists_cutoffOperator_traceCost (lam : Radius) :
    ∃ T : ℝ, ∀ R : ℝ, T ≤ R → ∀ r : Radius,
      compactOperatorTraceCost HeightSpace (cutoffOperator ⟨lam, lam.property.le⟩ r R) =
        if newmanConstant ≤ (lam : ℝ) then 0 else ∞ := by
  obtain ⟨T, hT⟩ := exists_cutoffOperator_eq lam
  exact ⟨T, fun R hR r => by rw [hT R hR r, massOperator_traceCost]; rfl⟩

end
end RHTower.PaperHeatSlice
