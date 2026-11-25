import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # A null image with finite boundary in physical time has finitely many values -/

open Set Filter Topology MeasureTheory Metric
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

private theorem equal_on_interval {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ}
    (hz : volume (f '' S)=0) {l r : ℝ} (hlr : l≤r) (hI : Icc l r⊆S) : f l=f r := by
  have null_interval {a b : ℝ} (hab : a<b) (hs : Icc a b⊆f '' Icc l r) : False := by
    have h := measure_mono_null (hs.trans (image_mono hI)) hz
    rw [Real.volume_Icc,ENNReal.ofReal_eq_zero] at h
    linarith only [hab,h]
  exact le_antisymm
    (le_of_not_gt fun h => null_interval h (intermediate_value_Icc' hlr hf.continuousOn))
    (le_of_not_gt fun h => null_interval h (intermediate_value_Icc hlr hf.continuousOn))

/-- Every value first attained on the compact observation interval is
already attained at its left endpoint or on the boundary of the set.
In the interior, continuity and a null image force local constancy. -/
theorem finite_image_of_finite_frontier {S : Set ℝ} (hs : IsClosed S) {f : ℝ → ℝ}
    (hf : Continuous f) (hz : volume (f '' S)=0) (a b : ℝ)
    (hfin : (Icc a b ∩ frontier S).Finite) : (f '' (Icc a b∩S)).Finite := by
  apply ((hfin.insert a).image f).subset
  rintro y ⟨v,hv,rfl⟩
  let K := (Icc a b∩S) ∩ f ⁻¹' {f v}
  have hK : IsCompact K := (isCompact_Icc.inter_right hs).inter_right (isClosed_singleton.preimage hf)
  obtain ⟨t,ht,hmin⟩ := hK.exists_isMinOn (show K.Nonempty from ⟨v,hv,rfl⟩) continuous_id.continuousOn
  have htv : f t=f v := ht.2
  refine ⟨t,?_,htv⟩
  by_cases h : t=a
  · exact Or.inl h
  right
  refine ⟨ht.1.1,subset_closure ht.1.2,?_⟩
  intro hi
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  let l := max a (t-δ/2)
  have hal : a≤l := le_max_left ..
  have hlt : l<t := max_lt (lt_of_le_of_ne ht.1.1.1 (Ne.symm h)) (by linarith only [hδ])
  have hI : Icc l t⊆S := by
    intro w hw
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hw.2)]
    linarith only [(le_max_right a (t-δ/2)).trans hw.1,hδ]
  have he := equal_on_interval hf hz hlt.le hI
  have hl : l∈K := ⟨⟨⟨hal,hlt.le.trans ht.1.1.2⟩,hI ⟨le_rfl,hlt.le⟩⟩,he.trans htv⟩
  exact hlt.not_ge (hmin hl)

#print axioms finite_image_of_finite_frontier
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
