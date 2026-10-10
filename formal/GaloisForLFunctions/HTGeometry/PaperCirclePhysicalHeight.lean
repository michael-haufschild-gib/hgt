import GaloisForLFunctions.HTGeometry.PaperFourierLiteralConvergence

/-! # Common physical heights for Fourier reconstruction on varying circles

The covering map pulls Haar-null sets back to Lebesgue-null sets on the entire
real line. Hence countably many continuous periodic observables with different
periods admit simultaneous reconstruction at the same physical height.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
open scoped BigOperators

/-- The covering map preserves null sets even though its source has infinite mass. -/
theorem paperCirclePhysicalHeight_quasiMeasurePreserving
    (T : ℝ) [hT : Fact (0 < T)] :
    QuasiMeasurePreserving (fun t : ℝ => (t : AddCircle T))
      volume AddCircle.haarAddCircle := by
  refine ⟨AddCircle.measurable_mk', AbsolutelyContinuous.mk ?_⟩
  intro E hEm hEz
  rw [Measure.map_apply AddCircle.measurable_mk' hEm]
  have hvol : (volume : Measure (AddCircle T)) E = 0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, hEz]
    simp
  have hparts : ∀ n : ℤ, volume
      ((fun t : ℝ => (t : AddCircle T)) ⁻¹' E ∩ Ioc (n • T) ((n + 1) • T)) = 0 := by
    intro n
    have hr := (AddCircle.measurePreserving_mk T (n • T)).measure_preimage
      hEm.nullMeasurableSet
    rw [Measure.restrict_apply (hEm.preimage AddCircle.measurable_mk')] at hr
    simpa only [add_smul, one_smul] using hr.trans hvol
  calc
    volume ((fun t : ℝ => (t : AddCircle T)) ⁻¹' E) =
        volume (⋃ n : ℤ,
          (fun t : ℝ => (t : AddCircle T)) ⁻¹' E ∩ Ioc (n • T) ((n + 1) • T)) := by
      rw [← inter_iUnion, iUnion_Ioc_zsmul hT.out, inter_univ]
    _ = 0 := measure_iUnion_null hparts

/-- Different periods share one exceptional set on the actual real-height line. -/
theorem paperCircleContinuous_common_physical_convergence
    {κ : Type*} [Countable κ] (T : κ → ℝ) [∀ j, Fact (0 < T j)]
    (f : (j : κ) → C(AddCircle (T j), ℂ)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ j,
        Tendsto (fun N => paperCircleFourierPartialSum (T j) (f j) N (t : AddCircle (T j)))
          atTop (𝓝 (f j (t : AddCircle (T j)))) := by
  classical
  have hj (j : κ) : ∀ᵐ t : ℝ ∂volume,
      Tendsto (fun N => paperCircleFourierPartialSum (T j) (f j) N (t : AddCircle (T j)))
        atTop (𝓝 (f j (t : AddCircle (T j)))) := by
    obtain ⟨E, _, hz, hc⟩ := paperCircleContinuous_fourier_convergence (T j) (f j)
    have he : ∀ᵐ x : AddCircle (T j) ∂AddCircle.haarAddCircle, x ∉ E := by
      apply ae_iff.mpr
      simpa using hz
    exact (paperCirclePhysicalHeight_quasiMeasurePreserving (T j)).ae
      (he.mono (fun x hx => hc x hx))
  have hall := ae_all_iff.mpr hj
  obtain ⟨E, hs, hm, hz⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
  refine ⟨E, hm, hz, fun t ht => ?_⟩
  by_contra h
  exact ht (hs h)

/-- Finite mixtures with arbitrary complex weights use the same real exceptional set. -/
theorem paperCircleContinuous_common_physical_span_convergence
    {κ : Type*} [Countable κ] (T : κ → ℝ) [∀ j, Fact (0 < T j)]
    (f : (j : κ) → C(AddCircle (T j), ℂ)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ t ∉ E, ∀ (S : Finset κ) (c : κ → ℂ),
        Tendsto (fun N => ∑ j ∈ S, c j *
          paperCircleFourierPartialSum (T j) (f j) N (t : AddCircle (T j)))
          atTop (𝓝 (∑ j ∈ S, c j * f j (t : AddCircle (T j)))) := by
  obtain ⟨E, hm, hz, hc⟩ := paperCircleContinuous_common_physical_convergence T f
  exact ⟨E, hm, hz, fun t ht S c =>
    tendsto_finsetSum S (fun j _ => (hc t ht j).const_mul (c j))⟩

end
end GaloisForLFunctions.HTGeometry
