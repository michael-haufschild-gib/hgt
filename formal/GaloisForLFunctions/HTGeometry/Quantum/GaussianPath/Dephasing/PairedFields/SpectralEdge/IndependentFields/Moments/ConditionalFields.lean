import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.CenteredProbability

/-! # Circuit probabilities conditional on one frozen base -/

open Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private pack pack_law from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.CenteredProbability
open private real_sections from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.SharedDraw
noncomputable section

/-- A bound valid off an arbitrary set of base fields transfers by Fubini.
Only the measurable source event is sliced. The base exceptional set enters
through its outer probability. -/
theorem sliced_field_bound {n : ℕ} (G : Set (FieldPair n)) (hG : MeasurableSet G)
    (B : Set (Coeff n)) {c : ℝ} (hc : 0 ≤ c)
    (hq : ∀ h∉B, (fieldLaw n).real {g | (fun i => (h i,g i))∈G} ≤ c) :
    (pairLaw n).real G ≤ (fieldLaw n).real B+c := by
  let μ := fieldLaw n
  let D := toMeasurable μ B
  let E := pack ⁻¹' G
  let F := E \ (D ×ˢ (univ : Set (Coeff n)))
  have hE : MeasurableSet E := hG.preimage (pack_law n).measurable
  have hF : MeasurableSet F := hE.diff ((measurableSet_toMeasurable ..).prod MeasurableSet.univ)
  have hsub : E ⊆ D ×ˢ (univ : Set (Coeff n)) ∪ F := fun z hz => by
    by_cases hd : z.1∈D
    · exact Or.inl ⟨hd,mem_univ _⟩
    · exact Or.inr ⟨hz,fun h => hd h.1⟩
  have hsec (h : Coeff n) : μ.real (Prod.mk h ⁻¹' F) ≤ c := by
    by_cases hd : h∈D
    · have he : Prod.mk h ⁻¹' F=∅ := eq_empty_iff_forall_notMem.mpr
        (fun g hg => hg.2 ⟨hd,mem_univ _⟩)
      rwa [he,measureReal_empty]
    · exact (measureReal_mono (preimage_mono (sdiff_subset : F ⊆ E))).trans
        (hq h (fun hm => hd (subset_toMeasurable _ _ hm)))
  have hi : Integrable (fun h => μ.real (Prod.mk h ⁻¹' F)) μ := Integrable.of_bound
    (measurable_measure_prodMk_left hF).ennreal_toReal.aestronglyMeasurable 1
    (ae_of_all _ fun _ => (Real.norm_of_nonneg measureReal_nonneg).le.trans measureReal_le_one)
  rw [←show (μ.prod μ).real E=(pairLaw n).real G from
    congrArg ENNReal.toReal ((pack_law n).measure_preimage hG.nullMeasurableSet)]
  apply (measureReal_mono hsub).trans ((measureReal_union_le ..).trans (add_le_add _ _))
  · rw [measureReal_prod_prod,probReal_univ,mul_one]
    exact (congrArg ENNReal.toReal (measure_toMeasurable (μ:=μ) B)).le
  · rw [real_sections μ μ hF]
    simpa only [integral_const,probReal_univ,one_smul] using integral_mono hi (integrable_const c) hsec

#print axioms sliced_field_bound
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
