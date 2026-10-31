import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveLoopFieldMap

/-!
# The intrinsic Borel torus kernel and coefficient-field descent

Both torus coordinates equal one exactly on the actual positive
unipotent subgroup. Naturality and faithful coefficient-field maps then
reflect unipotent membership as well as preserving it.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2
noncomputable section
variable {F E : Type*} [Field F] [Field E]

/-- Positive unipotent loops belong to the actual positive Borel. -/
theorem positiveUnipotent_le_positiveBorel : positiveUnipotent F ≤ positiveBorel F := by
  rintro g ⟨u, hu, rfl⟩
  refine ⟨(1, ⟨u, positiveUnipotentMatrices_le_iwahori F hu⟩), ?_⟩
  change centralEmbedding F 1 * positiveEmbedding F u = positiveEmbedding F u
  rw [map_one, one_mul]

/-- The two intrinsic Borel coordinates have exactly the positive unipotent kernel. -/
theorem borelTorusHom_eq_one_iff (b : positiveBorel F) :
    borelTorusHom F b = 1 ↔ (b : LoopSL2 F) ∈ positiveUnipotent F := by
  let p := positiveBorelFactors F b
  constructor
  · intro ht
    have hc : p.1 = 1 := congrArg Prod.fst ht
    have ha : iwahoriFiniteCoordinate F p.2 = 1 := congrArg Prod.snd ht
    have hu := (iwahoriFiniteCoordinate_eq_one_iff F p.2).mp ha
    rw [← positiveBorelFactors_spec F b]
    change centralEmbedding F p.1 * positiveEmbedding F p.2 ∈ positiveUnipotent F
    rw [hc, map_one, one_mul]
    exact ⟨p.2, hu, rfl⟩
  · rintro ⟨u, hu, he⟩
    have hp : p = (1, ⟨u, positiveUnipotentMatrices_le_iwahori F hu⟩) := by
      apply positiveBorelEmbedding_injective F
      rw [positiveBorelFactors_spec]
      change (b : LoopSL2 F) = centralEmbedding F 1 * positiveEmbedding F u
      rw [map_one, one_mul]
      exact he.symm
    change (p.1, iwahoriFiniteCoordinate F p.2) = (1, 1)
    rw [hp]
    have ha := (iwahoriFiniteCoordinate_eq_one_iff F
      ⟨u, positiveUnipotentMatrices_le_iwahori F hu⟩).mpr hu
    exact Prod.ext rfl ha

/-- A coefficient-field map preserves the actual positive unipotent subgroup. -/
theorem fieldMap_mem_positiveUnipotent (ι : F →+* E) {g : LoopSL2 F}
    (hg : g ∈ positiveUnipotent F) : fieldMap ι g ∈ positiveUnipotent E := by
  obtain ⟨u, hu, rfl⟩ := hg
  have hmu : powerSeriesFieldMatrixMap ι u ∈ positiveUnipotentMatrices E := by
    apply (mem_positiveUnipotentMatrices E _).mpr
    change ι (PowerSeries.constantCoeff (u 0 0)) = 1 ∧
      ι (PowerSeries.constantCoeff (u 1 0)) = 0 ∧ ι (PowerSeries.constantCoeff (u 1 1)) = 1
    obtain ⟨ha, hc, hd⟩ := (mem_positiveUnipotentMatrices F u).mp hu
    rw [ha, hc, hd, map_one, map_zero]
    exact ⟨rfl, rfl, rfl⟩
  exact ⟨powerSeriesFieldMatrixMap ι u, hmu, (fieldMap_positiveEmbedding ι u).symm⟩

/-- Faithful coefficient-field maps reflect the actual completed unipotent subgroup. -/
theorem fieldMap_mem_positiveUnipotent_iff (ι : F →+* E) (g : LoopSL2 F) :
    fieldMap ι g ∈ positiveUnipotent E ↔ g ∈ positiveUnipotent F := by
  constructor
  · intro hg
    have hb : g ∈ positiveBorel F := (fieldMap_mem_positiveBorel_iff ι g).mp
      (positiveUnipotent_le_positiveBorel hg)
    let b : positiveBorel F := ⟨g, hb⟩
    have ht := (borelTorusHom_eq_one_iff (borelFieldMap ι b)).mpr hg
    rw [borelTorusHom_fieldMap] at ht
    have hi : Function.Injective (Units.map ι.toMonoidHom) := by
      intro a c h
      apply Units.ext
      apply ι.injective
      exact congrArg (fun z : Eˣ => (z : E)) h
    have hc : (borelTorusHom F b).1 = 1 := by
      apply hi
      simpa only [map_one, Prod.fst_one] using congrArg Prod.fst ht
    have ha : (borelTorusHom F b).2 = 1 := by
      apply hi
      simpa only [map_one, Prod.snd_one] using congrArg Prod.snd ht
    exact (borelTorusHom_eq_one_iff b).mp (Prod.ext hc ha)
  · exact fieldMap_mem_positiveUnipotent ι

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.borelTorusHom_eq_one_iff
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.fieldMap_mem_positiveUnipotent_iff
