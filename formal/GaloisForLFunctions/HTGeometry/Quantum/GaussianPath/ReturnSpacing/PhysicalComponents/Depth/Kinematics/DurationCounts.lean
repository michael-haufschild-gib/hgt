import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Kinematics.ClosingSpeed
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.AllDepths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.DurationCharge
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.LimitLaw.PhysicalMarks

/-! # Counting long residence intervals by their depth and closing speed -/
open MeasureTheory Finset Set Real
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open EmptyVisitFlux SharpOccupation SpectralGapMass.Bulk
noncomputable section

/-- Every deep component either lasts at least L or has a fast closing
pair. This counting inequality holds at each finite observation endpoint. -/
theorem depth_mark_cover {n : ℕ} (u : PathShell n) (σ T : ℝ) {ρ δ b : ℝ}
    (hρ : ρ∈Ioo (0:ℝ) (sqrt 2)) (hδ : δ∈Ioo (0:ℝ) (sqrt 2)) (hb : 0<b)
    (hd : physicalArc δ≤physicalArc ρ) (L : ℝ)
    (hL : L*(b*sqrt (n+2:ℕ)/(2*π))≤physicalArc ρ-physicalArc δ) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
    let E := fun i => -H.2.isHermitian.eigenvalues i
    let r := physicalArc ρ
    let A := entriesAfter E r σ T
    (reached (visitSet H 0 ρ) (visitSet H 0 δ) A).card ≤
      (longVisits (visitSet H 0 ρ) L A).card+((selectedDates E (fastPairs u b) r T) \ entryDates E r σ).card := by
  classical
  intro H E r A
  let w := fun i => E i/(2*π)
  let G := b*sqrt (n+2:ℕ)/(2*π)
  have hG : 0<G := by dsimp only [G]; positivity
  have hr := (physicalArc_spec hρ.1 hρ.2).1
  have hx := (physicalArc_spec hδ.1 hδ.2).1
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro a ha
  obtain ⟨ha',v,hav,hv,hseg⟩ := mem_filter.mp ha
  obtain ⟨hen,hno⟩ := mem_sdiff.mp ha'
  obtain ⟨p,_,hp⟩ := mem_biUnion.mp hen
  by_cases hf : p∈fastPairs u b
  · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨p,hf,hp⟩,hno⟩)
  have hgap : scaledGap u p.swap≤b := le_of_not_gt fun h => hf (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hbound : w p.1-w p.2≤G := by
    let e := H.2.isHermitian.eigenvalues
    let v₀ := sqrt (n+2:ℕ)
    change e p.2/v₀-e p.1/v₀≤b at hgap
    rw [←sub_div] at hgap
    have hv₀ : 0<v₀ := by dsimp only [v₀]; positivity
    have he := div_le_div_of_nonneg_right ((div_le_iff₀ hv₀).mp hgap) (by positivity : 0≤2*π)
    change -(e p.1)/(2*π)- -(e p.2)/(2*π)≤b*v₀/(2*π)
    exact (show -(e p.1)/(2*π)- -(e p.2)/(2*π)=(e p.2-e p.1)/(2*π) by ring).trans_le he
  have hface := ((mem_markedDates E p.1 p.2 hr.1.le (by linarith only [hr.2]) _ a T).mp hp).2.2
  have hkin := closing_travel_to_depth w hx.1.le hd hr.2 hav hface.1 hface.2.1
    ((physical_visit H hδ.1 hδ.2 v).mpr hv)
  have ht : L≤v-a := by
    by_contra! h
    exact (mul_lt_mul_of_pos_right h hG).not_ge ((hL.trans hkin).trans
      (mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hav)))
  exact mem_union_left _ (mem_filter.mpr ⟨ha',fun z hz =>
    hseg ⟨hz.1,by linarith only [ht,hz.2]⟩⟩)

#print axioms depth_mark_cover
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
