import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CandidateFace
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalFace

/-! # An atom at the shortest possible first scalar wait from a pair antipode -/

open Set Filter Topology MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
open EmptyVisitFlux
noncomputable section

/-- From the preceding antipode the pair alone excludes a scalar visit for
2π(1/2−r) divided by its gap. Equality in this waiting bound is equivalent
to the whole register entering through the specified face. -/
theorem antipodal_first_iff {I : Type*} [Fintype I] (E : I→ℝ) (i j : I) (hE : E j<E i)
    (r : Ioo (0:ℝ) (1/2)) (n : ℕ) :
    let t := pairDate (fun l => -E l) j i r n
    let a := pairDate (fun l => -E l) j i (1/2) n
    let w := fun l => -E l/(2*π)
    (t-a)*(E i-E j)=2*π*(1/2-(r:ℝ)) ∧
    t ∈ lowerBounds {v : ℝ | a≤v ∧ flow w v∈enclosingUnitArc r} ∧
    (IsLeast {v : ℝ | a≤v ∧ flow w v∈enclosingUnitArc r} t ↔
      visitEntry w r t ∧ pairFace (forwardUnitArc r) w r t j i) := by
  intro t a w
  have hg := sub_pos.mpr hE
  have htime : (t-a)*(E i-E j)=2*π*(1/2-(r:ℝ)) := by
    dsimp only [t,a,pairDate]
    rw [neg_sub_neg]
    field_simp [hg.ne']
    ring
  have hta : a≤t := by
    apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_left (b:=E i-E j) _ hg
    rw [htime]
    exact mul_nonneg two_pi_pos.le (sub_nonneg.mpr r.2.2.le)
  have hgap : (t-a)*(w j-w i)=1/2-(r:ℝ) := by
    change (t-a)*(-E j/(2*π)-(-E i)/(2*π))=_
    rw [←sub_div,neg_sub_neg,←mul_div_assoc,htime]
    field_simp [Real.pi_ne_zero]
  have hf := earliest_visit_iff_face w r.2.1.le r.2.2
    (div_lt_div_of_pos_right (neg_lt_neg hE) two_pi_pos) (pinned_at_pair E i j hE r n) hta
    (hgap.trans_lt (by linarith only [r.2.2]))
  have hlow : t ∈ lowerBounds {v : ℝ | a≤v ∧ flow w v∈enclosingUnitArc r} := by
    intro v hv
    by_contra! hvt
    have hvel : w i<w j := div_lt_div_of_pos_right (neg_lt_neg hE) two_pi_pos
    have h := gap_before_contact w r.2.1.le hvt hv.2 hvel (pinned_at_pair E i j hE r n)
    have hle := mul_le_mul_of_nonneg_right (sub_le_sub_left hv.1 t) (sub_nonneg.mpr hvel.le)
    linarith only [h.trans hle,hgap,r.2.2]
  exact ⟨htime,hlow,hf.trans ⟨fun h => ⟨(entry_iff_closed_face w r.2.1.le r.2.2).mpr ⟨j,i,h⟩,h⟩,And.right⟩⟩

/-- For one specified high winding the first scalar visit after its
preceding antipode attains the two-level minimum with probability tending
to r^(D−2). Both the origin and its minimum wait use the actual energy gap. -/
theorem gaussian_antipodal_minimum_wait (k : ℕ) {i j : Level k} (hij : j < i) (r : Ioo (0:ℝ) (1/2)) :
    let μ := centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1
    Tendsto (fun n : ℕ => μ {x | let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
      let t := pairDate (fun l => -E l) j i r n
      let a := pairDate (fun l => -E l) j i (1/2) n
      let w := fun l => -E l/(2*π)
      IsLeast {v : ℝ | a≤v ∧ flow w v∈enclosingUnitArc r} t}) atTop
      (𝓝 (ENNReal.ofReal (r:ℝ)^(2^(k+3)-2))) := by
  intro μ
  have hs : ∀ᵐ x ∂μ, Function.Injective (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x) := by
    apply (productGaussian_absolutelyContinuous _ one_ne_zero _).ae_le
    exact (ae_iff.mpr (volume_notMaximallyProjective_chain_eq_zero k)).mono fun _ hx =>
      injective_sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) hx.injective
  apply (gaussian_single_winding_entry k hij r).congr
  intro n
  apply measure_congr
  filter_upwards [hs] with x hx
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
  have hE : E j<E i := lt_of_le_of_ne (monotone_sortedTuple _ hij.le) (hx.ne hij.ne)
  exact propext (antipodal_first_iff E i j hE r n).2.2.symm

#print axioms gaussian_antipodal_minimum_wait
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
