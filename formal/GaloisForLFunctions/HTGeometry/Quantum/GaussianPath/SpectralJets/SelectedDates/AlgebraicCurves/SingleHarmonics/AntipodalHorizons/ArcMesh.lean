import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryFaces

/-! # A time mesh for short enclosing arcs of a bounded spectrum -/

open Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
noncomputable section

/-- Backing up from s to q shifts phases with frequencies in [−1,0] by
at most s−q turns, all in the same direction. Even a subset of phases
therefore fits an arc enlarged by only one mesh step. -/
theorem mesh_encloses {I J : Type*} [Fintype I] [Nonempty I] [Fintype J] (u : I → J)
    (f : I → ℝ) (hf : ∀ i, f i∈Icc (-1:ℝ) 0) (p : J → UnitAddCircle) (b : J)
    {q s δ r : ℝ} (hr : 0≤r) (hq : q≤s) (hδ : s-q≤δ) (hp : p∈enclosingUnitArc r)
    (z : I → UnitAddCircle)
    (hz : ∀ i, z i = p (u i)-p b+(((q-s)*f i:ℝ):UnitAddCircle)) :
    z∈enclosingUnitArc (r+δ) := by
  classical
  obtain ⟨a,ha⟩ := mem_iUnion.mp hp
  have lift (i : I) : ∃ x∈Icc (0:ℝ) r, (x:UnitAddCircle)=p (u i)-p a := by
    by_cases h : u i=a
    · exact ⟨0,⟨le_rfl,hr⟩,by simp only [h,sub_self,AddCircle.coe_zero]⟩
    · exact ha (u i) h
  choose x hx he using lift
  let y (i : I) := x i+(q-s)*f i
  have hy (i : I) : y i∈Icc (0:ℝ) (r+δ) := by
    have hh := hf i
    have hstep : (q-s)*f i≤s-q := by
      calc (q-s)*f i ≤ (q-s)*(-1) := mul_le_mul_of_nonpos_left hh.1 (sub_nonpos.mpr hq)
           _ = s-q := by ring
    exact ⟨add_nonneg (hx i).1 (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hq) hh.2),
      add_le_add (hx i).2 (hstep.trans hδ)⟩
  have heq (i : I) : (y i:UnitAddCircle)=z i-(p a-p b) := by
    rw [hz,y,AddCircle.coe_add,he]
    abel
  obtain ⟨a',_,hle⟩ := Finset.exists_min_image Finset.univ y Finset.univ_nonempty
  refine mem_iUnion.mpr ⟨a',fun i _ => ⟨y i-y a',⟨sub_nonneg.mpr (hle i (Finset.mem_univ _)),?_⟩,?_⟩⟩
  · exact (sub_le_self _ (hy a').1).trans (hy i).2
  · rw [AddCircle.coe_sub,heq,heq,sub_sub_sub_cancel_right]

#print axioms mesh_encloses
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
