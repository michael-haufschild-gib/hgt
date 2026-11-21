import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.FaceGeometry

/-! # Unique endpoint labels and isolation of regular inward crossings -/
open Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

private theorem face_lifts {I : Type*} {w : I → ℝ} {r t : ℝ} {i j : I}
    (hr : 0 < r) (hf : inwardFace w r t i j) (k : I) :
    ∃ x ∈ Icc (0:ℝ) r, (x:UnitAddCircle)=flow w t k-flow w t i ∧
      (x=0 → k=i) ∧ (x=r → k=j) := by
  by_cases hki : k=i
  · subst k
    exact ⟨0,⟨le_rfl,hr.le⟩,by simp,fun _ => rfl,fun h => (hr.ne h).elim⟩
  by_cases hkj : k=j
  · subst k
    exact ⟨r,⟨hr.le,le_rfl⟩,hf.2.1.symm,fun h => (hr.ne' h).elim,fun _ => rfl⟩
  obtain ⟨x,hx,he⟩ := hf.2.2 k hki hkj
  exact ⟨x,⟨hx.1.le,hx.2.le⟩,he,fun h => (hx.1.ne' h).elim,fun h => (hx.2.ne h).elim⟩

/-- At a regular crossing of a subsemicircle, any pair at separation
r in the forward direction must be its two specified endpoints. -/
theorem inward_endpoints_unique {I : Type*} {w : I → ℝ} {r t : ℝ} {i j b c : I}
    (hr : 0<r) (hs : r<1/2) (hf : inwardFace w r t i j)
    (hc : flow w t c-flow w t b=(r:UnitAddCircle)) : b=i ∧ c=j := by
  obtain ⟨x,hx,he,h0,_⟩ := face_lifts hr hf b
  obtain ⟨y,hy,hf',_,h1⟩ := face_lifts hr hf c
  have heq : ((y-x:ℝ):UnitAddCircle)=(r:UnitAddCircle) := by
    rw [AddCircle.coe_sub,hf',he,sub_sub_sub_cancel_right,hc]
  have hxy : y-x ∈ Ioc (r-1) (r-1+1) :=
    ⟨by linarith only [hs,hx.2,hy.1],by linarith only [hx.1,hy.2]⟩
  have hrr : r ∈ Ioc (r-1) (r-1+1) := ⟨by linarith,by linarith⟩
  have h := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hxy hrr).mp heq
  exact ⟨h0 (by linarith only [h,hx.1,hy.2]),h1 (by linarith only [h,hx.1,hy.2])⟩

/-- Positive time between contacts times the full velocity width is at
least the complement of two enclosing arcs. -/
theorem inward_spacing {I : Type*} [Fintype I] [Nonempty I] (w : I → ℝ)
    {r t u : ℝ} (hr : 0 ≤ r) (ht : t < u) {i j b c : I}
    (hf : inwardFace w r t i j) (hg : inwardFace w r u b c) :
    1-2*r ≤ (u-t)*(Finset.univ.sup' Finset.univ_nonempty w-Finset.univ.inf' Finset.univ_nonempty w) :=
  (gap_before_contact w hr ht (inwardFace_visit hr hf) hg.1 hg.2.1).trans
    (mul_le_mul_of_nonneg_left (sub_le_sub (Finset.le_sup' w (Finset.mem_univ b))
      (Finset.inf'_le w (Finset.mem_univ c))) (sub_nonneg.mpr ht.le))

#print axioms inward_endpoints_unique
#print axioms inward_spacing
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
