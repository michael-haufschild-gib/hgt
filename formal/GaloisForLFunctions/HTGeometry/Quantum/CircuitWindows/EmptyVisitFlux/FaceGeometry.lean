import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar

/-! # Minimum gap before an inward crossing of an enclosing spectral arc -/
open Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

/-- Evolution of phases with velocities measured in turns per unit time. -/
def flow {I : Type*} (w : I → ℝ) (t : ℝ) (i : I) : UnitAddCircle := ((t*w i:ℝ):UnitAddCircle)

/-- The right endpoint is moving towards the left endpoint. All other
phases are strictly between the two endpoints. -/
def inwardFace {I : Type*} (w : I → ℝ) (r t : ℝ) (i j : I) : Prop :=
  w j < w i ∧ flow w t j-flow w t i = (r:UnitAddCircle) ∧
    ∀ k, k≠i → k≠j → flow w t k-flow w t i ∈ ((↑) : ℝ → UnitAddCircle) '' Ioo 0 r

private theorem lifts_at_visit {I : Type*} [Fintype I] {p : I → UnitAddCircle} {r : ℝ}
    (hr : 0≤r) (h : p ∈ enclosingUnitArc r) :
    ∃ i : I, ∀ k, ∃ v ∈ Icc (0:ℝ) r, (v:UnitAddCircle)=p k-p i := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp h
  refine ⟨i,fun k => ?_⟩
  by_cases he : k=i
  · subst k
    exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
  · exact hi k he

/-- An inward contact excludes every earlier visit for at least the
uncovered 1−2r turns divided by this particular pair's relative speed. -/
theorem gap_before_contact {I : Type*} [Fintype I] (w : I → ℝ) {r t u : ℝ}
    (hr : 0≤r) (ht : t<u) (hv : flow w t ∈ enclosingUnitArc r)
    {i j : I} (hs : w j < w i) (hc : flow w u j-flow w u i=(r:UnitAddCircle)) :
    1-2*r ≤ (u-t)*(w i-w j) := by
  obtain ⟨b,hb⟩ := lifts_at_visit hr hv
  obtain ⟨x,hx,hxe⟩ := hb i
  obtain ⟨y,hy,hye⟩ := hb j
  let d := y-x+(u-t)*(w j-w i)
  have hdiff : ((y-x:ℝ):UnitAddCircle)=flow w t j-flow w t i := by
    rw [AddCircle.coe_sub,hye,hxe,sub_sub_sub_cancel_right]
  have hturn : (d:UnitAddCircle)=(r:UnitAddCircle) := by
    rw [←hc]
    dsimp only [d]
    rw [AddCircle.coe_add,hdiff]
    simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
    congr 1
    ring
  have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr ht) (sub_neg.mpr hs)
  have hlt : d<r := by dsimp only [d]; linarith only [hneg,hx.1,hy.2]
  by_contra! hfail
  have hd : d ∈ Ioc (r-1) (r-1+1) := by
    refine ⟨?_,by linarith only [hlt]⟩
    dsimp only [d]
    linarith only [hfail,hy.1,hx.2]
  have hr' : r ∈ Ioc (r-1) (r-1+1) := ⟨by linarith,by linarith⟩
  exact hlt.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ioc hd hr').mp hturn)

/-- A regular inward contact belongs to the closed empty-circuit arc. -/
theorem inwardFace_visit {I : Type*} [Fintype I] {w : I → ℝ} {r t : ℝ} {i j : I}
    (hr : 0≤r) (hf : inwardFace w r t i j) : flow w t ∈ enclosingUnitArc r := by
  refine mem_iUnion.mpr ⟨i,fun k hki => ?_⟩
  by_cases hkj : k=j
  · subst k
    exact ⟨r,⟨hr,le_rfl⟩,hf.2.1.symm⟩
  · exact image_mono Ioo_subset_Icc_self (hf.2.2 k hki hkj)

#print axioms gap_before_contact
#print axioms inwardFace_visit
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
