import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.FaceGeometry

/-! # Transport of real phase lifts across a scalar visit -/

open Set Finset
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
open EmptyVisitFlux
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- The circle configuration admits lifted ordinates of span at most r,
up to a common phase. -/
theorem arc_iff_lifts (p : I → UnitAddCircle) {r : ℝ} (hr : 0≤r) :
    p∈enclosingUnitArc r ↔ ∃ (y : I → ℝ) (b : UnitAddCircle),
      (∀ i, (y i : UnitAddCircle)=p i-b) ∧ ∀ i j, y i-y j≤r := by
  classical
  constructor
  · intro h
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    have hrep (k : I) : ∃ v∈Icc (0:ℝ) r, (v:UnitAddCircle)=p k-p i := by
      by_cases he : k=i
      · subst k
        exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
      · exact hi k he
    choose y hy hc using hrep
    exact ⟨y,p i,hc,fun i j => (sub_le_self _ (hy j).1).trans (hy i).2⟩
  · rintro ⟨y,b,hy,hw⟩
    obtain ⟨j,_,hj⟩ := exists_mem_eq_inf' univ_nonempty y
    refine mem_iUnion.mpr ⟨j,fun i _ => ⟨y i-y j,⟨sub_nonneg.mpr (hj.symm.trans_le (inf'_le y (mem_univ i))),hw i j⟩,?_⟩⟩
    rw [AddCircle.coe_sub,hy,hy,sub_sub_sub_cancel_right]

/-- A pair of lifts cannot leave its initial copy of the arc-difference
interval without passing through the open gap between neighboring copies. -/
theorem end_span (w : I → ℝ) {r v h : ℝ} (hr : 0≤r) (hs : r<1/2) (hh : 0≤h)
    (hvis : ∀ u∈Icc (0:ℝ) h, flow w (v+u)∈enclosingUnitArc r)
    {y : I → ℝ} {b : UnitAddCircle} (hy : ∀ i, (y i:UnitAddCircle)=flow w v i-b)
    (hw : ∀ i j, y i-y j≤r) (i j : I) :
    y i-y j+h*(w i-w j)≤r := by
  by_contra! hbad
  let f (u : ℝ) := y i-y j+u*(w i-w j)
  have h0 : f 0≤r := by simpa only [f,zero_mul,add_zero] using hw i j
  have hend : r<f h := hbad
  obtain ⟨s,hrs,hsm⟩ := exists_between (lt_min hend (by linarith only [hs] : r<1/2))
  have hf : Continuous f := continuous_const.add (continuous_id.mul_const _)
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc hh hf.continuousOn
    (show s∈Icc (f 0) (f h) from ⟨h0.trans hrs.le,hsm.le.trans (min_le_left ..)⟩)
  obtain ⟨z,c,hz,hspan⟩ := (arc_iff_lifts _ hr).mp (hvis u hu)
  have hpair : ((y i-y j:ℝ):UnitAddCircle)=flow w v i-flow w v j := by
    rw [AddCircle.coe_sub,hy,hy,sub_sub_sub_cancel_right]
  have heq : ((z i-z j:ℝ):UnitAddCircle)=(s:UnitAddCircle) := by
    rw [←he,AddCircle.coe_sub,hz,hz,sub_sub_sub_cancel_right]
    dsimp only [f]
    rw [AddCircle.coe_add,hpair]
    simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
    congr 1
    ring
  have h1 : z i-z j∈Ico (-(1/2):ℝ) (-(1/2)+1) :=
    ⟨by linarith only [hspan j i,hs],by linarith only [hspan i j,hs]⟩
  have h2 : s∈Ico (-(1/2):ℝ) (-(1/2)+1) :=
    ⟨by linarith only [hr,hrs],by linarith only [hsm.trans_le (min_le_right ..)]⟩
  exact hrs.not_ge (((AddCircle.coe_eq_coe_iff_of_mem_Ico h1 h2).mp heq) ▸ hspan i j)

#print axioms end_span
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
