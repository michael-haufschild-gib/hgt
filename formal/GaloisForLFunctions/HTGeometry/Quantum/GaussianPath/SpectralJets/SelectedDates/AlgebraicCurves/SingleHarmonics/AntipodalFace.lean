import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryFaces
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.PairFrequency

/-! # Earliest scalar visit after the preceding antipode of a closing pair -/

open Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
open EmptyVisitFlux
noncomputable section

/-- Two phases exactly r turns apart determine the containing r-arc when
r is less than half a turn. A simultaneous endpoint tie is allowed. -/
private theorem pinned_arc {I : Type*} [Fintype I] (p : I→UnitAddCircle) {r : ℝ}
    (hr : 0≤r) (hs : r<1/2) (i j : I) (hp : p j-p i=(r:UnitAddCircle))
    (hin : p∈enclosingUnitArc r) : ∀ k, p k-p i∈forwardUnitArc r := by
  obtain ⟨b,hb⟩ := mem_iUnion.mp hin
  have hl (k : I) : ∃ x∈Icc (0:ℝ) r, (x:UnitAddCircle)=p k-p b := by
    by_cases he : k=b
    · subst k
      exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
    · exact hb k he
  choose x hx he using hl
  have hd : ((x j-x i:ℝ):UnitAddCircle)=(r:UnitAddCircle) := by
    rw [AddCircle.coe_sub,he,he,sub_sub_sub_cancel_right,hp]
  have h₁ : x j-x i∈Ioc (r-1) (r-1+1) := by
    constructor <;> linarith only [hs,(hx i).1,(hx i).2,(hx j).1,(hx j).2]
  have h₂ : r∈Ioc (r-1) (r-1+1) := ⟨by linarith,by linarith⟩
  have hr' := (AddCircle.coe_eq_coe_iff_of_mem_Ioc h₁ h₂).mp hd
  have hi : x i=0 := by linarith only [hr',(hx i).1,(hx j).2]
  have hib : p i=p b := sub_eq_zero.mp (by rw [←he,hi,AddCircle.coe_zero])
  exact fun k => ⟨x k,hx k,by rw [hib]; exact he k⟩

/-- If a chosen pair is just now closing to r, any origin in its preceding
forbidden interval gives a true first visit precisely when the other
phases lie in the same arc. -/
theorem earliest_visit_iff_face {I : Type*} [Fintype I] (w : I→ℝ) {r a u : ℝ}
    (hr : 0≤r) (hs : r<1/2) {i j : I} (hv : w j<w i)
    (hpin : flow w u j-flow w u i=(r:UnitAddCircle))
    (hau : a≤u) (hgap : (u-a)*(w i-w j)<1-2*r) :
    IsLeast {t : ℝ | a≤t ∧ flow w t∈enclosingUnitArc r} u ↔
      pairFace (forwardUnitArc r) w r u i j := by
  constructor
  · intro hh
    exact ⟨hv,hpin,fun k _ _ => pinned_arc _ hr hs i j hpin hh.1.2 k⟩
  · intro hface
    refine ⟨⟨hau,closed_face_visit hr hface⟩,?_⟩
    intro t ht
    by_contra! he
    have h := gap_before_contact w hr he ht.2 hv hpin
    have hle := mul_le_mul_of_nonneg_right (sub_le_sub_left ht.1 u) (sub_nonneg.mpr hv.le)
    exact hgap.not_ge (h.trans hle)

#print axioms earliest_visit_iff_face
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
