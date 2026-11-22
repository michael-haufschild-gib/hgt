import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryFaces

/-! # Distinct inner entries lie in distinct enclosing-arc components -/
open Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

/-- Before an inner entry the pinned pair also crosses the outer width.
Immediately before that crossing it cannot fit inside the outer arc.
Consequently a connected outer visit contains at most one inner entry. -/
theorem outer_absence_before_inner_entry {I : Type*} [Fintype I] (w : I → ℝ)
    {x y u v : ℝ} (hy : 0≤y) (hyx : y≤x) (hx : x<1/2) (huv : u<v)
    (hu : flow w u ∈ enclosingUnitArc y) (hv : visitEntry w y v) :
    ∃ z∈Ioo u v, flow w z ∉ enclosingUnitArc x := by
  obtain ⟨i,j,hf⟩ := (entry_iff_closed_face w hy (hyx.trans_lt hx)).mp hv
  let d := w i-w j
  have hd : 0<d := sub_pos.mpr hf.1
  have hgap : (1-2*y)/d≤v-u := (div_le_iff₀ hd).mpr
    (gap_before_contact w hy huv hu hf.1 hf.2.1)
  let t := v-(x-y)/d
  have ht : u<t := by
    have h : (x-y)/d<(1-2*y)/d := (div_lt_div_iff_of_pos_right hd).mpr
      (by linarith only [hx,hyx])
    dsimp only [t]
    linarith only [h,hgap]
  have htv : t≤v := sub_le_self _ (div_nonneg (sub_nonneg.mpr hyx) hd.le)
  have he : flow w t j-flow w t i=(x:UnitAddCircle) := calc
    _ = (flow w v j-flow w v i)+(((t-v)*(w j-w i):ℝ):UnitAddCircle) := by
      simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
      congr 1
      ring
    _ = _ := by
      rw [hf.2.1,←AddCircle.coe_add]
      congr 1
      rw [show w j-w i = -d by dsimp only [d]; ring]
      dsimp only [t]
      field_simp [hd.ne']
      <;> ring
  let h := min (t-u) ((1-2*x)/d)
  have hh : 0<h := lt_min (sub_pos.mpr ht) (div_pos (by linarith only [hx]) hd)
  have h₁ : h≤t-u := min_le_left ..
  have h₂ : h≤(1-2*x)/d := min_le_right ..
  refine ⟨t-h/2,⟨by linarith only [h₁,hh],by linarith only [htv,hh]⟩,?_⟩
  intro hz
  have hb := gap_before_contact w (hy.trans hyx) (show t-h/2<t by linarith only [hh])
    hz hf.1 he
  have := (div_le_iff₀ hd).mpr hb
  linarith only [this,h₂,hh]

#print axioms outer_absence_before_inner_entry
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
