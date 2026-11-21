import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.FaceGeometry

/-! # Continuous entries are exactly inward endpoint contacts -/
open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

/-- First date of a closed visit after a nonempty open interval of absence. -/
def visitEntry {I : Type*} [Fintype I] (w : I → ℝ) (r t : ℝ) : Prop :=
  flow w t ∈ enclosingUnitArc r ∧ ∃ d > 0, ∀ u ∈ Ioo (t-d) t, flow w u ∉ enclosingUnitArc r

/-- All phases fitted between the two endpoints give a visit even at a tie. -/
theorem closed_face_visit {I : Type*} [Fintype I] {w : I → ℝ} {r t : ℝ} {i j : I}
    (hr : 0 ≤ r) (h : pairFace (forwardUnitArc r) w r t i j) : flow w t ∈ enclosingUnitArc r := by
  refine mem_iUnion.mpr ⟨i,fun k hki => ?_⟩
  by_cases hkj : k=j
  · subst k; exact ⟨r,⟨hr,le_rfl⟩,h.2.1.symm⟩
  · exact h.2.2 k hki hkj

private theorem closed_face_entry {I : Type*} [Fintype I] {w : I → ℝ} {r t : ℝ} {i j : I}
    (hr : 0 ≤ r) (hs : r < 1/2) (hf : pairFace (forwardUnitArc r) w r t i j) : visitEntry w r t := by
  have hg := sub_pos.mpr hf.1
  refine ⟨closed_face_visit hr hf,(1-2*r)/(w i-w j),div_pos (by linarith only [hs]) hg,?_⟩
  intro u hu hv
  exact (not_le_of_gt ((lt_div_iff₀ hg).mp (show t-u < (1-2*r)/(w i-w j) by linarith only [hu.1])))
    (gap_before_contact w hr hu.2 hv hf.1 hf.2.1)

private theorem spread_fits {I : Type*} [Fintype I] [Nonempty I] (y : I → ℝ) (p : I → UnitAddCircle)
    (r : ℝ) (h : ∀ i j, y j-y i ≤ r)
    (he : ∀ i j, ((y j-y i:ℝ):UnitAddCircle)=p j-p i) : p ∈ enclosingUnitArc r := by
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty y
  refine mem_iUnion.mpr ⟨b,fun k _ => ⟨y k-y b,⟨?_,h b k⟩,he b k⟩⟩
  exact sub_nonneg.mpr (hb ▸ Finset.inf'_le y (Finset.mem_univ k))

/-- At a left boundary some pair spans the entire arc with decreasing
separation. If every such gap opens forward, shifting all real lifts
a little backwards keeps every ordered gap at most r. -/
theorem entry_iff_closed_face {I : Type*} [Fintype I] (w : I → ℝ) {r t : ℝ}
    (hr : 0 ≤ r) (hs : r < 1/2) :
    visitEntry w r t ↔ ∃ i j, pairFace (forwardUnitArc r) w r t i j := by
  classical
  refine ⟨?_,fun ⟨_,_,hf⟩ => closed_face_entry hr hs hf⟩
  rintro ⟨hv,d,hd,hgap⟩
  obtain ⟨b,hb⟩ := mem_iUnion.mp hv
  letI : Nonempty I := ⟨b⟩
  have hl (k : I) : ∃ x ∈ Icc (0:ℝ) r, (x:UnitAddCircle) = flow w t k-flow w t b := by
    by_cases hk : k=b
    · subst k; exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
    · exact hb k hk
  choose x hx he using hl
  have he' (i j : I) : ((x j-x i:ℝ):UnitAddCircle)=flow w t j-flow w t i := by
    rw [AddCircle.coe_sub,he j,he i,sub_sub_sub_cancel_right]
  by_contra! hf
  have hvel (i j : I) (h : x j-x i=r) : w i ≤ w j := by
    by_contra! hneg
    have hz : x i=0 := by linarith only [h,(hx j).2,(hx i).1]
    apply hf i j
    refine ⟨hneg,(he' i j).symm.trans (by rw [h]),fun k _ _ => ?_⟩
    exact ⟨x k-x i,by rw [hz,sub_zero]; exact hx k,he' i k⟩
  let y (u : ℝ) (i : I) := x i+(u-t)*w i
  have hpair (i j : I) : ∀ᶠ u in 𝓝[<] t, y u j-y u i ≤ r := by
    have hh : x j-x i ≤ r := by linarith only [(hx j).2,(hx i).1]
    rcases lt_or_eq_of_le hh with h | h
    · have hc : Continuous (fun u : ℝ => y u j-y u i) := by dsimp only [y]; fun_prop
      have ht : y t j-y t i < r := by simpa only [y,sub_self,zero_mul,add_zero] using h
      exact ((hc.continuousAt.eventually_lt continuousAt_const ht).filter_mono nhdsWithin_le_nhds).mono
        fun _ hu => hu.le
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have hh' := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_lt (show u<t from hu)))
        (sub_nonneg.mpr (hvel i j h))
      dsimp only [y]
      linarith only [hh',h]
  have hall : ∀ᶠ u in 𝓝[<] t, ∀ i j, y u j-y u i ≤ r :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hpair i)
  have hupp : ∀ᶠ u : ℝ in 𝓝[<] t, t-d<u :=
    (lt_mem_nhds (show t-d<t by linarith only [hd])).filter_mono nhdsWithin_le_nhds
  obtain ⟨u,hu,hu',hlo⟩ := (hall.and (hupp.and self_mem_nhdsWithin)).exists
  apply hgap u ⟨hu',hlo⟩
  apply spread_fits (y u) _ r hu
  intro i j
  rw [show y u j-y u i=(x j-x i)+(u-t)*(w j-w i) by dsimp only [y]; ring,AddCircle.coe_add,he']
  simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
  congr 1
  ring

#print axioms entry_iff_closed_face
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
