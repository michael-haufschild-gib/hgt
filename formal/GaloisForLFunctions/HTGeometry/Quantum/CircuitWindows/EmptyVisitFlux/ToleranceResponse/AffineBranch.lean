import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryIsolation

/-! # Motion of a strict scalar entry under a change in arc width -/
open Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

/-- At a strict entry the two closing lines stay the unique endpoints when
the tolerance varies. The entry date is affine, with slope minus the
reciprocal of their relative velocity in turns per unit physical time. -/
theorem strict_entry_width_branch {I : Type*} [Fintype I] (w : I→ℝ) {i j : I} {r t : ℝ}
    (hr : 0<r) (hs : r<1/2) (hf : inwardFace w r t i j) :
    ∀ᶠ q in 𝓝 r, let u := t+(r-q)/(w i-w j)
      inwardFace w q u i j ∧ visitEntry w q u ∧
      ∀ b c, flow w u c-flow w u b=(q:UnitAddCircle) → b=i ∧ c=j := by
  let d (q : ℝ) := (r-q)/(w i-w j)
  have hd : d r=0 := by simp only [d,sub_self,zero_div]
  have hc : Continuous d := (continuous_const.sub continuous_id).div_const _
  have hg := (sub_pos.mpr hf.1).ne'
  have hshift (k : I) (q : ℝ) : flow w (t+d q) k-flow w (t+d q) i =
      (flow w t k-flow w t i)+((d q*(w k-w i):ℝ):UnitAddCircle) := by
    simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
    congr 1
    ring
  have hspec (k : I) : ∀ᶠ q in 𝓝 r, k≠i → k≠j →
      flow w (t+d q) k-flow w (t+d q) i∈((↑) : ℝ→UnitAddCircle) '' Ioo 0 q := by
    by_cases hki : k=i
    · exact Eventually.of_forall fun _ h => (h hki).elim
    by_cases hkj : k=j
    · exact Eventually.of_forall fun _ _ h => (h hkj).elim
    obtain ⟨y,hy,he⟩ := hf.2.2 k hki hkj
    let f (q : ℝ) := y+d q*(w k-w i)
    have hcont : Continuous f := continuous_const.add (hc.mul continuous_const)
    have heq : f r=y := by simp only [f,hd,zero_mul,add_zero]
    have h₀ := hcont.continuousAt.tendsto.eventually_const_lt (heq.symm ▸ hy.1 : 0<f r)
    have h₁ : ∀ᶠ q in 𝓝 r, f q<q :=
      (hcont.continuousAt.tendsto.eventually_lt continuousAt_id.tendsto (heq.symm ▸ hy.2 : f r<r))
    filter_upwards [h₀,h₁] with q hq hq'
    intro _ _
    refine ⟨f q,⟨hq,hq'⟩,?_⟩
    rw [hshift,←he]
    exact AddCircle.coe_add ..
  filter_upwards [lt_mem_nhds hr,gt_mem_nhds hs,eventually_all.mpr hspec] with q hq hq' h
  let u := t+d q
  have hdiff : d q*(w j-w i)=q-r := by
    dsimp only [d]
    rw [show w j-w i= -(w i-w j) by ring,mul_neg,div_mul_cancel₀ _ hg]
    ring
  have hf' : inwardFace w q u i j := by
    refine ⟨hf.1,?_,h⟩
    rw [show u=t+d q from rfl,hshift,hf.2.1,hdiff,←AddCircle.coe_add,show r+(q-r)=q by ring]
  refine ⟨hf',(entry_iff_closed_face w hq.le hq').mpr ⟨i,j,hf'.1,hf'.2.1,?_⟩,
    fun _ _ => inward_endpoints_unique hq hq' hf'⟩
  exact fun k hki hkj => image_mono Ioo_subset_Icc_self (hf'.2.2 k hki hkj)

#print axioms strict_entry_width_branch
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
