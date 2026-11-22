import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryIsolation

/-! # Stability of the first scalar visit at a regular pair of endpoints -/
open Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity
noncomputable section
open EmptyVisitFlux
variable {I : Type*} [Fintype I]

/-- Varying the frequencies while holding the observation origin fixed
moves a regular first entry exactly inversely to its endpoint gap.
All the other coordinates can vary freely in a neighborhood. -/
theorem first_face_stable {w₀ : I→ℝ} {a v r : ℝ} {i j : I} (hr : 0 ≤ r) (hs : r < 1/2)
    (ha : a < v) (hf : inwardFace w₀ r v i j)
    (hfirst : ∀ t∈Ico a v, flow w₀ t ∉ enclosingUnitArc r) :
    ∀ᶠ w : I→ℝ in 𝓝 w₀,
      IsLeast {t : ℝ | a ≤ t ∧ flow w t∈enclosingUnitArc r}
        (v*(w₀ i-w₀ j)/(w i-w j)) := by
  classical
  let g (w : I→ℝ) := w i-w j
  let T (w : I→ℝ) := v*g w₀/g w
  have hg : 0 < g w₀ := sub_pos.mpr hf.1
  have hgcont : Continuous g := (continuous_apply i).sub (continuous_apply j)
  have hTcont : ContinuousAt T w₀ := continuousAt_const.div hgcont.continuousAt hg.ne'
  have hTv : T w₀=v := mul_div_cancel_right₀ _ hg.ne'
  have hc (k : I) : ContinuousAt (fun w => flow w (T w) k) w₀ := by
    change ContinuousAt (fun w : I→ℝ => ((T w*w k:ℝ):UnitAddCircle)) w₀
    exact (AddCircle.continuous_mk' 1).continuousAt.comp (hTcont.mul (continuous_apply k).continuousAt)
  have hopen : IsOpen (((↑) : ℝ → UnitAddCircle) '' Ioo 0 r) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hint (k : I) : ∀ᶠ w in 𝓝 w₀, k≠i → k≠j →
      flow w (T w) k-flow w (T w) i ∈ ((↑) : ℝ→UnitAddCircle) '' Ioo 0 r := by
    by_cases hki : k=i
    · exact Eventually.of_forall fun _ hk => (hk hki).elim
    by_cases hkj : k=j
    · exact Eventually.of_forall fun _ _ hk => (hk hkj).elim
    have hmem := hf.2.2 k hki hkj
    rw [←hTv] at hmem
    filter_upwards [((hc k).sub (hc i)).tendsto (hopen.mem_nhds hmem)] with w hw
    exact fun _ _ => hw
  let b := v-(1-2*r)/(2*g w₀)
  have hn : 0 < 1-2*r := by linarith only [hs]
  have hb : b < v := sub_lt_self _ (div_pos hn (mul_pos two_pos hg))
  have hmargin : (T w₀-b)*g w₀ < 1-2*r := by
    rw [hTv,show v-b=(1-2*r)/(2*g w₀) by dsimp only [b]; ring]
    field_simp
    linarith only [hn]
  let S : Set ((I→ℝ) × Icc a b) := {p | flow p.1 p.2.val∈enclosingUnitArc r}
  have hS : IsClosed S := by
    apply (isClosed_enclosingUnitArc r).preimage
    apply continuous_pi
    intro k
    exact (AddCircle.continuous_mk' 1).comp
      ((continuous_subtype_val.comp continuous_snd).mul ((continuous_apply k).comp continuous_fst))
  have haway : w₀ ∉ Prod.fst '' S := by
    rintro ⟨⟨w,t⟩,ht,hw⟩
    change w=w₀ at hw
    change flow w t.val∈enclosingUnitArc r at ht
    rw [hw] at ht
    exact hfirst t ⟨t.2.1,t.2.2.trans_lt hb⟩ ht
  have hne := (isClosedMap_fst_of_compactSpace _ hS).isOpen_compl.mem_nhds haway
  have hgap : ContinuousAt (fun w => (T w-b)*g w) w₀ :=
    (hTcont.sub continuousAt_const).mul hgcont.continuousAt
  filter_upwards [hne,hgap.tendsto.eventually_lt_const hmargin,
    hgcont.continuousAt.tendsto.eventually_const_lt hg,
    hTcont.tendsto.eventually_const_lt (ha.trans_eq hTv.symm),Filter.eventually_all.mpr hint] with w hno hm hpos hafter hinterior
  have hshift : T w*(w j-w i)=v*(w₀ j-w₀ i) := by
    rw [show w j-w i= -g w by dsimp [g]; ring,show w₀ j-w₀ i= -g w₀ by dsimp [g]; ring]
    dsimp only [T]
    field_simp [hpos.ne']
  have hf' : inwardFace w r (T w) i j := by
    refine ⟨sub_pos.mp hpos,?_,hinterior⟩
    rw [←hf.2.1]
    simp only [flow,←AddCircle.coe_sub,←mul_sub,hshift]
  refine ⟨⟨hafter.le,inwardFace_visit hr hf'⟩,?_⟩
  rintro t ⟨hat,ht⟩
  by_contra! hbefore
  by_cases htb : t ≤ b
  · exact hno ⟨(w,⟨t,hat,htb⟩),ht,rfl⟩
  · have hlim := gap_before_contact w hr hbefore ht hf'.1 hf'.2.1
    exact (not_le_of_gt ((mul_lt_mul_of_pos_right (sub_lt_sub_left (lt_of_not_ge htb) _) hpos).trans hm)) hlim

#print axioms first_face_stable
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity
