import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.ResidenceBound

/-! # Speed of the defining pair of a scalar excursion reaching a smaller arc -/
open Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section
variable {I : Type*}

private theorem relative_lift {w : I→ℝ} {u r : ℝ} (hr : 0≤r)
    (hv : flow w u∈enclosingUnitArc r) (i j : I) :
    ∃ x∈Icc (-r) r, (x:UnitAddCircle)=flow w u i-flow w u j := by
  obtain ⟨b,hb⟩ := mem_iUnion.mp hv
  have lift (k : I) : ∃ y∈Icc (0:ℝ) r, (y:UnitAddCircle)=flow w u k-flow w u b := by
    by_cases he : k=b
    · subst k; exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
    · exact hb k he
  obtain ⟨x,hx,he⟩ := lift i
  obtain ⟨y,hy,hf⟩ := lift j
  exact ⟨x-y,⟨by linarith only [hx.1,hy.2],by linarith only [hx.2,hy.1]⟩,
    by rw [AddCircle.coe_sub,he,hf,sub_sub_sub_cancel_right]⟩

private theorem transport_lift (w : I→ℝ) (i j : I) (a b x : ℝ)
    (hx : (x:UnitAddCircle)=flow w a i-flow w a j) :
    ((x+(b-a)*(w i-w j):ℝ):UnitAddCircle)=flow w b i-flow w b j := by
  rw [AddCircle.coe_add,hx]
  simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
  congr 1
  ring

/-- From an outer contact to any later inner visit the closing pair
must travel at least the difference of the widths. -/
theorem closing_travel_to_depth (w : I→ℝ) {i j : I} {r d a b : ℝ}
    (hd : 0≤d) (hdr : d≤r) (hr : r<1/2) (hab : a≤b) (hg : w j<w i)
    (he : flow w a j-flow w a i=(r:UnitAddCircle)) (hb : flow w b∈enclosingUnitArc d) :
    r-d ≤ (b-a)*(w i-w j) := by
  obtain ⟨y,hy,hy'⟩ := relative_lift hd hb j i
  let z := r+(b-a)*(w j-w i)
  have hz : (z:UnitAddCircle)=(y:UnitAddCircle) := (transport_lift w j i a b r he.symm).trans hy'.symm
  by_contra! h
  have hzr : z≤r := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) (sub_nonpos.mpr hg.le))
  have hzd : d<z := by
    dsimp only [z]
    rw [show w j-w i= -(w i-w j) by ring,mul_neg]
    linarith only [h]
  have hz' : z∈Ico (-r) (-r+1) := ⟨by linarith only [hzd,hd,hdr],by linarith only [hzr,hr]⟩
  have hy'' : y∈Ico (-r) (-r+1) := ⟨(neg_le_neg hdr).trans hy.1,by linarith only [hy.2,hdr,hr]⟩
  exact (hy.2.trans_lt hzd).ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico hz' hy'').mp hz).symm

/-- Within one outer excursion the lifted relative phase cannot wind.
If the terminal span is at most d, its travel is bounded by r+d. -/
theorem travel_until_depth (w : I→ℝ) {r d a b : ℝ} (hd : 0≤d) (hdr : d≤r) (hr : r<1/2)
    (hab : a≤b) (hv : ∀ s∈Icc a b, flow w s∈enclosingUnitArc r)
    (hb : flow w b∈enclosingUnitArc d) (p q : I) :
    (b-a)*(w p-w q) ≤ r+d := by
  obtain ⟨x,hx,hx'⟩ := relative_lift (hd.trans hdr) (hv a ⟨le_rfl,hab⟩) p q
  obtain ⟨z,hz,hz'⟩ := relative_lift hd hb p q
  let g := w p-w q
  by_cases hg : 0<g
  · have hend : x+(b-a)*g ≤ r := by
      by_contra! h
      obtain ⟨y,hy,hy'⟩ := exists_between (lt_min (show r<1-r by linarith only [hr]) h)
      let s := a+(y-x)/g
      have hs : s∈Icc a b := by
        have h₁ := div_nonneg (sub_nonneg.mpr (hx.2.trans hy.le)) hg.le
        have h₂ : (y-x)/g≤b-a := (div_le_iff₀ hg).mpr (by linarith only [hy'.trans_le (min_le_right ..)])
        exact ⟨by dsimp only [s]; linarith only [h₁],by dsimp only [s]; linarith only [h₂]⟩
      obtain ⟨z',hz₀,hz₁⟩ := relative_lift (hd.trans hdr) (hv s hs) p q
      have hs' : x+(s-a)*(w p-w q)=y := by change x+(a+(y-x)/g-a)*g=y; field_simp [hg.ne']; ring
      have hh := (transport_lift w p q a s x hx').trans hz₁.symm
      rw [hs'] at hh
      have hy₀ : y∈Ico (-r) (-r+1) := ⟨by linarith only [hy,hdr,hd],by linarith only [hy'.trans_le (min_le_left ..)]⟩
      have hz₂ : z'∈Ico (-r) (-r+1) := ⟨hz₀.1,by linarith only [hz₀.2,hr]⟩
      exact (hz₀.2.trans_lt hy).ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico hy₀ hz₂).mp hh).symm
    have hxlo := mul_nonneg (sub_nonneg.mpr hab) hg.le
    have hY : x+(b-a)*g∈Ico (-r) (-r+1) := ⟨by linarith only [hx.1,hxlo],by linarith only [hend,hr]⟩
    have hZ : z∈Ico (-r) (-r+1) := ⟨(neg_le_neg hdr).trans hz.1,by linarith only [hz.2,hdr,hr]⟩
    have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico hY hZ).mp ((transport_lift w p q a b x hx').trans hz'.symm)
    change (b-a)*g ≤ r+d
    linarith only [he,hx.1,hz.2]
  · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) (le_of_not_gt hg)).trans (add_nonneg (hd.trans hdr) hd)

/-- Every outer entry that reaches d has closing speed at least
(r−d)/(r+d) times the full velocity diameter. -/
theorem deep_entry_speed (w : I→ℝ) {i j : I} {r d a b : ℝ} (hd : 0≤d) (hdr : d≤r) (hr : r<1/2)
    (hab : a≤b) (hf : pairFace (forwardUnitArc r) w r a i j)
    (hv : ∀ s∈Icc a b, flow w s∈enclosingUnitArc r) (hb : flow w b∈enclosingUnitArc d) (p q : I) :
    (r-d)*(w p-w q) ≤ (r+d)*(w i-w j) := by
  have h₁ := closing_travel_to_depth w hd hdr hr hab hf.1 hf.2.1 hb
  have h₂ := travel_until_depth w hd hdr hr hab hv hb p q
  rcases le_total (w q) (w p) with h|h
  · calc _ ≤ ((b-a)*(w i-w j))*(w p-w q) := mul_le_mul_of_nonneg_right h₁ (sub_nonneg.mpr h)
         _ = ((b-a)*(w p-w q))*(w i-w j) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right h₂ (sub_nonneg.mpr hf.1.le)
  · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hdr) (sub_nonpos.mpr h)).trans
      (mul_nonneg (add_nonneg (hd.trans hdr) hd) (sub_nonneg.mpr hf.1.le))

#print axioms deep_entry_speed
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
