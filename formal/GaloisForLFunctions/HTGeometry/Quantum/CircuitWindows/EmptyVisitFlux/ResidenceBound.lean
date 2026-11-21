import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.FaceGeometry

/-! # Sharp maximum duration of a continuous enclosing-arc visit -/
open Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

private theorem pair_lift {I : Type*} [Fintype I] {w : I → ℝ}
    {r t : ℝ} (hr : 0 ≤ r) (hv : flow w t ∈ enclosingUnitArc r) (i j : I) :
    ∃ x ∈ Icc (-r) r, (x:UnitAddCircle)=flow w t i-flow w t j := by
  obtain ⟨b,hb⟩ := mem_iUnion.mp hv
  have lift (k : I) : ∃ y ∈ Icc (0:ℝ) r, (y:UnitAddCircle)=flow w t k-flow w t b := by
    by_cases h : k=b
    · subst k; exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
    · exact hb k h
  obtain ⟨x,hx,he⟩ := lift i
  obtain ⟨y,hy,hf⟩ := lift j
  exact ⟨x-y,⟨by linarith only [hx.1,hy.2],by linarith only [hx.2,hy.1]⟩,
    by rw [AddCircle.coe_sub,he,hf,sub_sub_sub_cancel_right]⟩

/-- A visit interval cannot carry any relative phase by more than two
enclosing-arc widths. Relative phase is continuous even across full turns. -/
theorem visit_interval_width {I : Type*} [Fintype I] {w : I → ℝ} {a b r : ℝ}
    (hr : 0 ≤ r) (hs : r < 1/2) (hab : a ≤ b)
    (hv : ∀ t ∈ Icc a b, flow w t ∈ enclosingUnitArc r) (i j : I) :
    (b-a)*(w i-w j) ≤ 2*r := by
  by_contra! h
  obtain ⟨x,hx,h0⟩ := pair_lift hr (hv a ⟨le_rfl,hab⟩) i j
  have hg : 0 < w i-w j := by
    by_contra! hn
    linarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) hn,h,hr]
  have hcut : r < min (1-r) (x+(b-a)*(w i-w j)) :=
    lt_min (by linarith only [hs]) (by linarith only [h,hx.1])
  obtain ⟨y,hy,hz⟩ := exists_between hcut
  let t := a+(y-x)/(w i-w j)
  have ht : t ∈ Icc a b := by
    have h1 : 0 ≤ (y-x)/(w i-w j) := div_nonneg (sub_nonneg.mpr (hx.2.trans hy.le)) hg.le
    have h2 : (y-x)/(w i-w j) ≤ b-a := (div_le_iff₀ hg).mpr (by
      linarith only [hz.trans_le (min_le_right (1-r) _)])
    exact ⟨by dsimp only [t]; linarith only [h1],by dsimp only [t]; linarith only [h2]⟩
  obtain ⟨z,hw,he⟩ := pair_lift hr (hv t ht) i j
  have heq : (z:UnitAddCircle)=(y:UnitAddCircle) := by
    rw [show y=x+(t-a)*(w i-w j) by dsimp only [t]; field_simp; ring,AddCircle.coe_add,h0,he]
    simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
    congr 1
    ring
  have hey := hz.trans_le (min_le_left (1-r) _)
  have hzu : z ∈ Ico (-r) (-r+1) := ⟨hw.1,by linarith only [hw.2,hs]⟩
  have hyu : y ∈ Ico (-r) (-r+1) := ⟨by linarith only [hr,hy],by linarith only [hey]⟩
  exact (hw.2.trans_lt hy).ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico hzu hyu).mp heq)

/-- The interval symmetric about the identity attains the maximum possible
residence length, given by two arc widths divided by the velocity width. -/
theorem longest_visit {I : Type*} [Fintype I] [Nonempty I] (w : I → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hs : r < 1/2) :
    let W := Finset.univ.sup' Finset.univ_nonempty w-Finset.univ.inf' Finset.univ_nonempty w
    (∀ a b : ℝ, a≤b → (∀ t ∈ Icc a b, flow w t ∈ enclosingUnitArc r) → (b-a)*W ≤ 2*r) ∧
      (∀ t : ℝ, |t| *W ≤ r → flow w t ∈ enclosingUnitArc r) := by
  intro W
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty w
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty w
  have he : W=w i-w j := by dsimp only [W]; rw [hi,hj]
  have hb (k : I) : w j ≤ w k ∧ w k ≤ w i := by
    rw [←hi,←hj]
    exact ⟨Finset.inf'_le w (Finset.mem_univ k),Finset.le_sup' w (Finset.mem_univ k)⟩
  constructor
  · intro a b hab hv
    rw [he]
    exact visit_interval_width hr hs hab hv i j
  · intro t ht
    rw [he] at ht
    have cover (b : I) (h : ∀ k, t*(w k-w b) ∈ Icc 0 r) : flow w t ∈ enclosingUnitArc r := by
      refine mem_iUnion.mpr ⟨b,fun k _ => ⟨_,h k,?_⟩⟩
      simp only [flow,←AddCircle.coe_sub]
      congr 1
      ring
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h] at ht
      exact cover j fun k => ⟨mul_nonneg h (sub_nonneg.mpr (hb k).1),
        (mul_le_mul_of_nonneg_left (sub_le_sub_right (hb k).2 _) h).trans ht⟩
    · rw [abs_of_nonpos h] at ht
      apply cover i
      intro k
      refine ⟨mul_nonneg_of_nonpos_of_nonpos h (sub_nonpos.mpr (hb k).2),?_⟩
      have hh := mul_le_mul_of_nonpos_left (sub_le_sub_right (hb k).1 (w i)) h
      linarith only [hh,ht]

#print axioms longest_visit
#print axioms visit_interval_width
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
