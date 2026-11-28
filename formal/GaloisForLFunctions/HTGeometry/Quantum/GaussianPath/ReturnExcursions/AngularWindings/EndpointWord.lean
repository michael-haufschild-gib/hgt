import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.InverseTime

/-! # Recovering the relative winding vector from its extremal integer -/

open Set
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
noncomputable section

/-- Interpolate the endpoint circuit phases after fixing their relative winding. -/
def targetWord {I : Type*} (A b : I → ℝ) (l u : I) (N : ℤ) (i : I) : ℝ :=
  ((A i-A l)/(A u-A l))*((N:ℝ)+b u-b l)-(b i-b l)

/-- The integer reconstruction uses the same circuit phases for every choice
of the crossing origin and global phase. -/
theorem targetWord_shift {I : Type*} (A b : I → ℝ) (l u i : I) (N : ℤ) (σ φ : ℝ)
    (hne : A u≠A l) :
    targetWord A (fun j => b j-σ*A j+φ) l u N i=targetWord A b l u N i := by
  dsimp only [targetWord]
  field_simp [sub_ne_zero.mpr hne]
  ring

/-- The extremal winding integer fixes every relative winding to within the
original arc width. The observation time appears only in its scalar index bound. -/
theorem endpoint_word {I : Type*} (A b : I → ℝ) (m : I → ℤ) (l u : I) (t p x : ℝ)
    (hgap : A l<A u) (hext : ∀ i, A i∈Icc (A l) (A u))
    (h : ∀ i, |t*A i-(b i+(m i:ℝ))-p|≤x/2) :
    let N := m u-m l
    |t*(A u-A l)-(b u-b l)-(N:ℝ)|≤x ∧
      ∀ i, |targetWord A b l u N i-((m i-m l:ℤ):ℝ)|≤x := by
  intro N
  let e (i : I) := t*A i-(b i+(m i:ℝ))-p
  have hlo (i) : -(x/2)≤e i := (abs_le.mp (h i)).1
  have hup (i) : e i≤x/2 := (abs_le.mp (h i)).2
  constructor
  · have he : t*(A u-A l)-(b u-b l)-(N:ℝ)=e u-e l := by dsimp only [N,e]; push_cast; ring
    rw [he]
    exact abs_le.mpr ⟨by linarith only [hlo u,hup l],by linarith only [hup u,hlo l]⟩
  · intro i
    let q := (A i-A l)/(A u-A l)
    have hg := sub_pos.mpr hgap
    have hq : q∈Icc (0:ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr (hext i).1) hg.le,(div_le_one hg).mpr (sub_le_sub_right (hext i).2 _)⟩
    have hc : (1-q)*e l+q*e u∈Icc (-(x/2)) (x/2) :=
      convex_Icc _ _ ⟨hlo l,hup l⟩ ⟨hlo u,hup u⟩ (sub_nonneg.mpr hq.2) hq.1 (sub_add_cancel ..)
    have he : targetWord A b l u N i-((m i-m l:ℤ):ℝ)=e i-((1-q)*e l+q*e u) := by
      dsimp only [targetWord,N,e,q]
      push_cast
      field_simp [hg.ne']
      ring
    rw [he]
    exact abs_le.mpr ⟨by linarith only [hlo i,hc.2],by linarith only [hup i,hc.1]⟩

/-- At every sub-semicircle width, the relative winding equals an explicit rounded
integer. All levels use the same extremal winding, even at an adaptive visit date. -/
theorem endpoint_word_round {I : Type*} (A b : I → ℝ) (m : I → ℤ) (l u : I) (t p x : ℝ)
    (hx : x<1/2) (hgap : A l<A u) (hext : ∀ i, A i∈Icc (A l) (A u))
    (h : ∀ i, |t*A i-(b i+(m i:ℝ))-p|≤x/2) (i : I) :
    ⌊targetWord A b l u (m u-m l) i+1/2⌋=m i-m l := by
  have hnear := abs_lt.mp (((endpoint_word A b m l u t p x hgap hext h).2 i).trans_lt hx)
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith only [hnear.1,hnear.2]

#print axioms endpoint_word_round
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
