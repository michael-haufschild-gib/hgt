import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.FaceGeometry

/-! # Linear inequalities for the entire visit in one extreme-gap clock cell -/
open Set Finset
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
noncomputable section

/-- Centered representative in turns. -/
def residual (x : ℝ) : ℝ := (AddCircle.equivIco (1:ℝ) (-(1/2)) (x:UnitAddCircle):ℝ)

private theorem coe_residual (x : ℝ) : (residual x : UnitAddCircle)=(x:UnitAddCircle) :=
  AddCircle.coe_equivIco

private theorem residual_from_lift {x y : ℝ} (hy : y∈Ico (-(1/2):ℝ) (1/2))
    (he : (y:UnitAddCircle)=(x:UnitAddCircle)) : residual x=y := by
  unfold residual
  rw [←he]
  exact AddCircle.equivIco_coe_of_mem ⟨hy.1,by linarith only [hy.2]⟩

private theorem coe_int_zero (n : ℤ) : ((n:ℝ):UnitAddCircle)=0 :=
  (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨n,by simp [zsmul_eq_mul]⟩

theorem residual_int (n : ℤ) : residual (n:ℝ)=0 :=
  residual_from_lift (by constructor <;> norm_num) (by rw [coe_int_zero,AddCircle.coe_zero])

/-- The offset in turns is constrained by all ordered pairs of lifted
spectator phases. The extreme lines are included among these pairs. -/
def offsets {I : Type*} (θ : I→ℝ) (n : ℤ) (r : ℝ) : Set ℝ :=
  {z | ∀ i j, (residual (n*θ i)+z*θ i)-(residual (n*θ j)+z*θ j)≤r}

/-- A cell has one convex interval of admissible offsets, possibly empty. -/
theorem offsets_convex {I : Type*} (θ : I→ℝ) (n : ℤ) (r : ℝ) : Convex ℝ (offsets θ n r) := by
  intro x hx y hy a b ha hb hab i j
  have h₁ := mul_le_mul_of_nonneg_left (hx i j) ha
  have h₂ := mul_le_mul_of_nonneg_left (hy i j) hb
  change (_+(a*x+b*y)*θ i)-(_+(a*x+b*y)*θ j)≤r
  linear_combination h₁+h₂+(r-residual (n*θ i)+residual (n*θ j))*hab

theorem offsets_closed {I : Type*} (θ : I→ℝ) (n : ℤ) (r : ℝ) : IsClosed (offsets θ n r) := by
  have he : offsets θ n r=⋂ i, ⋂ j, {z : ℝ |
      (residual (n*θ i)+z*θ i)-(residual (n*θ j)+z*θ j)≤r} := by
    ext z
    simp only [offsets,mem_iInter,mem_setOf_eq]
  rw [he]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le ((continuous_const.add (continuous_id.mul_const (θ i))).sub
      (continuous_const.add (continuous_id.mul_const (θ j)))) continuous_const

/-- Extreme rows bound every admissible offset by the tolerance itself. -/
theorem offsets_bound {I : Type*} {θ : I→ℝ} {p q : I} (hp : θ p=1) (hq : θ q=0)
    (n : ℤ) (r : ℝ) : offsets θ n r ⊆ Icc (-r) r := by
  intro z h
  have h₁ := h p q
  have h₂ := h q p
  have h₀ : residual 0=0 := by simpa only [Int.cast_zero] using residual_int 0
  simp only [hp,hq,mul_one,mul_zero,residual_int,h₀,zero_add,add_zero,sub_zero,zero_sub] at h₁ h₂
  exact ⟨neg_le.mp h₂,h₁⟩

/-- On the cell indexed by n, an actual scalar visit is exactly the
ordinary real span test on the centered residues of n times the normalized
gaps. This includes endpoint ties and every subsemicircle tolerance. -/
theorem visit_iff_offsets {I : Type*} [Fintype I] [Nonempty I] (w : I→ℝ) (p q : I)
    (he : w q<w p) (hb : ∀ i, w q≤w i ∧ w i≤w p) {r : ℝ} (hr : 0≤r) (hs : r<1/2)
    (n : ℤ) {z : ℝ} (hz : z∈Ico (-(1/2):ℝ) (1/2)) :
    let W := w p-w q
    let θ := fun i => (w i-w q)/W
    let t := ((n:ℝ)+z)/W
    flow w t∈enclosingUnitArc r ↔ z∈offsets θ n r := by
  intro W θ t
  have hw : 0<W := sub_pos.mpr he
  have hp : θ p=1 := div_self hw.ne'
  have hθ (i : I) : θ i∈Icc (0:ℝ) 1 := ⟨div_nonneg (sub_nonneg.mpr (hb i).1) hw.le,
    (div_le_one hw).mpr (sub_le_sub_right (hb i).2 _)⟩
  let f (i : I) := residual (n*θ i)+z*θ i
  have phase (i : I) : (f i : UnitAddCircle)=flow w t i-flow w t q := by
    change ((residual (n*θ i)+z*θ i:ℝ):UnitAddCircle)=_
    rw [AddCircle.coe_add,coe_residual,←AddCircle.coe_add]
    simp only [flow,←AddCircle.coe_sub]
    congr 1
    dsimp only [θ,t]
    ring
  have fp : f p=z := by simp only [f,hp,mul_one,residual_int,zero_add]
  constructor
  · intro hv
    obtain ⟨b,hb'⟩ := mem_iUnion.mp hv
    have lift (i : I) : ∃ x∈Icc (0:ℝ) r, (x:UnitAddCircle)=flow w t i-flow w t b := by
      by_cases h : i=b
      · subst i; exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
      · exact hb' i h
    choose x hx hx' using lift
    have rel (i : I) : ((x i-x q:ℝ):UnitAddCircle)=(f i:UnitAddCircle) := by
      rw [AddCircle.coe_sub,hx',hx',sub_sub_sub_cancel_right,phase]
    have mem {y : ℝ} (hl : -r≤y) (hu : y≤r) : y∈Ico (-(1/2):ℝ) (1/2) :=
      ⟨(neg_le_neg hs.le).trans hl,hu.trans_lt hs⟩
    have hxp : x p-x q=z := by
      have hh := rel p
      rw [fp] at hh
      apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a:= -(1/2:ℝ)) _ _).mp hh
      · exact ⟨by linarith only [(hx p).1,(hx q).2,hs],by linarith only [(hx p).2,(hx q).1,hs]⟩
      · exact ⟨hz.1,by linarith only [hz.2]⟩
    have hf (i : I) : f i=x i-x q := by
      let y := x i-((1-θ i)*x q+θ i*x p)
      have hl := add_nonneg (mul_nonneg (sub_nonneg.mpr (hθ i).2) (hx q).1) (mul_nonneg (hθ i).1 (hx p).1)
      have hu := add_le_add (mul_le_mul_of_nonneg_left (hx q).2 (sub_nonneg.mpr (hθ i).2))
        (mul_le_mul_of_nonneg_left (hx p).2 (hθ i).1)
      have hy : y∈Ico (-(1/2):ℝ) (1/2) := mem (by dsimp only [y]; linarith only [hu,(hx i).1])
        (by dsimp only [y]; linarith only [hl,(hx i).2])
      have hy' : y=(x i-x q)-z*θ i := by dsimp only [y]; rw [←hxp]; ring
      have hyc : (y:UnitAddCircle)=((n*θ i:ℝ):UnitAddCircle) := by
        rw [hy',AddCircle.coe_sub,rel]
        change ((residual (n*θ i)+z*θ i:ℝ):UnitAddCircle)-_ = _
        rw [AddCircle.coe_add,add_sub_cancel_right,coe_residual]
      change residual (n*θ i)+z*θ i=_
      rw [residual_from_lift hy hyc,hy',sub_add_cancel]
    intro i j
    change f i-f j≤r
    rw [hf,hf,sub_sub_sub_cancel_right]
    linarith only [(hx i).2,(hx j).1]
  · intro hv
    obtain ⟨j,_,hj⟩ := exists_mem_eq_inf' univ_nonempty f
    refine mem_iUnion.mpr ⟨j,fun i _ => ⟨f i-f j,⟨sub_nonneg.mpr (hj.symm.trans_le (inf'_le f (mem_univ i))),
      hv i j⟩,?_⟩⟩
    rw [AddCircle.coe_sub,phase,phase,sub_sub_sub_cancel_right]

#print axioms visit_iff_offsets
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
