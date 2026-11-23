import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.ResidenceBound

/-! # Exact maximal residence of sufficiently deep scalar visits -/
open Set Finset
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section
variable {I : Type*}

/-- At the extreme-pair alignment, each spectator has a symmetric interval
whose width depends on its velocity relative to the two edges. -/
def alignmentBox (w : I→ℝ) (q : I) (θ : I→ℝ) (r c : ℝ) : Prop :=
  ∃ y : I→ℝ, ∀ k, (y k : UnitAddCircle)=flow w c k-flow w c q ∧
    |y k|≤r*min (θ k) (1-θ k)

private theorem span_on_segment {θ y : I→ℝ} {r z : ℝ} (hz : z∈Icc (-r) r)
    (hr : 0≤r) (hy : ∀ k, |y k|≤r*min (θ k) (1-θ k)) (i j : I) :
    (y i+z*θ i)-(y j+z*θ j)≤r := by
  have bound (k : I) := abs_le.mp (hy k)
  have lo (k : I) := mul_le_mul_of_nonneg_left (min_le_left (θ k) (1-θ k)) hr
  have hi (k : I) := mul_le_mul_of_nonneg_left (min_le_right (θ k) (1-θ k)) hr
  rcases le_total (θ j) (θ i) with h|h
  · have ht := mul_le_mul_of_nonneg_right hz.2 (sub_nonneg.mpr h)
    linarith only [ht,(bound i).2.trans (hi i),(neg_le_neg (lo j)).trans (bound j).1]
  · have ht := mul_le_mul_of_nonpos_right hz.1 (sub_nonpos.mpr h)
    linarith only [ht,(bound i).2.trans (lo i),(neg_le_neg (hi j)).trans (bound j).1]

variable [Fintype I] [Nonempty I]

/-- An alignment in the spectator box gives a full interval of maximum
possible length. No connected visit can extend it in either direction. -/
theorem maximum_residence_of_alignment (w : I→ℝ) (p q : I) {r c : ℝ}
    (hr : 0<r) (hs : r<1/2) (hw : w q<w p) :
    let W := w p-w q
    let θ := fun k => (w k-w q)/W
    alignmentBox w q θ r c →
      (∀ s∈Icc (c-r/W) (c+r/W), flow w s∈enclosingUnitArc r) ∧
      ∀ a≤c-r/W, ∀ b≥c+r/W, (∀ s∈Icc a b, flow w s∈enclosingUnitArc r) →
        a=c-r/W ∧ b=c+r/W := by
  intro W θ ha
  have hW : 0<W := sub_pos.mpr hw
  obtain ⟨y,hy⟩ := ha
  constructor
  · intro s h
    let z := (s-c)*W
    have hl : -(r/W)≤s-c := by linarith only [h.1]
    have hh : s-c≤r/W := by linarith only [h.2]
    have hz : z∈Icc (-r) r := by
      obtain ⟨hl',hh'⟩ := And.intro (mul_le_mul_of_nonneg_right hl hW.le) (mul_le_mul_of_nonneg_right hh hW.le)
      rw [neg_mul,div_mul_cancel₀ _ hW.ne'] at hl'
      rw [div_mul_cancel₀ _ hW.ne'] at hh'
      exact ⟨hl',hh'⟩
    let f (k : I) := y k+z*θ k
    have hf (k : I) : (f k : UnitAddCircle)=flow w s k-flow w s q := by
      have he : z*θ k=(s-c)*(w k-w q) := by
        change (s-c)*W*((w k-w q)/W)=_
        field_simp [hW.ne']
      change ((y k+z*θ k:ℝ):UnitAddCircle)=_
      rw [AddCircle.coe_add,(hy k).1,he]
      simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
      congr 1
      ring
    obtain ⟨j,_,hj⟩ := exists_mem_eq_inf' univ_nonempty f
    refine mem_iUnion.mpr ⟨j,fun k _ => ⟨f k-f j,⟨?_,?_⟩,?_⟩⟩
    · exact sub_nonneg.mpr (hj.symm.trans_le (inf'_le f (mem_univ k)))
    · exact span_on_segment hz hr.le (fun k => (hy k).2) k j
    · rw [AddCircle.coe_sub,hf,hf,sub_sub_sub_cancel_right]
  · intro a ha b hb hh
    have hpos := div_pos hr hW
    have hl := visit_interval_width hr.le hs (by linarith only [ha,hb,hpos] : a≤b) hh p q
    change (b-a)*W≤2*r at hl
    have he : b-a≤2*(r/W) := calc
      b-a ≤ (2*r)/W := (le_div_iff₀ hW).mpr hl
      _ = 2*(r/W) := by ring
    exact ⟨le_antisymm ha (by linarith only [he,hb]),le_antisymm (by linarith only [he,ha]) hb⟩

/-- Every sufficiently deep visit on a fixed simple finite spectrum lies
in the alignment box of the extreme pair. One depth threshold works at
all times on this spectrum. -/
theorem deep_visit_alignment (w : I→ℝ) (hw : Function.Injective w) (p q : I)
    (he : w q<w p) (hb : ∀ k, w q≤w k ∧ w k≤w p) {r : ℝ} (hr : 0<r) :
    let W := w p-w q
    let θ := fun k => (w k-w q)/W
    ∃ d∈Ioc (0:ℝ) r, ∀ s∈Icc (0:ℝ) d, ∀ v, flow w v∈enclosingUnitArc s →
      ∃ c, |v-c| * W≤s ∧ flow w c p=flow w c q ∧ alignmentBox w q θ r c := by
  classical
  intro W θ
  have hW : 0<W := sub_pos.mpr he
  have hθ (k : I) : θ k∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr (hb k).1) hW.le,
      (div_le_one hW).mpr (sub_le_sub_right (hb k).2 _)⟩
  have hq : θ q=0 := by simp only [θ,sub_self,zero_div]
  have hp : θ p=1 := div_self hW.ne'
  let margin (k : I) := if k=p ∨ k=q then r else r*min (θ k) (1-θ k)
  have hm (k : I) : 0<margin k := by
    by_cases h : k=p ∨ k=q
    · rwa [show margin k=r from if_pos h]
    rw [show margin k=r*min (θ k) (1-θ k) from if_neg h]
    have h₁ := lt_of_le_of_ne (hb k).1 (fun hh => h (Or.inr (hw hh).symm))
    have h₂ := lt_of_le_of_ne (hb k).2 (fun hh => h (Or.inl (hw hh)))
    exact mul_pos hr (lt_min (div_pos (sub_pos.mpr h₁) hW)
      (sub_pos.mpr ((div_lt_one hW).mpr (sub_lt_sub_right h₂ _))))
  obtain ⟨j,_,hj⟩ := exists_mem_eq_inf' univ_nonempty margin
  let d := min r (margin j)
  have hd : 0<d := lt_min hr (hm j)
  refine ⟨d,⟨hd,min_le_left ..⟩,?_⟩
  intro s hs v hv
  obtain ⟨b,hb'⟩ := mem_iUnion.mp hv
  have lift (k : I) : ∃ x∈Icc (0:ℝ) s, (x:UnitAddCircle)=flow w v k-flow w v b := by
    by_cases h : k=b
    · subst k; exact ⟨0,⟨le_rfl,hs.1⟩,by simp⟩
    · exact hb' k h
  choose x hx hx' using lift
  let c := v-(x p-x q)/W
  let y (k : I) := x k-((1-θ k)*x q+θ k*x p)
  have hz (k : I) : |y k|≤s := by
    have h₀ := (hθ k).1
    have h₁ := sub_nonneg.mpr (hθ k).2
    have hl := add_nonneg (mul_nonneg h₁ (hx q).1) (mul_nonneg h₀ (hx p).1)
    have hu := add_le_add (mul_le_mul_of_nonneg_left (hx q).2 h₁) (mul_le_mul_of_nonneg_left (hx p).2 h₀)
    change |x k-_|≤s
    exact abs_le.mpr ⟨by linarith only [hu,(hx k).1],by linarith only [hl,(hx k).2]⟩
  have hphase (k : I) : (y k : UnitAddCircle)=flow w c k-flow w c q := by
    have hy : y k=(x k-x q)+(c-v)*(w k-w q) := by
      dsimp only [y,c,θ]
      ring
    rw [hy,AddCircle.coe_add,AddCircle.coe_sub,hx',hx',sub_sub_sub_cancel_right]
    simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
    congr 1
    ring
  have hyp : y p=0 := by simp [y,hp]
  have hyq : y q=0 := by simp [y,hq]
  refine ⟨c,?_,?_,y,fun k => ⟨hphase k,?_⟩⟩
  · rw [show v-c=(x p-x q)/W by dsimp only [c]; ring,abs_div,abs_of_pos hW,div_mul_cancel₀ _ hW.ne']
    exact abs_le.mpr ⟨by linarith only [(hx p).1,(hx q).2],by linarith only [(hx p).2,(hx q).1]⟩
  · have hh := hphase p
    rw [hyp,AddCircle.coe_zero] at hh
    exact sub_eq_zero.mp hh.symm
  · by_cases h : k=p ∨ k=q
    · rcases h with rfl|rfl <;> simp [hyp,hyq,hp,hq]
    · have h' := (min_le_right r (margin j)).trans (hj.symm.trans_le (inf'_le margin (mem_univ k)))
      exact ((hz k).trans hs.2).trans (h'.trans_eq (if_neg h))

#print axioms deep_visit_alignment
#print axioms maximum_residence_of_alignment
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
