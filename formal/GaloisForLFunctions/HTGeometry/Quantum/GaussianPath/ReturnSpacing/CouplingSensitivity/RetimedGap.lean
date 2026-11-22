import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.ResidenceBound

/-! # Spectral rigidity of continuously retimed scalar visits -/
open Set
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.CouplingSensitivity
noncomputable section
variable {I : Type*} [Fintype I]

private theorem pair_representative {p : I→ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hp : (fun i => (p i:UnitAddCircle)) ∈ enclosingUnitArc r) (i j : I) :
    ∃ x∈Icc (-r) r, (x:UnitAddCircle)=((p i-p j:ℝ):UnitAddCircle) := by
  obtain ⟨b,hb⟩ := mem_iUnion.mp hp
  have lift (k : I) : ∃ y∈Icc (0:ℝ) r, (y:UnitAddCircle)=(p k:UnitAddCircle)-(p b:UnitAddCircle) := by
    by_cases he : k=b
    · subst k; exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
    · exact hb k he
  obtain ⟨x,hx,he⟩ := lift i
  obtain ⟨y,hy,hf⟩ := lift j
  refine ⟨x-y,⟨by linarith only [hx.1,hy.2],by linarith only [hx.2,hy.1]⟩,?_⟩
  rw [AddCircle.coe_sub,he,hf,sub_sub_sub_cancel_right,AddCircle.coe_sub]

private theorem connected_gap {f : ℝ→ℝ} {a b r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) (hs : r < 1/2)
    (hf : ContinuousOn f (Icc a b)) (h : ∀ z∈Icc a b, ∃ x∈Icc (-r) r,
      (x:UnitAddCircle)=(f z:UnitAddCircle)) : f b-f a ≤ 2*r := by
  by_contra! hfar
  obtain ⟨x,hx,he⟩ := h a ⟨le_rfl,hab⟩
  have hcut : r < min (1-r) (x+(f b-f a)) := lt_min (by linarith only [hs]) (by linarith only [hfar,hx.1])
  obtain ⟨y,hy,hend⟩ := exists_between hcut
  have hh := hend.trans_le (min_le_right ..)
  obtain ⟨z,hz,hval⟩ := intermediate_value_Icc hab hf
    (show f a+(y-x)∈Icc (f a) (f b) from ⟨by linarith only [hy,hx.2],by linarith only [hh]⟩)
  obtain ⟨v,ht,hv⟩ := h z hz
  have heq : (v:UnitAddCircle)=(y:UnitAddCircle) := by
    rw [hv,hval,AddCircle.coe_add,AddCircle.coe_sub,←he]
    abel
  have hv' : v∈Ico (-r) (-r+1) := ⟨ht.1,by linarith only [ht.2,hs]⟩
  have hy' : y∈Ico (-r) (-r+1) := ⟨by linarith only [hr,hy],by linarith only [hend.trans_le (min_le_left ..)]⟩
  exact (ht.2.trans_lt hy).ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico hv' hy').mp heq)

/-- Continuously retiming a scalar return preserves every unwrapped pair
gap, measured in turns, to twice the arc tolerance. -/
theorem retimed_pair_rigidity (p : ℝ→I→ℝ) {a b r : ℝ} (hab : a ≤ b)
    (hr : 0 ≤ r) (hs : r < 1/2) (hc : ∀ i, ContinuousOn (fun z => p z i) (Icc a b))
    (hv : ∀ z∈Icc a b, (fun i => (p z i:UnitAddCircle))∈enclosingUnitArc r) (i j : I) :
    |(p b i-p b j)-(p a i-p a j)| ≤ 2*r := by
  have H (k l : I) : (p b k-p b l)-(p a k-p a l) ≤ 2*r :=
    connected_gap hab hr hs ((hc k).sub (hc l)) (fun z hz => pair_representative hr (hv z hz) k l)
  exact abs_le.mpr ⟨by linarith only [H j i],H i j⟩

/-- For traceless generators a bound on the motion of every pair gap
also bounds the motion of each individual energy times the chosen date. -/
theorem retimed_level_rigidity [Nonempty I] (p : ℝ→I→ℝ) {a b r : ℝ} (hab : a ≤ b)
    (hr : 0 ≤ r) (hs : r < 1/2) (hc : ∀ i, ContinuousOn (fun z => p z i) (Icc a b))
    (hv : ∀ z∈Icc a b, (fun i => (p z i:UnitAddCircle))∈enclosingUnitArc r)
    (ha : (∑ i,p a i)=0) (hb : (∑ i,p b i)=0) (i : I) :
    |p b i-p a i| ≤ 2*r := by
  let d (j : I) := p b j-p a j
  have hd : ∑ j,d j=0 := by simp only [d,Finset.sum_sub_distrib,hb,ha,sub_zero]
  have hh (j : I) : |d i-d j| ≤ 2*r := by
    convert retimed_pair_rigidity p hab hr hs hc hv i j using 1 <;> dsimp [d] <;> ring_nf
  have hid : ∑ j,d i-d j=(Fintype.card I:ℝ)*d i := by
    rw [Finset.sum_sub_distrib,hd,sub_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have ht := (Finset.abs_sum_le_sum_abs (fun j => d i-d j) Finset.univ).trans
    (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hh j))
  rw [hid,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
  exact (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr Fintype.card_pos : 0 < (Fintype.card I:ℝ))).mp ht

#print axioms retimed_level_rigidity
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.CouplingSensitivity
