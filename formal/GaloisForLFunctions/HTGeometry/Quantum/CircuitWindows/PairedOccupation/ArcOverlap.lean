import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AnchorPairGeometry

/-! # Haar overlap of two arcs at every separation -/

open Set MeasureTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PairedOccupation
noncomputable section

private theorem canonical {y u : ℝ} (hy : y∈Ico (0:ℝ) 1) (hu : u∈Ico (0:ℝ) 1) :
    ((y:UnitAddCircle)=(u:UnitAddCircle)) ↔ y=u :=
  AddCircle.coe_eq_coe_iff_of_mem_Ico (p:=(1:ℝ)) (a:=0)
    (by simpa only [zero_add] using hy) (by simpa only [zero_add] using hu)

private theorem arc_test {r y : ℝ} (hr : r<1) (hy : y∈Ico (0:ℝ) 1) :
    (y:UnitAddCircle)∈forwardUnitArc r ↔ y≤r := by
  constructor
  · rintro ⟨u,hu,he⟩
    exact (canonical ⟨hu.1,hu.2.trans_lt hr⟩ hy).mp he ▸ hu.2
  · exact fun h => ⟨y,⟨hy.1,h⟩,rfl⟩

private theorem two_intervals {t y r : ℝ} (hr : r∈Ico (0:ℝ) 1) (ht : t∈Ico (0:ℝ) 1)
    (hy : y∈Icc (0:ℝ) r) : ((y:UnitAddCircle)-(t:UnitAddCircle))∈forwardUnitArc r ↔
      y∈Icc t r ∪ Icc 0 (r+t-1) := by
  rw [←AddCircle.coe_sub]
  by_cases h : t≤y
  · rw [arc_test hr.2 ⟨sub_nonneg.mpr h,by linarith only [hy.2,hr.2,ht.1]⟩]
    exact ⟨fun _ => Or.inl ⟨h,hy.2⟩,fun _ => (sub_le_self _ ht.1).trans hy.2⟩
  · have hd : ((y-t:ℝ):UnitAddCircle)=((y-t+1:ℝ):UnitAddCircle) := by
      rw [AddCircle.coe_add,AddCircle.coe_period,add_zero]
    rw [hd,arc_test hr.2 ⟨by linarith only [hy.1,ht.2],by linarith only [lt_of_not_ge h]⟩]
    constructor
    · exact fun he => Or.inr ⟨hy.1,by linarith only [he]⟩
    · rintro (he|he)
      · exact (h he.1).elim
      · linarith only [he.2]

/-- For two arcs of width r<1, their intersection consists of the
unwrapped and wrapped intervals, each counted by its positive length. -/
theorem volume_overlap {r t : ℝ} (hr : r∈Ico (0:ℝ) 1) (ht : t∈Ico (0:ℝ) 1) :
    volume (commonForwardUnitArc r (t:UnitAddCircle))=
      ENNReal.ofReal (r-t)+ENNReal.ofReal (r+t-1) := by
  let a := (r-1)/2
  have sub : Icc 0 r ⊆ Ioc a (a+1) := fun y hy => by
    dsimp only [a]; exact ⟨by linarith only [hr.2,hy.1],by linarith only [hr.2,hy.2]⟩
  have hmeas := (isClosed_forwardUnitArc r).measurableSet
  have hT : MeasurableSet (commonForwardUnitArc r (t:UnitAddCircle)) :=
    hmeas.inter (hmeas.preimage (continuous_id.sub continuous_const).measurable)
  rw [AddCircle.add_projection_respects_measure 1 a hT]
  have heq : (((↑) : ℝ → UnitAddCircle) ⁻¹' commonForwardUnitArc r (t:UnitAddCircle)) ∩ Ioc a (a+1)
      = Icc t r ∪ Icc 0 (r+t-1) := by
    ext y
    constructor
    · rintro ⟨⟨⟨u,hu,he⟩,hp⟩,hy⟩
      obtain rfl : u=y := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (sub hu) hy).mp he
      exact (two_intervals hr ht hu).mp hp
    · intro h
      have hy : y∈Icc (0:ℝ) r := by
        rcases h with h|h
        · exact ⟨ht.1.trans h.1,h.2⟩
        · exact ⟨h.1,by linarith only [h.2,ht.2]⟩
      exact ⟨⟨⟨y,hy,rfl⟩,(two_intervals hr ht hy).mpr h⟩,sub hy⟩
  have hd : Disjoint (Icc t r) (Icc 0 (r+t-1)) := disjoint_left.mpr fun _ h₁ h₂ => by
    linarith only [h₁.1,h₂.2,hr.2]
  rw [heq,measure_union hd measurableSet_Icc,Real.volume_Icc,Real.volume_Icc,sub_zero]

#print axioms volume_overlap
end
end GaloisForLFunctions.HTGeometry.PairedOccupation
