import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ComponentCounts
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.IntervalPacking

/-! # Occupation bound for the number of long connected visits -/
open Set MeasureTheory
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
noncomputable section

/-- True entries whose connected visit continues for at least h. -/
def longVisits (E : Set ℝ) (h : ℝ) (F : Finset ℝ) : Finset ℝ := by
  classical
  exact F.filter fun u => Icc u (u+h) ⊆ E

/-- Each long visit contributes h distinct units of occupied time.
Extending the observation interval past its right endpoint costs at most h. -/
theorem duration_charge (E : Set ℝ) (a T h : ℝ) (hh : 0≤h) (F : Finset ℝ)
    (hF : ∀ u∈F, u∈Icc a T ∧ Entry E u) :
    ((longVisits E h F).card:ℝ)*h ≤ volume.real (E∩Icc a T)+h := by
  classical
  let L := longVisits E h F
  let J (i : L) := Ico i.val (i.val+h)
  have hm (i : L) : i.val∈F ∧ Icc i.val (i.val+h) ⊆ E := Finset.mem_filter.mp i.property
  have hsep (i j : L) (hlt : i.val<j.val) : i.val+h≤j.val := by
    by_contra! h
    obtain ⟨d,hd,he⟩ := (hF _ (hm j).1).2.2
    obtain ⟨z,hz₁,hz₂⟩ := exists_between (max_lt hlt (sub_lt_self j.val hd))
    exact he z ⟨(le_max_right ..).trans_lt hz₁,hz₂⟩
      ((hm i).2 ⟨((le_max_left ..).trans_lt hz₁).le,(hz₂.trans h).le⟩)
  have hd : Pairwise fun i j : L => Disjoint (J i) (J j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne (Subtype.coe_injective.ne hij) with h|h
    · exact hx.2.not_ge ((hsep i j h).trans hy.1)
    · exact hy.2.not_ge ((hsep j i h).trans hx.1)
  let A := E∩Icc a T
  let B := Icc T (T+h)
  have hsub : (⋃ i : L, J i) ⊆ A∪B := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have ht := (hF _ (hm i).1).1
    by_cases hxT : x≤T
    · exact Or.inl ⟨(hm i).2 ⟨hi.1,hi.2.le⟩,ht.1.trans hi.1,hxT⟩
    · exact Or.inr ⟨(lt_of_not_ge hxT).le,hi.2.le.trans (add_le_add_left ht.2 h)⟩
  have hA : volume A≠⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hB : volume B≠⊤ := measure_Icc_lt_top.ne
  have hu : volume (A∪B)≠⊤ := ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr
    ⟨hA.lt_top,hB.lt_top⟩)).ne
  have hb := (measureReal_mono (μ:=volume) hsub hu).trans (measureReal_union_le A B)
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_Ico) (fun _ => measure_Ico_lt_top.ne)] at hb
  simpa only [J,B,Real.volume_real_Ico,Real.volume_real_Icc,add_sub_cancel_left,max_eq_left hh,
    Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] using hb

/-- An entry reaching a deeper level either reaches it within h or belongs
to a component charged by the duration bound. -/
theorem reached_le_early_add_long (E F G : Set ℝ) (h : ℝ) (A : Finset ℝ)
    (hfit : ∀ u∈A, ∀ v∈F, u≤v → v-u≤h → u∈G) :
    (reached E F A).card ≤ (A.filter fun u => u∈G).card+(longVisits E h A).card := by
  classical
  apply (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro u hu
  obtain ⟨hA,v,huv,hv,hseg⟩ := Finset.mem_filter.mp hu
  by_cases he : v-u≤h
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hA,hfit u hA v hv huv he⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA,fun _ hz => hseg
      ⟨hz.1,hz.2.trans (by linarith only [lt_of_not_ge he])⟩⟩)

#print axioms duration_charge
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
