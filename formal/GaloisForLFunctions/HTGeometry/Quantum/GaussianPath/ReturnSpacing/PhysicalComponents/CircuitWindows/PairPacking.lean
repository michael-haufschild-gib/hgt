import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows
import GaloisForLFunctions.HTGeometry.SeparatedPointCount

/-! # The number of true scalar entries in any bounded window -/
open Real Set
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
open EmptyVisitFlux
noncomputable section

private theorem pair_packing {I : Type*} (E : I → ℝ) (i j : I) (r T a b : ℝ)
    (hab : a≤b) (A : Set UnitAddCircle) :
    (((markedDates E i j r A T).filter fun v => v∈Icc a b).card:ℝ) ≤
      (b-a)*(max 0 (E i-E j)/(2*π))+1 := by
  classical
  by_cases hg : E j<E i
  · let τ := 2*π/(E i-E j)
    have hτ : 0<τ := div_pos (by positivity) (sub_pos.mpr hg)
    have htick {t : ℝ} (ht : t∈markedDates E i j r A T) : ∃ k, pairDate E i j r k=t := by
      rw [markedDates,if_pos hg] at ht
      obtain ⟨k,_,he⟩ := Finset.mem_image.mp ht
      exact ⟨k,he⟩
    let S := (markedDates E i j r A T).filter fun v => v∈Icc a b
    have hsep (u : ℝ) (hu : u∈S) (v : ℝ) (hv : v∈S) (hne : u≠v) : τ≤|u-v| := by
      obtain ⟨k,rfl⟩ := htick (Finset.mem_filter.mp hu).1
      obtain ⟨l,rfl⟩ := htick (Finset.mem_filter.mp hv).1
      have hkl : k≠l := fun h => hne (congrArg _ h)
      have hgap : (1:ℝ)≤|(k:ℝ)-(l:ℝ)| := by
        rcases lt_or_gt_of_ne hkl with h|h
        · rw [abs_of_neg (sub_neg.mpr (Nat.cast_lt.mpr h))]
          have hh : (k:ℝ)+1≤l := by exact_mod_cast Nat.succ_le_of_lt h
          linarith only [hh]
        · rw [abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr h))]
          have hh : (l:ℝ)+1≤k := by exact_mod_cast Nat.succ_le_of_lt h
          linarith only [hh]
      change τ≤|(1-r+(k:ℝ))*τ-(1-r+(l:ℝ))*τ|
      rw [←sub_mul,add_sub_add_left_eq_sub,abs_mul,abs_of_pos hτ]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap hτ.le
    have h := card_le_of_separated_of_subset_Icc hτ hab S hsep (fun v hv => (Finset.mem_filter.mp hv).2)
    apply h.trans_eq
    rw [max_eq_right (sub_nonneg.mpr hg.le)]
    dsimp only [τ]
    rw [div_div_eq_mul_div,mul_div_assoc]
  · rw [markedDates,if_neg hg,max_eq_left (sub_nonpos.mpr (le_of_not_gt hg))]
    simp

/-- Each oriented pair contributes its winding rate times window length,
plus at most one boundary tick. This holds for arbitrary tolerance and
arbitrary observation origin, even when pair clocks coincide. -/
theorem entry_window_count {I : Type*} [Fintype I] (E : I→ℝ) (r σ T a b : ℝ) (hab : a≤b) :
    (((entriesAfter E r σ T).filter fun v => v∈Icc a b).card:ℝ) ≤
      (Fintype.card I:ℝ)^2+(b-a)*pairTurnRate E := by
  classical
  let S (p : I×I) := (markedDates E p.1 p.2 r (forwardUnitArc r) T).filter fun v => v∈Icc a b
  have hsub : ((entriesAfter E r σ T).filter fun v => v∈Icc a b) ⊆ Finset.univ.biUnion S := by
    intro v hv
    obtain ⟨he,hi⟩ := Finset.mem_filter.mp hv
    obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp he).1
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hv,hi⟩⟩
  calc
    _ ≤ ∑ p, ((S p).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ p : I×I, ((b-a)*(max 0 (E p.1-E p.2)/(2*π))+1) :=
      Finset.sum_le_sum fun p _ => pair_packing E p.1 p.2 r T a b hab _
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
        nsmul_eq_mul,mul_one,Fintype.card_prod,Nat.cast_mul,pairTurnRate,pow_two,add_comm]

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
