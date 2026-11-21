import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.EntryCount
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ShiftPacking

/-! # Disjoint affordable time intervals after continuous entries -/
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section
open EmptyVisitFlux SharpOccupation

/-- Distinct actual entries are separated by one uncovered part of a
turn, including when some endpoint phases coincide. -/
theorem entries_separated {I : Type*} [Fintype I] [Nonempty I] (w : I → ℝ)
    {r t u : ℝ} (hr : 0 ≤ r) (hs : r<1/2) (ht : t < u)
    (hf : visitEntry w r t) (hg : visitEntry w r u) :
    1-2*r ≤ (u-t)*(Finset.univ.sup' Finset.univ_nonempty w-Finset.univ.inf' Finset.univ_nonempty w) := by
  obtain ⟨i,j,hj⟩ := (entry_iff_closed_face w hr hs).mp hg
  exact (gap_before_contact w hr ht hf.1 hj.1 hj.2.1).trans
    (mul_le_mul_of_nonneg_left (sub_le_sub (Finset.le_sup' w (Finset.mem_univ i))
      (Finset.inf'_le w (Finset.mem_univ j))) (sub_nonneg.mpr ht.le))

/-- A physical empty visit followed by an affordable interval of lags
contributes the entire interval to the larger circuit budget. -/
theorem interval_packing {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ)
    {T h r e : ℝ} (F : Finset ℝ) (hh : 0≤h)
    (hf : ∀ t ∈ F, t∈Icc 0 T ∧ t∈visitSet H 0 r)
    (hgap : ∀ t ∈ F, ∀ u ∈ F, t<u → t+h ≤ u)
    (hc : ∀ v ∈ Icc 0 h, v∈visitSet H s e) :
    (F.card:ℝ)*h ≤ volume.real (visitSet H s (r+e) ∩ Icc 0 (T+h)) := by
  classical
  let A (i : F) := Ico (i:ℝ) ((i:ℝ)+h)
  have hd : Pairwise fun i j : F => Disjoint (A i) (A j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases lt_or_gt_of_ne (Subtype.coe_injective.ne hij) with ht | ht
    · exact (lt_of_lt_of_le hv.2 ((hgap i i.property j j.property ht).trans hw.1)).false
    · exact (lt_of_lt_of_le hw.2 ((hgap j j.property i i.property ht).trans hv.1)).false
  have hsub : (⋃ i : F, A i) ⊆ visitSet H s (r+e) ∩ Icc 0 (T+h) := by
    intro t ht
    obtain ⟨i,hi⟩ := mem_iUnion.mp ht
    have hx := hf i i.property
    have hi' : (i:ℝ) ≤ t ∧ t<(i:ℝ)+h := hi
    have hy := hc (t-i) ⟨sub_nonneg.mpr hi'.1,by linarith only [hi'.2]⟩
    have ha := affordable_add_time H hx.2 hy
    rw [show (i:ℝ)+(t-i)=t by ring,zero_add] at ha
    exact ⟨ha,hx.1.1.trans hi'.1,by linarith only [hi'.2,hx.1.2]⟩
  have hle := measureReal_mono (μ := volume) hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_Ico) (fun _ => measure_Ico_lt_top.ne)] at hle
  simpa only [A,Real.volume_real_Ico,add_sub_cancel_left,Finset.sum_const,Finset.card_univ,
    Fintype.card_coe,nsmul_eq_mul,max_eq_left hh] using hle

#print axioms interval_packing
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
