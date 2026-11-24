import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! # Cardinality of separated samples in a closed time interval -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.TimePacking

/-- Attaching a half-open interval of length δ to each sampled time
gives disjoint intervals inside a window of length T+δ. -/
theorem separated_interval_count {ι : Type*} [Fintype ι] (t : ι → ℝ) (a T δ : ℝ)
    (hT : 0≤T) (hδ : 0<δ) (ht : ∀ i, t i∈Icc a (a+T))
    (hsep : ∀ i j, i≠j → δ≤|t i-t j|) :
    (Fintype.card ι:ℝ)*δ≤T+δ := by
  classical
  let A (i : ι) := Ico (t i) (t i+δ)
  have hd : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro v ⟨hi,hi'⟩ ⟨hj,hj'⟩
    exact (hsep i j hij).not_gt (abs_lt.mpr
      ⟨by linarith only [hj,hi'],by linarith only [hi,hj']⟩)
  have hsub : (⋃ i, A i) ⊆ Icc a (a+T+δ) := by
    intro v hv
    obtain ⟨i,hi⟩ := mem_iUnion.mp hv
    exact ⟨(ht i).1.trans hi.1,hi.2.le.trans (add_le_add (ht i).2 (le_refl δ))⟩
  have h := measureReal_mono (μ:=volume) hsub measure_Icc_lt_top.ne
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_Ico) (fun _ => measure_Ico_lt_top.ne),
    Real.volume_real_Icc_of_le (by linarith only [hT,hδ])] at h
  simpa only [A,Real.volume_real_Ico,add_sub_cancel_left,max_eq_left hδ.le,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,add_assoc,add_sub_cancel_left] using h

#print axioms separated_interval_count
end GaloisForLFunctions.HTGeometry.TimePacking
