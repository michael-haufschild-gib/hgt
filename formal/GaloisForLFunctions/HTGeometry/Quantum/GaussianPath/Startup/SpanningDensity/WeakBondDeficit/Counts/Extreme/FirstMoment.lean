import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.MovingBoxes

/-! # One-hit probability and monotonicity of weak-bond samples -/
open Finset Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
open private row_law from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.BoxTails
noncomputable section

/-- Enlarging a prefix of a fixed progression retains every weak row. -/
theorem boxCount_mono_length (ω : PathPauliDisorder) (s d : ℕ) {m M : ℕ} (hm : m≤M) (h : ℝ) :
    boxCount ω s d m h≤boxCount ω s d M h := by
  classical
  rw [boxCount_as_filter,boxCount_as_filter]
  apply card_le_card_of_injOn (Fin.castLE hm)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  · exact (Fin.castLE_injective hm).injOn

/-- Even one bond in a very small box costs at most the one-row mass
times the number of sampled bonds. -/
theorem any_weak_row_bound (s d m : ℕ) (hd : 0<d) (h : ℝ) :
    pathPauliDisorderLaw.real {ω | 0<boxCount ω s d m h} ≤ m*bondLaw.real (weakBond h) := by
  classical
  let B := weakBond h
  let A (i : Fin m) := {ω | bondRow9 ω (s+d*i.val)∈B}
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hmass (i : Fin m) : pathPauliDisorderLaw.real (A i)=bondLaw.real B :=
    ((measurePreserving_eval_infinitePi (fun _ : Fin m => bondLaw) i).comp
      (row_law s d m hd)).measureReal_preimage (weakBond_measurable h).nullMeasurableSet
  have hs : {ω | 0<boxCount ω s d m h}⊆⋃ i : Fin m, A i := by
    intro ω hw
    change 0<boxCount ω s d m h at hw
    rw [boxCount_as_filter] at hw
    obtain ⟨i,hi⟩ := card_pos.mp hw
    exact mem_iUnion.mpr ⟨i,(mem_filter.mp hi).2⟩
  apply ((measureReal_mono (μ:=pathPauliDisorderLaw) hs).trans (measureReal_iUnion_fintype_le _)).trans_eq
  simp only [hmass,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

#print axioms any_weak_row_bound
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
