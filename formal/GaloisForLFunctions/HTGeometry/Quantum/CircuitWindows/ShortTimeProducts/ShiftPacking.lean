import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # Disjoint translates of the empty-circuit return set inside a larger budget -/
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ShortTimeProducts
noncomputable section
open SharpOccupation

/-- Affordable lags separated at twice the empty-circuit radius generate
disjoint copies of every earlier empty-circuit visit. -/
theorem translated_returns {n : ℕ} {I : Type*} [Fintype I]
    (H : selfAdjoint (Register n)) (s : ℕ) (r e B : ℝ) (u : I → ℝ)
    (hu : ∀ i, u i ∈ Icc 0 B) (hc : ∀ i, u i ∈ visitSet H s e)
    (hsep : ∀ i j, i ≠ j → 2*r < orbitCircuitDistance H 0 (u j-u i))
    (a T : ℝ) :
    (Fintype.card I:ℝ)*volume.real (visitSet H 0 r ∩ Icc a T) ≤
      volume.real (visitSet H s (r+e) ∩ Icc a (T+B)) := by
  let F := visitSet H 0 r ∩ Icc a T
  let G (i : I) := (fun t : ℝ => t+(-u i)) ⁻¹' F
  have hclosed : IsClosed (visitSet H 0 r) := by
    change IsClosed {t | HasProjectiveCircuitApproximation n r 0 (unitaryEvolution H.val t)}
    simp only [hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const
  have hm : MeasurableSet F := hclosed.measurableSet.inter measurableSet_Icc
  have hG (i : I) : volume (G i)=volume F := (measurePreserving_add_right volume (-u i)).measure_preimage hm.nullMeasurableSet
  have hreal (i : I) : volume.real (G i)=volume.real F := congrArg ENNReal.toReal (hG i)
  have hfin : volume F ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hd : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t hi hj
    have hx : HasProjectiveCircuitApproximation n r 0 (unitaryEvolution H.val (t+-u i)) := hi.1
    have hy : HasProjectiveCircuitApproximation n r 0 (unitaryEvolution H.val (t+-u j)) := hj.1
    have hh := affordable_add_time H hx (hy.neg_time H)
    rw [show t+-u i+ -(t+-u j)=u j-u i by ring,←two_mul] at hh
    exact (hsep i j hij).not_ge ((hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mp hh)
  have hsub : (⋃ i, G i) ⊆ visitSet H s (r+e) ∩ Icc a (T+B) := by
    intro t ht
    obtain ⟨i,hi⟩ := mem_iUnion.mp ht
    have hx : HasProjectiveCircuitApproximation n r 0 (unitaryEvolution H.val (t+-u i)) := hi.1
    have hh := affordable_add_time H hx (hc i)
    rw [show t+-u i+u i=t by ring,zero_add] at hh
    have ht' : t+-u i ∈ Icc a T := hi.2
    exact ⟨hh,by linarith only [ht'.1,(hu i).1],by linarith only [ht'.2,(hu i).2]⟩
  have h := measureReal_mono (μ := volume) hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  rw [measureReal_iUnion_fintype hd (fun i => hm.preimage (measurable_id.add_const _))
    (fun i => (hG i).trans_ne hfin)] at h
  simpa only [hreal,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,F] using h

#print axioms translated_returns
end
end GaloisForLFunctions.HTGeometry.ShortTimeProducts
