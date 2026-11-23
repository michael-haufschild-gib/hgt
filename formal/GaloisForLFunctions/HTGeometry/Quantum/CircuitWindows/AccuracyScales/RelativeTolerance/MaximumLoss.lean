import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.RelativeTolerance.WeightedHeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.CriticalHeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc

/-! # Exact logarithmic loss in the physical orbit maximum -/
open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.RelativeTolerance
open MaximumIntervals DiagonalSynthesis (Register)
noncomputable section

/-- A budget falls short of the orbit maximum precisely below its critical
height. The strict inequality accounts for attainable fits at the boundary. -/
theorem below_criticalHeight_iff {N m : ℕ} (H : selfAdjoint (Register N)) {e : ℝ}
    (hm : IsRecurrentOrbitCircuitMaximumAt H e m) (j : ℕ) : e < criticalHeight H j ↔ j<m := by
  have hb : BddAbove (range (orbitCircuitDistance H j)) := by
    refine ⟨2,?_⟩
    rintro _ ⟨t,rfl⟩
    have hf := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val t) 0 (2:ℝ)).mpr
      (orbitCircuitDistance_zeroGate_lt_two H t).le
    obtain ⟨z,hz,C,hC,he⟩ := hf
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC.trans (Nat.zero_le _),he⟩
  constructor
  · intro h
    by_contra! hj
    apply h.not_ge (csSup_le (range_nonempty _) ?_)
    rintro _ ⟨t,rfl⟩
    obtain ⟨z,hz,C,hC,he⟩ := hm.1 t
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC.trans hj,he⟩
  · intro hj
    obtain ⟨t,ht⟩ := required_at_some_date hm
    have hh : e < orbitCircuitDistance H j t := lt_of_not_ge fun h =>
      hj.not_ge (ht j ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr h))
    exact hh.trans_le (le_csSup hb (mem_range_self t))

private theorem truncated_weight {m B : ℕ} (hm : m≤B) :
    (∑ j ∈ Finset.range B, if j<m then gateWeight j else 0) = log ((m:ℝ)+1) := by
  rw [←Finset.sum_filter]
  have hf : (Finset.range B).filter (fun j => j<m)=Finset.range m := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hf,sum_gateWeight]

/-- The full relative loss, including simultaneous jumps of arbitrarily
many gate counts, is the sum of the weights of the crossed heights. -/
theorem log_maximum_drop {N m n B : ℕ} (H : selfAdjoint (Register N)) {e δ : ℝ} (hδ : 0≤δ)
    (hm : IsRecurrentOrbitCircuitMaximumAt H e m) (hn : IsRecurrentOrbitCircuitMaximumAt H (e+δ) n)
    (hB : m≤B) :
    thresholdLoss B (criticalHeight H) δ e = log ((m:ℝ)+1)-log ((n:ℝ)+1) := by
  have hnB : n≤B := by
    obtain ⟨t,ht⟩ := required_at_some_date hn
    obtain ⟨z,hz,C,hC,he⟩ := hm.1 t
    exact (ht m ⟨z,hz,C,hC,he.trans (le_add_of_nonneg_right hδ)⟩).trans hB
  rw [←truncated_weight hB,←truncated_weight hnB,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hf := below_criticalHeight_iff H hm j
  have hc := below_criticalHeight_iff H hn j
  by_cases h : e < criticalHeight H j
  · rw [if_pos (hf.mp h)]
    by_cases h' : e+δ < criticalHeight H j
    · rw [if_pos (hc.mp h'),sub_self,indicator_of_notMem]
      intro he
      exact h'.not_ge (by linarith only [he.1])
    · rw [if_neg (fun hh => h' (hc.mpr hh)),sub_zero,indicator_of_mem]
      exact ⟨by linarith only [le_of_not_gt h'],h⟩
  · have h' : ¬ e+δ < criticalHeight H j := fun hh => h ((le_add_of_nonneg_right hδ).trans_lt hh)
    rw [if_neg (fun hh => h (hf.mpr hh)),if_neg (fun hh => h' (hc.mpr hh)),sub_zero,indicator_of_notMem]
    exact fun he => h he.2

#print axioms log_maximum_drop
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.RelativeTolerance
