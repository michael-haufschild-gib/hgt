import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitWindows

/-! # Covering a finite record of forward hitting windows -/
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- Each hit has an integer offset placing it in a translated unit window.
Only the finite list of enlarged occupations on this record enters the bound. -/
theorem finite_window_hit_fraction {n j k : ℕ} {H : selfAdjoint (Register n)} {ε η p W a T : ℝ}
    (hW : 0≤W) (hunit : windowHits H j ε 1 ⊆ visitSet H k η) (hT : a<T)
    (ht : ∀ i : Fin (⌊W⌋₊+1), visitFraction H k η (a+(i.val:ℝ)) (T+(i.val:ℝ)) < p) :
    volume.real (windowHits H j ε W ∩ Icc a T)/(T-a) ≤ (W+1)*p := by
  classical
  let M := ⌊W⌋₊+1
  let shift (i : Fin M) := (i.val:ℝ)
  have hclosed : IsClosed (visitSet H k η) := by
    have he : visitSet H k η = {v | orbitCircuitDistance H k v ≤ η} := Set.ext fun _ =>
      hasProjectiveCircuitApproximation_iff_infDist _ _ _
    rw [he]
    exact isClosed_le (orbitCircuitDistance_lipschitz H k).continuous continuous_const
  let A (i : Fin M) := visitSet H k η ∩ Icc (a+shift i) (T+shift i)
  let B (i : Fin M) := (fun u : ℝ => u+shift i) ⁻¹' (A i)
  have hlen (i : Fin M) : volume.real (B i) = volume.real (A i) :=
    congrArg ENNReal.toReal ((measurePreserving_add_right volume (shift i)).measure_preimage
      (hclosed.measurableSet.inter measurableSet_Icc).nullMeasurableSet)
  have hsub : windowHits H j ε W ∩ Icc a T ⊆ ⋃ i : Fin M, B i := by
    rintro u ⟨⟨v,hv,hcheap⟩,hu⟩
    let i : Fin M := ⟨⌊v-u⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (by linarith only [hv.2]))⟩
    have hlow : shift i ≤ v-u := Nat.floor_le (sub_nonneg.mpr hv.1)
    have hupp : v-u < shift i+1 := Nat.lt_floor_add_one _
    exact mem_iUnion.mpr ⟨i,hunit ⟨v,⟨by linarith only [hlow],by linarith only [hupp]⟩,hcheap⟩,
      add_le_add hu.1 le_rfl,add_le_add hu.2 le_rfl⟩
  have hI : (⋃ i : Fin M, B i) ⊆ Icc a T := by
    intro u hu
    obtain ⟨i,hi⟩ := mem_iUnion.mp hu
    have hh : u+shift i ∈ Icc (a+shift i) (T+shift i) := hi.2
    exact ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have htot := (measureReal_mono (μ := volume) hsub (measure_ne_top_of_subset hI measure_Icc_lt_top.ne)).trans
    (measureReal_iUnion_fintype_le B)
  have heach (i : Fin M) : volume.real (B i)/(T-a) ≤ p := by
    have h := (ht i).le
    change volume.real (A i)/((T+shift i)-(a+shift i)) ≤ p at h
    rwa [add_sub_add_right_eq_sub,←hlen i] at h
  have hp : 0 ≤ p := (div_nonneg measureReal_nonneg (sub_nonneg.mpr hT.le)).trans (heach ⟨0,Nat.zero_lt_succ _⟩)
  calc
    _ ≤ (∑ i : Fin M, volume.real (B i))/(T-a) := div_le_div_of_nonneg_right htot (sub_nonneg.mpr hT.le)
    _ ≤ (M:ℝ)*p := by
      rw [Finset.sum_div]
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [M]; push_cast; linarith only [Nat.floor_le hW]) hp

#print axioms finite_window_hit_fraction
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
