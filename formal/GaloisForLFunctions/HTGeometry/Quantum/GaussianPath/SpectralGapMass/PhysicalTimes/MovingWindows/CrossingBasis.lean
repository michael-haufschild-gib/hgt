import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.MovingWindows.InverseRoot
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.BasisCost
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.FirstVisit

/-! # Exponential basis-change cost near the first physical crossing -/
open Matrix Filter MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Every observation origin is within K/√N of a date with spectral
gate count exactly three. The interval may depend on the whole orbit. -/
theorem gaussian_three_date_every_origin :
    ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ v : ℝ, ∃ t ∈ Icc v (v+K/sqrt (n+2:ℕ)), exactThreeAt (pathPauliDisorderShell ω n) t := by
  obtain ⟨c,hc,h⟩ := gaussian_inverse_root_exception_length 1
  obtain ⟨m,hm⟩ := exists_nat_gt ((2*c)^2)
  refine ⟨2*c,by positivity,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw,eventually_ge_atTop m] with n hn hlarge
  let N := ((n+2:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  let h := 2*c/sqrt N
  have hh : 0 < h := by dsimp only [h]; positivity
  have hs : h ≤ 1 := by
    apply (div_le_one (sqrt_pos.mpr hN)).mpr
    apply (le_sqrt (by positivity) hN.le).mpr
    exact hm.le.trans (Nat.cast_le.mpr (by omega : m ≤ n+2))
  intro v
  by_contra hn'
  let E := {t | ¬exactThreeAt (pathPauliDisorderShell ω n) t} ∩ Icc v (v+1)
  have hsub : Icc v (v+h) ⊆ E := by
    intro t ht
    exact ⟨fun hg => hn' ⟨t,ht,hg⟩,ht.1,ht.2.trans (add_le_add_right hs _)⟩
  have hl := (measureReal_mono (μ:=volume) hsub (measure_ne_top_of_subset
    (show E ⊆ Icc v (v+1) from inter_subset_right) measure_Icc_lt_top.ne)).trans (hn v)
  rw [Real.volume_real_Icc_of_le (le_add_of_nonneg_right hh.le),add_sub_cancel_left] at hl
  exact (div_lt_div_of_pos_right (by linarith only [hc] : c < 2*c) (sqrt_pos.mpr hN)).not_ge hl

/-- At the first robust crossing, the first three-gate date in a free
basis lies within K/√N. Every such fit throughout the exponential travel
window needs an exponentially costly basis change even at error 1/1000. -/
theorem gaussian_first_crossing_spectral_wait :
    ∃ K > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ : ℝ, LocalPatches.localCrossingWidth N < σ ∧ orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        (SpectralApproximation.firstVisit H σ 3 (1/10) ∈ Icc σ (σ+K/sqrt N)) ∧
        (∃ t∈Icc σ (σ+K/sqrt N), exactThreeAt x t) ∧
        ∀ t : ℝ, |σ-t| ≤ LocalPatches.localCrossingWidth N →
          ∀ (W : unitaryGroup (Fin N → Bool) ℂ) (b j : ℕ),
            HasProjectiveCircuitApproximation N (1/1000) b W.val →
            HasProjectiveCircuitApproximation N (1/10) j
              (W.val*unitaryEvolution H.val t*star W.val) → P/2 < 2*b+j := by
  obtain ⟨K,hK,h⟩ := gaussian_three_date_every_origin
  refine ⟨K,hK,?_⟩
  filter_upwards [h,LocalPatches.gaussian_first_crossing_local_width,LocalPatches.gaussian_local_travel_at_error]
    with ω hw hf ht
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hw,hf,ht] with k hn hfirst htravel
  intro N x H P
  obtain ⟨σ,hσ,he,hprior,_⟩ := hfirst
  obtain ⟨t,ht,hthree⟩ := hn σ
  have hleast := SpectralApproximation.firstVisit_isLeast H σ 3 (by norm_num : (0:ℝ) < 1/10)
  refine ⟨σ,hσ,he,hprior,⟨hleast.1.1,(hleast.2 ⟨ht.1,hthree.1⟩).trans ht.2⟩,⟨t,ht,hthree⟩,?_⟩
  intro v hv W b j hb hj
  let U : unitaryGroup (Fin N → Bool) ℂ := ⟨_,unitaryEvolution_mem_unitary H.property v⟩
  have hc := SpectralApproximation.cost_in_physical_basis U W hb hj
  exact lt_of_not_ge (fun hs => (htravel (1/10+2*(1/1000)) (by norm_num) σ v he.ge _ hs hc).not_ge hv)

#print axioms gaussian_three_date_every_origin
#print axioms gaussian_first_crossing_spectral_wait
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
