import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Physical gate budgets on both sides of the first robust crossing -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.CrossingProfile
open PrescribedTimes ShortWindows
noncomputable section

private theorem budget_bracket {N P j : ℕ} (H : selfAdjoint (Register N)) {σ t : ℝ}
    (hc : orbitCircuitDistance H P σ = 9/80)
    (hi : HasProjectiveCircuitApproximation N (1/100:ℝ) j (unitaryEvolution H.val t)) :
    orbitCircuitDistance H (P+j) (σ+t) ≤ 1/8 ∧ ∀ s, s+j ≤ P → 1/10 < orbitCircuitDistance H s (σ+t) := by
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val σ) P (9/80:ℝ)).mpr hc.le
  have hplus := affordable_add_time H (x:=σ) (y:=t) hfit hi
  refine ⟨((hasProjectiveCircuitApproximation_iff_infDist ..).mp hplus).trans (by norm_num),?_⟩
  intro s hs
  apply lt_of_not_ge
  intro hh
  have hfit' := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val (σ+t)) s (1/10:ℝ)).mpr hh
  have hback := affordable_add_time H (x:=σ+t) (y:= -t) hfit' (hi.neg_time H)
  rw [show σ+t+-t=σ by ring] at hback
  obtain ⟨z,hz,C,hC,he⟩ := hback
  have hbad : orbitCircuitDistance H P σ ≤ 1/10+1/100 :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC.trans hs,he⟩
  rw [hc] at hbad
  norm_num at hbad

/-- On one frozen chain, gate slack about the actual first crossing is at
most the compilation cost of the elapsed time. Each date receives both
the coarse upper fit and the fine lower obstruction. -/
theorem gaussian_crossing_budget_profile :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let x := prefixPoint k ω
      let σ := crossingOrigin (k+1) P (9/80) x
      ∀ t : ℝ, ∀ d : ℕ, (N:ℝ)*(1+|t|) ≤ (2:ℝ)^d →
        ∃ j : ℕ, (j:ℝ) ≤ (N:ℝ)*(1+|t|)*2^(5*d.sqrt+17) ∧
          pathGateDistance (k+1) (P+j) x (σ+t) ≤ 1/8 ∧
          ∀ s, s+j ≤ P → 1/10 < pathGateDistance (k+1) s x (σ+t) := by
  filter_upwards [gaussian_path_spacetime_upper,gaussian_first_crossing_local_width] with ω hsim hfirst
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hsim,hfirst] with k hs hf
  intro N P x σ t d hv
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  have hd (s : ℕ) (v : ℝ) : pathGateDistance (k+1) s x v = orbitCircuitDistance H s v := by
    unfold pathGateDistance orbitCircuitDistance
    rw [show numberedGenerator (k+1) x=H.val from numberedGenerator_shell u]
  obtain ⟨τ,hτ,he,hprior,_⟩ := hf
  have hpos : 0 ≤ localCrossingWidth N := by dsimp only [localCrossingWidth]; positivity
  have hor : σ=τ := crossingOrigin_eq_of_first (hpos.trans hτ.le) ((hd P τ).trans he)
    (fun v hh => (hd P v).trans_lt (hprior v hh))
  obtain ⟨j,hfit,hcost⟩ := hs t d hv
  obtain ⟨hup,hlo⟩ := budget_bracket H he hfit
  refine ⟨j,hcost,?_,?_⟩
  · rw [hor,hd]; exact hup
  · intro s hsj
    rw [hor,hd]; exact hlo s hsj

#print axioms gaussian_crossing_budget_profile
end
end GaloisForLFunctions.HTGeometry.LocalPatches.CrossingProfile
