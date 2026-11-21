import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.FixedTolerance

/-! # Ordered first returns following the actual near-Hilbert crossing -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels
noncomputable section
open PrecisionReturns

/-- At almost every prescribed error below 9/80, one additional sweep
advances the actual first return simultaneously at every budget through
the crossing budget, on all sufficiently long prefixes of one draw. -/
theorem gaussian_crossing_first_visit_order :
    ∀ᵐ ε : ℝ ∂volume, ε ∈ Ioo (0:ℝ) (9/80) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let x := pathPauliDisorderShell ω (k+1)
        let N := k+3
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
        let P := nearHilbertContinuousCircuitBudget N
        let J := Fintype.card (PathLabel (k+1))
        ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
          ∀ s ≤ P, firstVisit H σ (s+J) ε < firstVisit H σ s ε := by
  filter_upwards [gaussian_prescribed_levels] with ε hε htol
  filter_upwards [hε,LocalPatches.gaussian_first_crossing_local_width] with ω hω hc
  filter_upwards [hc] with k hk
  intro x N H P J
  obtain ⟨σ,hσ,he,hbefore,_⟩ := hk
  have hw : 0 ≤ LocalPatches.localCrossingWidth N := by unfold LocalPatches.localCrossingWidth; positivity
  refine ⟨σ,hw.trans_lt hσ,he,hbefore,?_⟩
  intro s hs
  apply first_visit_strict x htol.1 (hω (k+1)) s σ
  by_contra! h
  obtain ⟨z,hz,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s ε).mpr h
  have hp : orbitCircuitDistance H P σ ≤ ε :=
    (hasProjectiveCircuitApproximation_iff_infDist _ P ε).mp ⟨z,hz,C,hC.trans hs,herr⟩
  exact htol.2.not_ge (he ▸ hp)

#print axioms gaussian_crossing_first_visit_order
end
end GaloisForLFunctions.HTGeometry.ReturnLevels
