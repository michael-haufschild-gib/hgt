import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.ThreeGateUpper
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.BasisCost
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.PhysicalWindow

/-! # Physical cost of the basis implementing a short spectral circuit -/
open MeasureTheory Matrix Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- Three gates are attainable after conjugation, but every basis that
reduces the evolution to j gates costs b with 2b+j above the physical
spanning floor, even when the basis itself is only approximated. -/
theorem gaussian_basis_cost_floor {a T η δ : ℝ} (ha : 0 < a) (hη : 0 < η)
    (hδ : 0 ≤ δ) (herr : 1/10+2*δ < Real.sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc a T,
      let U := unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t
      (∃ W : unitaryGroup (Fin (n+2) → Bool) ℂ,
        HasProjectiveCircuitApproximation (n+2) (1/10) 3 (W.val*U*star W.val)) ∧
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (b j : ℕ),
        HasProjectiveCircuitApproximation (n+2) δ b W.val →
        HasProjectiveCircuitApproximation (n+2) (1/10) j (W.val*U*star W.val) →
        (1-η)*(n+1:ℕ) < ((2*b+j:ℕ):ℝ) := by
  filter_upwards [gaussian_three_gate_conjugate_upper,
    SpanningDensity.FixedHorizon.gaussian_uniform_gate_floor (T:=T) ha hη (by positivity) herr] with ω hu hf
  filter_upwards [hu a T ha,hf] with n hn hl
  intro t ht U
  refine ⟨hn t ht,?_⟩
  intro W b j hW hj
  let V : unitaryGroup (Fin (n+2) → Bool) ℂ := ⟨U,unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian _) t⟩
  exact hl t ht _ (SpectralApproximation.cost_in_physical_basis V W hW hj)

#print axioms gaussian_basis_cost_floor
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
