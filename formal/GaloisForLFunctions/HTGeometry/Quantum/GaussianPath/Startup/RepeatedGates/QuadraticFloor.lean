import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.LastPair
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.ShortSignals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.Threshold

/-! # Sharp quadratic error at one gate per physical bond -/
open Filter MeasureTheory Matrix Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
noncomputable section

/-- For almost every Gaussian chain, on each fixed N≥3 prefix the
best error of N−1 gates has exact order t² on both sides of zero. -/
theorem gaussian_quadratic_bond_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
      let N := n+3
      let H := pathHamiltonian (pathPauliDisorderShell ω (n+1))
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        (∀ t : ℝ, HasProjectiveCircuitApproximation N (b*t^2) (n+2) (unitaryEvolution H t)) ∧
        ∀ᶠ t : ℝ in 𝓝 0, ∀ C : TwoQubitCircuit N, C.gateCount ≤ n+2 →
          ∀ z : ℂ, ‖z‖=1 → a*t^2 ≤ ‖unitaryEvolution H t-z • C.eval.val‖ := by
  filter_upwards [gaussian_missing_pair_floor,ConnectedGates.gaussian_minimum_bond_count] with ω hf hfit n
  intro N H
  obtain ⟨a,ha,ht⟩ := hf n
  obtain ⟨b,_,hb,_,hu,_⟩ := hfit (n+1)
  refine ⟨a,b,ha,hb,hu,?_⟩
  filter_upwards [ht] with t h
  exact fun C hC => h C (short_missing_ordered_pair C hC)

#print axioms gaussian_quadratic_bond_floor
end
end GaloisForLFunctions.HTGeometry.RepeatedGates
