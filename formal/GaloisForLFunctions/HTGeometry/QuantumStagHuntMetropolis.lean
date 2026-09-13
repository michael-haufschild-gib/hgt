import GaloisForLFunctions.HTGeometry.QuantumStagHuntGraphPotential

/-!
# Metropolis energy changes for the quantum Stag Hunt Ising model

Exact local-flip and global-inversion energy laws from arXiv:2609.02957. The local
star formula works at every finite degree. Endpoint incidence then specializes global
field inversion to the paper's `8 H sum_i s_i` law on a four-regular graph.
-/

set_option autoImplicit false
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Ising energy terms involving one spin and its `n` neighbors. -/
def localIsingStarEnergy {n : ℕ} (J H s : ℝ) (neighborSpin : Fin n → ℝ) : ℝ :=
  -(J * s * ∑ j, neighborSpin j) - (n : ℝ) * H * s - H * ∑ j, neighborSpin j

/-- Exact Metropolis energy change under a local spin flip. -/
theorem localIsingStarEnergy_flip (n : ℕ) (J H s : ℝ) (neighborSpin : Fin n → ℝ) :
    localIsingStarEnergy J H (-s) neighborSpin -
        localIsingStarEnergy J H s neighborSpin =
      2 * s * (J * ∑ j, neighborSpin j + n * H) := by
  simp [localIsingStarEnergy]
  ring

/-- Field part of the graph Hamiltonian, counted once at each edge endpoint. -/
def graphStagHuntFieldEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : ℝ) (spin : V → ℝ) : ℝ :=
  -H * graphEndpointField G spin

theorem graphEndpointField_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (spin : V → ℝ) :
    graphEndpointField G (fun v => -spin v) = -graphEndpointField G spin := by
  rw [graphEndpointField_eq_degreeWeighted, graphEndpointField_eq_degreeWeighted]
  simp [Finset.sum_neg_distrib]

/-- Pair interactions cancel under global inversion; only endpoint field changes. -/
theorem graphStagHuntFieldEnergy_global_inversion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : ℝ) (spin : V → ℝ) :
    graphStagHuntFieldEnergy G H (fun v => -spin v) -
        graphStagHuntFieldEnergy G H spin =
      2 * H * graphEndpointField G spin := by
  rw [graphStagHuntFieldEnergy, graphStagHuntFieldEnergy, graphEndpointField_neg]
  ring

/-- Paper's `z=4` global-inversion law on a concrete four-regular graph. -/
theorem graphStagHuntFieldEnergy_completeGraph_finFive_global_inversion
    (H : ℝ) (spin : Fin 5 → ℝ) :
    graphStagHuntFieldEnergy (SimpleGraph.completeGraph (Fin 5)) H (fun v => -spin v) -
        graphStagHuntFieldEnergy (SimpleGraph.completeGraph (Fin 5)) H spin =
      8 * H * ∑ v, spin v := by
  rw [graphStagHuntFieldEnergy_global_inversion, graphEndpointField_completeGraph_finFive]
  ring

end
end GaloisForLFunctions.HTGeometry
