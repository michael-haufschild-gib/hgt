import GaloisForLFunctions.HTGeometry.NearestNeighborQuditPathRecurrenceLaw
import GaloisForLFunctions.HTGeometry.CommutingHermitianSpectrumSum

/-!
# Nearest-neighbour qubit chains have generically maximal projective rank

The open `n`-qubit path specialisation of the generic qudit-path law: for almost every
traceless onsite-plus-nearest-neighbour qubit Hamiltonian the spectrum is simple, trace is the
only rational affine relation among the `2 ^ n` eigenvalues, and the anchored projective rank is
the maximal value `2 ^ n - 1`.

The contrast with commuting locality is exact: a Hamiltonian written as `m` commuting two-qubit
terms has anchored projective rank at most `3 m`.
-/

open Set SimpleGraph MeasureTheory Topology Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Generic nearest-neighbour qubit chain law.**  For every open path of at least two qubits the
full real trace-zero onsite-plus-edge Hamiltonian space contains a dense residual full-measure set
on which the spectrum is simple, has no nontrivial balanced rational relation, and has anchored
projective rank exactly `2 ^ n - 1`. -/
theorem exists_uniformQubitChainMaximalRank_dense_residual_fullMeasure
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
    ∃ e : Z.spectral.Observer ≃ Fin n,
      Z.architectureGraph = SimpleGraph.comap e (SimpleGraph.pathGraph n) ∧
      Z.spectral.stateCard = 2 ^ n ∧
      (letI : Fintype Z.PhysicalState := Z.physicalFintype
       letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
       let L := Z.tracelessLocalHamiltonianSubmodule
       let hL := Z.tracelessLocalHamiltonianSubmodule_le_selfAdjoint
       let S := realHermitianSubmoduleMaximalSet L hL
       Dense S ∧ S ∈ residual (Fin (Module.finrank ℝ L) → ℝ) ∧
         volume Sᶜ = 0 ∧
         ∀ p ∈ S,
           let hH := realAffineMatrix_isHermitian
             0 (realMatrixSubmoduleGenerator L)
             Matrix.isHermitian_zero
             (realMatrixSubmoduleGenerator_isHermitian L hL) p
           Function.Injective hH.eigenvalues ∧
             MaximallyProjectiveEnergy hH.eigenvalues ∧
             ∀ reference : Z.PhysicalState,
               anchoredTemporalRank hH.eigenvalues reference = 2 ^ n - 1) := by
  obtain ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull, hgeneric⟩ :=
    exists_uniformQuditPathTracelessRecurrenceGeometry_dense_residual_fullMeasure
      n 2 hn le_rfl
  refine ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull, ?_⟩
  intro p hp
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  obtain ⟨hmax, hrest⟩ := hgeneric p hp
  refine ⟨hmax.injective, hmax, ?_⟩
  intro reference
  exact (hrest reference).1

end

end GaloisForLFunctions.HTGeometry
