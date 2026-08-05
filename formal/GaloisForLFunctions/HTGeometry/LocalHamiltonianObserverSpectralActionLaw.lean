import GaloisForLFunctions.HTGeometry.NearestNeighborQuditPathRecurrenceLaw
import GaloisForLFunctions.HTGeometry.IntrinsicReplicaObserverSpectralActionLaw

/-!
# Observer--spectral action law for ordinary local Hamiltonians

Maximal projective spectral rank is exactly the arithmetic input making the
universal intrinsic replica action bound land at the unavoidable permutation
plateau.  The generic nearest-neighbour qudit recurrence theorem supplies
that input on a dense residual full-measure set of ordinary static local
Hamiltonians.
-/

open Set SimpleGraph MeasureTheory Topology Filter
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every positive normalized spectral weighting and every replica order
obeys the intrinsic unit-constant action bound to the permutation floor. -/
def HasIntrinsicReplicaObserverSpectralActionLaw
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) : Prop :=
  ∀ (weight : I → ℝ),
    (∀ i, 0 < weight i) →
    (∑ i, weight i = 1) →
    ∀ (r : ℕ) (T : ℝ), 0 < T →
      ‖finiteSpectralSurvivalFidelityMean weight energy r T -
          (fidelityReplicaPermutationFloor weight r : ℂ)‖ ≤
        min 1 (T * intrinsicReplicaActionResolution energy r)⁻¹

/-- Maximal projective rank forces the complete intrinsic observer--spectral
action law at every replica order simultaneously. -/
theorem MaximallyProjectiveEnergy.hasIntrinsicReplicaObserverSpectralActionLaw
    {I : Type*} [Fintype I] [DecidableEq I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy) :
    HasIntrinsicReplicaObserverSpectralActionLaw energy := by
  intro weight hweight hsum r T hT
  exact norm_finiteSpectralSurvivalFidelityMean_sub_floor_le_intrinsic
    hweight hsum hmax r hT

/-- **Ordinary local-Hamiltonian observer--spectral action law.** For every
open path of at least two `q`-level sites, `q ≥ 2`, the full real trace-zero
onsite-plus-edge Hamiltonian coefficient space contains a dense residual
full-Lebesgue-measure set on which the intrinsic unit-constant action law
holds for every positive normalized spectral weighting and every replica
order. -/
theorem
    exists_uniformQuditPathTracelessIntrinsicObserverSpectralAction_dense_residual_fullMeasure
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ Z : PhysicallyRealizedTensorTreeSystem.{0},
    ∃ e : Z.spectral.Observer ≃ Fin n,
      Z.architectureGraph =
          SimpleGraph.comap e (SimpleGraph.pathGraph n) ∧
      Z.spectral.stateCard = q ^ n ∧
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
           HasIntrinsicReplicaObserverSpectralActionLaw hH.eigenvalues) := by
  obtain ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull, hrecurrence⟩ :=
    exists_uniformQuditPathTracelessRecurrenceGeometry_dense_residual_fullMeasure
      n q hn hq
  refine ⟨Z, e, hgraph, hstate, hdense, hresidual, hnull, ?_⟩
  intro p hp
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  exact (hrecurrence p hp).1.hasIntrinsicReplicaObserverSpectralActionLaw

end

end GaloisForLFunctions.HTGeometry
