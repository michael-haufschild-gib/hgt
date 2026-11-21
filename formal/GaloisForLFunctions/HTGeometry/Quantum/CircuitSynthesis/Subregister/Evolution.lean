import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.Lift
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.Eigenphases
import GaloisForLFunctions.HTGeometry.SiteSupportedEvolutionFactorization
import GaloisForLFunctions.RHTower.StaticChoiProjectiveCubicScalarReturnLaw

/-! # Exact synthesis on an arbitrary subset of physical wires -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Subregister
open DiagonalSynthesis
noncomputable section

/-- Gate bound from exact synthesis on k physical wires. -/
def packetCost (k : ℕ) := (4*k+1)*(2*k+2)*(2^k)^2

/-- A projectively exact circuit keeps its budget when placed on a larger register. -/
theorem realizes_place {n k P : ℕ} {S : Finset (Fin n)} (e : Fin k ≃ S) {U : Register k}
    (h : Realizes P U) : Realizes P (place e U) := by
  obtain ⟨z,hz,C,hC,rfl⟩ := h
  exact ⟨z,hz,placeCircuit e C,hC,(place_smul e z _).trans (congrArg (z • ·) (placeCircuit_eval e C).symm)⟩

/-- The all-time gate cost for a packet Hamiltonian depends on the packet size,
including when the addressed wires have gaps in the full register. -/
theorem exact_supported_evolution {n : ℕ} (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (H : selfAdjoint (Register n)) (hsupp : IsSiteSupported (A := fun _ : Fin n => Bool) S H.val) (t : ℝ) :
    Realizes (packetCost S.card) (unitaryEvolution H.val t) := by
  obtain ⟨B,hB⟩ := exists_liftLocalMatrix_of_isSiteSupported hsupp
  have hherm : B.IsHermitian := isHermitian_of_isHermitian_liftLocalMatrix S (hB ▸ H.2.isHermitian)
  let e : Fin S.card ≃ S := S.equivFin.symm
  let f := Equiv.arrowCongr e (Equiv.refl Bool)
  let A := Matrix.reindexAlgEquiv ℂ ℂ f.symm B
  have hA : A.IsHermitian := isHermitian_reindex f.symm hherm
  have he : Matrix.reindexAlgEquiv ℂ ℂ f A = B := by
    ext x y
    simp [A,Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply]
  have h := realizes_place e (exact_evolution_gate_cap hS ⟨A,hA⟩ t)
  rw [hB,unitaryEvolution_liftLocalMatrix]
  change Realizes _ (liftLocalMatrix S (Matrix.reindexAlgEquiv ℂ ℂ f (unitaryEvolution A t))) at h
  rwa [RHTower.unitaryEvolution_reindexAlgEquiv,he] at h

#print axioms exact_supported_evolution
end
end GaloisForLFunctions.HTGeometry.Subregister
