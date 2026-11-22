import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondCoordinates

/-! # Decomposing the nearest-neighbor Hamiltonian into four-dimensional bond blocks -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.BondProducts
noncomputable section
abbrev LocalMatrix := BondCoordinates.LocalMatrix

theorem endpoints_ne {n : ℕ} (e : Fin (n+1)) : e.castSucc ≠ e.succ := BondCoordinates.endpoints_ne e

/-- Each onsite term belongs to its right bond except at the right
endpoint. Every coupling term belongs to its own bond. -/
theorem exists_bond_hamiltonians {n : ℕ} (u : PathShell n) :
    ∃ B : Fin (n+1) → selfAdjoint LocalMatrix, pathHamiltonian u =
      ∑ e, twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e) (B e).val := by
  obtain ⟨B,hB⟩ := BondCoordinates.exists_local_blocks u
  refine ⟨B,?_⟩
  simp only [hB,Finset.sum_comm (s:=Finset.univ (α:=Fin (n+1))) (t:=Finset.univ (α:=PathLabel n)),
    Finset.sum_ite_eq,Finset.mem_univ,if_true,pathHamiltonian_eq_sum]

end
end GaloisForLFunctions.HTGeometry.BondProducts
