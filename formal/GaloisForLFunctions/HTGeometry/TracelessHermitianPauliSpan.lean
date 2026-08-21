/-
# A traceless Hermitian qubit Hamiltonian is a real combination of nonidentity Pauli strings

The Pauli strings are a real basis of the Hermitian matrix space, and the identity coordinate of a
Hermitian matrix is its normalized trace, so tracelessness is exactly the vanishing of that one
coordinate.  Every Pauli label on `n` qubits has weight at most `n`, so a traceless Hermitian
Hamiltonian on `n` qubits lies in the bounded-weight Pauli span at every threshold `q ≥ n`.

Main results:
* `pauliWeight_le` — every label has weight at most the number of qubits.
* `mem_pauliSpan_of_isHermitian_of_trace_zero` — **the span statement**.
-/
import GaloisForLFunctions.HTGeometry.PauliBoundedWeightSpan
import GaloisForLFunctions.HTGeometry.TracelessPauliIdentityCoordinate

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem pauliWeight_le {n : ℕ} (P : Fin n → Option (Fin 3)) : pauliWeight P ≤ n := by
  classical
  rw [pauliWeight]
  calc (Finset.univ.filter fun s => P s ≠ none).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

/-- **Every traceless Hermitian qubit Hamiltonian is a real combination of nonidentity Pauli
strings of weight at most the number of qubits.** -/
theorem mem_pauliSpan_of_isHermitian_of_trace_zero {n q : ℕ} (hq : n ≤ q)
    {H : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hH : H.IsHermitian) (htr : H.trace = 0) :
    H ∈ pauliSpan n q := by
  classical
  have hsa : H ∈ selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) := hH
  obtain ⟨Hsa, hHsa⟩ : ∃ Hsa : selfAdjoint (Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ), (Hsa : Matrix _ _ ℂ) = H := ⟨⟨H, hsa⟩, rfl⟩
  have hzero := hasZeroPauliIdentityCoordinate_of_trace_eq_zero n Hsa (by rw [hHsa]; exact htr)
  have hexp := (finitePauliSelfAdjointBasis (Fin n)).sum_repr Hsa
  have hcoe : H = ∑ P : Fin n → Option (Fin 3),
      ((finitePauliSelfAdjointBasis (Fin n)).repr Hsa P : ℝ) • finitePauliMatrix P := by
    rw [← hHsa]
    conv_lhs => rw [← hexp]
    push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [finitePauliSelfAdjointBasis_apply]
    rfl
  rw [hcoe]
  refine Submodule.sum_mem _ fun P _ => ?_
  by_cases hP : P = pauliIdentityLabel n
  · subst hP
    rw [HasZeroPauliIdentityCoordinate] at hzero
    rw [hzero, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _
      (finitePauliMatrix_mem_pauliSpan (le_trans (pauliWeight_le P) hq) hP)

end GaloisForLFunctions.HTGeometry

end
