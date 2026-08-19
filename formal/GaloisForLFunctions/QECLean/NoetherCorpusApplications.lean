import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroupSingle.Representation
import GaloisForLFunctions.QuantumAlg.Core.Base.Gate

/-!
# Noether applications in quantum error correction

Every single-qubit Pauli-group element carries a bundled unitary certificate.  It therefore
preserves both state norm and transition amplitude without proposition-valued premises.
-/

noncomputable section

namespace Quantum.PauliGroupElement

/-- Pauli-group symmetry conserves one-qubit state norm. -/
theorem noetherFirst_pauliGroupNorm
    (p : PauliGroupElement) (psi : QuantumAlg.StateVector (QuantumAlg.Qubits 1)) :
    ‖QuantumAlg.HilbertOperator.applyVec (toMatrix p) psi‖ = ‖psi‖ :=
  QuantumAlg.HilbertOperator.norm_applyVec_of_mem_unitaryGroup
    (toMatrix_mem_unitaryGroup p) psi

/-- Pauli-group symmetry conserves one-qubit transition amplitudes. -/
theorem noetherFirst_pauliGroupInner
    (p : PauliGroupElement)
    (psi phi : QuantumAlg.StateVector (QuantumAlg.Qubits 1)) :
    inner ℂ (QuantumAlg.HilbertOperator.applyVec (toMatrix p) psi)
        (QuantumAlg.HilbertOperator.applyVec (toMatrix p) phi) =
      inner ℂ psi phi :=
  QuantumAlg.HilbertOperator.inner_applyVec_applyVec_of_mem_unitaryGroup
    (toMatrix_mem_unitaryGroup p) psi phi

end Quantum.PauliGroupElement
