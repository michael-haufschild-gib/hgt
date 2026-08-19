import GaloisForLFunctions.QuantumAlg.Core.Circuit
import GaloisForLFunctions.QuantumAlg.Core.Components.Gates
import GaloisForLFunctions.QuantumAlg.Primitives.QFT
import GaloisForLFunctions.QuantumAlg.Primitives.SwapTest

/-!
# Noether applications for quantum gates and circuits

Unitary symmetry conserves the Hilbert norm and inner product.  Since gates and circuits bundle
their unitarity proofs, all results below have no proposition-valued premises.
-/

noncomputable section

namespace QuantumAlg

/-- Every bundled quantum gate conserves state norm. -/
theorem noetherFirst_gateNorm
    {R : Register} (U : Gate R) (psi : StateVector R) :
    ‖U.op.applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup U.unitary psi

/-- Every bundled quantum gate conserves transition amplitudes. -/
theorem noetherFirst_gateInner
    {R : Register} (U : Gate R) (psi phi : StateVector R) :
    inner ℂ (U.op.applyVec psi) (U.op.applyVec phi) = inner ℂ psi phi :=
  HilbertOperator.inner_applyVec_applyVec_of_mem_unitaryGroup U.unitary psi phi

/-- Every complete circuit conserves state norm. -/
theorem noetherFirst_circuitNorm
    {R : Register} (circuit : Circuit R) (psi : StateVector R) :
    ‖circuit.matrix.op.applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup circuit.matrix_unitary psi

/-- Every complete circuit conserves transition amplitudes. -/
theorem noetherFirst_circuitInner
    {R : Register} (circuit : Circuit R) (psi phi : StateVector R) :
    inner ℂ (circuit.matrix.op.applyVec psi) (circuit.matrix.op.applyVec phi) =
      inner ℂ psi phi :=
  HilbertOperator.inner_applyVec_applyVec_of_mem_unitaryGroup
    circuit.matrix_unitary psi phi

/-- Pauli-X conserves one-qubit norm. -/
theorem noetherFirst_pauliXNorm (psi : StateVector (Qubits 1)) :
    ‖Gate.X.op.applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup Gate.X_mem_unitaryGroup psi

/-- Pauli-Y conserves one-qubit norm. -/
theorem noetherFirst_pauliYNorm (psi : StateVector (Qubits 1)) :
    ‖Gate.Y.op.applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup Gate.Y_mem_unitaryGroup psi

/-- Pauli-Z conserves one-qubit norm. -/
theorem noetherFirst_pauliZNorm (psi : StateVector (Qubits 1)) :
    ‖Gate.Z.op.applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup Gate.Z_mem_unitaryGroup psi

/-- Hadamard conserves one-qubit norm. -/
theorem noetherFirst_hadamardNorm (psi : StateVector (Qubits 1)) :
    ‖Gate.H.op.applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup Gate.H_mem_unitaryGroup psi

/-- CNOT conserves two-qubit norm. -/
theorem noetherFirst_cnotNorm (psi : StateVector (Qubits 2)) :
    ‖Gate.CNOT.op.applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup Gate.CNOT_mem_unitaryGroup psi

/-- Quantum Fourier transform conserves every `n`-qubit norm. -/
theorem noetherFirst_qftNorm (n : ℕ) (psi : StateVector (Qubits n)) :
    ‖(QFTMatrix n).applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup (QFT_mem_unitaryGroup n) psi

/-- Register swap conserves norm on the doubled register. -/
theorem noetherFirst_swapRegistersNorm
    (n : ℕ) (psi : StateVector (Qubits (n + n))) :
    ‖(swapRegisters n).op.applyVec psi‖ = ‖psi‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup
    (swapRegisters_mem_unitaryGroup n) psi

end QuantumAlg
