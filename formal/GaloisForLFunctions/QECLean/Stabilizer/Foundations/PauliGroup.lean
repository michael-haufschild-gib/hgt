import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroupSingle
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroup.NQubitOperator
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroup.NQubitElement
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroup.TransversalConjugation
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroup.Commutation
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroup.CommutationTactics
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroup.Representation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The N-Qubit Pauli Group

This module is a thin “barrel import” that re-exports the n-qubit Pauli operator and
group development from smaller files:

- `QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator`
- `QEC.Stabilizer.Foundations.PauliGroup.NQubitElement`
- `QEC.Stabilizer.Foundations.PauliGroup.TransversalConjugation`
- `QEC.Stabilizer.Foundations.PauliGroup.Commutation`
- `QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics`
  (tactics `pauli_comm_componentwise`, `pauli_comm_even_anticommutes`)
- `QEC.Stabilizer.Foundations.PauliGroup.Representation`
-/
