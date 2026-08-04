import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroupSingle.Core
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroupSingle.Operator
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroupSingle.Phase
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroupSingle.Element
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroupSingle.Representation
import GaloisForLFunctions.QECLean.Stabilizer.Foundations.PauliGroupSingle.Commutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The Pauli Group on a Single Qubit

This module is a thin “barrel import” that re-exports the single-qubit Pauli group
development from smaller files:

- `QEC.Stabilizer.Foundations.PauliGroupSingle.Core`
- `QEC.Stabilizer.Foundations.PauliGroupSingle.Operator`
- `QEC.Stabilizer.Foundations.PauliGroupSingle.Phase`
- `QEC.Stabilizer.Foundations.PauliGroupSingle.Element`
- `QEC.Stabilizer.Foundations.PauliGroupSingle.Representation`
- `QEC.Stabilizer.Foundations.PauliGroupSingle.Commutation`
-/
