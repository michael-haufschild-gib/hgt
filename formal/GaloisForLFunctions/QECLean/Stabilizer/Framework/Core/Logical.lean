import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.Logical.LogicalOperators
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.Logical.LogicalOperatorCoset
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.Logical.LogicalGates
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.Logical.LogicalGateGroup
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.Logical.LogicalCliffordAction
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.Logical.CodeDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Core: logical-operator theory

Logical operators, their cosets, logical gates, the Clifford action on
logicals, and code distance (distance is fundamentally a property of
nontrivial logicals — `chainWeight_lower_bound_transfers` etc.).
-/
