import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Symplectic
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Homological
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Concatenation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Framework

Abstract stabilizer + homological theory. Depends on `Foundations` only.

Sub-clusters:
- `QEC.Stabilizer.Framework.Core` — general stabilizer / logical / CSS theory
- `QEC.Stabilizer.Framework.Symplectic` — stabilizer ↔ symplectic bridge
- `QEC.Stabilizer.Framework.Homological` — chain-complex / CSS framework
- `QEC.Stabilizer.Framework.Concatenation` — block-embedding calculus (M1)
-/
