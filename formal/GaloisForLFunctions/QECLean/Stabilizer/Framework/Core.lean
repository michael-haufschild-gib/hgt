import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.Stabilizer
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.Logical
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Core.CSS

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Framework.Core

Abstract stabilizer-formalism content, split into three buckets:
- `QEC.Stabilizer.Framework.Core.Stabilizer` — stabilizer-group + codespace + centralizer
- `QEC.Stabilizer.Framework.Core.Logical`    — logical-operator theory + code distance
- `QEC.Stabilizer.Framework.Core.CSS`        — CSS-code theory
-/
