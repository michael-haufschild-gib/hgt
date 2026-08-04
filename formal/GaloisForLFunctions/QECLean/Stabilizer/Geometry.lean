import GaloisForLFunctions.QECLean.Stabilizer.Geometry.FinPeriodic
import GaloisForLFunctions.QECLean.Stabilizer.Geometry.GridIndexing
import GaloisForLFunctions.QECLean.Stabilizer.Geometry.CellComplexTypes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Geometry

Lattice-family-agnostic geometric primitives:
- `FinPeriodic`: modular arithmetic on `Fin L` (`next`, `prev`)
- `GridIndexing`: row-major / column-major coordinate encodings
- `CellComplexTypes`: abstract `EdgeIdx`, `FaceIdx`, `VtxIdx` and chain types
-/
