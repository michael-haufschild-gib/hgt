import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric
import GaloisForLFunctions.QECLean.Stabilizer.Codes.RotatedSurface
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Repetition
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Iceberg
import GaloisForLFunctions.QECLean.Stabilizer.Codes.BivariateBicycle
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Small
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Concat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Codes

Concrete stabilizer codes, organized by family:
- `Toric`          — parametric toric code (code + lattice + homology)
- `RotatedSurface` — rotated surface code (code + lattice + homology)
- `Repetition`     — classical repetition codes
- `Iceberg`        — parametric `[[2m, 2m−2, 2]]` iceberg / generalized
                     parity code family
- `BivariateBicycle` — chain-level gross `[[144,12,12]]` code + bb72 base
- `Small`          — single-instance codes (Shor9, Steane7, [[5,1,3]], …)

(Upstream's `_TEMPLATE.lean` scaffold is not vendored: it carries a deliberate `sorry`.)
-/
