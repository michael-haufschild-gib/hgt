/-
# Main theorem areas

This module is the formal proof project's agent-facing entry point.  The project
has six owned theorem areas:

* `GaloisForLFunctions.RHTower`
* `GaloisForLFunctions.HTGeometry`
* `GaloisForLFunctions.Hurwitz`
* `GaloisForLFunctions.U0`
* `GaloisForLFunctions.Bottcher`
* `GaloisForLFunctions.HilbertMetric`

and one vendored area, `GaloisForLFunctions.QuantumAlg`.

Import this module when checking whether the areas still build together.
Prefer the area-specific umbrella while developing inside one theorem program.
-/
import GaloisForLFunctions.RHTower
import GaloisForLFunctions.HTGeometry
import GaloisForLFunctions.Hurwitz
import GaloisForLFunctions.U0
import GaloisForLFunctions.Bottcher
import GaloisForLFunctions.HilbertMetric
import GaloisForLFunctions.QuantumAlg
import GaloisForLFunctions.FullyProvenNewTargets
import GaloisForLFunctions.KummerRootApplications
import GaloisForLFunctions.HTGeometry.NevanlinnaCharacteristicLowerBound
