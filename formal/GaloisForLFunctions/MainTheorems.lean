/-
# Main theorem areas

This module is the formal proof project's agent-facing entry point.  The project
has five owned theorem areas:

* `GaloisForLFunctions.RHTower`
* `GaloisForLFunctions.HTGeometry`
* `GaloisForLFunctions.Hurwitz`
* `GaloisForLFunctions.U0`
* `GaloisForLFunctions.Bottcher`

Import this module when checking whether the five areas still build together.
Prefer the area-specific umbrella while developing inside one theorem program.
-/
import GaloisForLFunctions.RHTower
import GaloisForLFunctions.HTGeometry
import GaloisForLFunctions.Hurwitz
import GaloisForLFunctions.U0
import GaloisForLFunctions.Bottcher
import GaloisForLFunctions.FullyProvenNewTargets
import GaloisForLFunctions.KummerRootApplications
import GaloisForLFunctions.HTGeometry.NevanlinnaCharacteristicLowerBound
