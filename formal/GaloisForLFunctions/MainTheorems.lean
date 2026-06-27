/-
# Main theorem areas

This module is the formal proof project's agent-facing entry point.  The project
currently has three active theorem areas:

* `GaloisForLFunctions.Hurwitz`
* `GaloisForLFunctions.U0`
* `GaloisForLFunctions.Bottcher`

Import this module when checking whether the three programs still build together.
Prefer the area-specific umbrella while developing inside one theorem program.
-/
import GaloisForLFunctions.Hurwitz
import GaloisForLFunctions.U0
import GaloisForLFunctions.Bottcher
