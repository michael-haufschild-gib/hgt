/-
# Main theorem areas

This module is the formal proof project's agent-facing entry point.  The project
has seven owned theorem areas:

* `GaloisForLFunctions.RHTower`
* `GaloisForLFunctions.HTGeometry`
* `GaloisForLFunctions.Hurwitz`
* `GaloisForLFunctions.U0`
* `GaloisForLFunctions.Bottcher`
* `GaloisForLFunctions.HilbertMetric`
* `GaloisForLFunctions.SelbergClass`
* `GaloisForLFunctions.BiScaleUncertainty`
* `GaloisForLFunctions.BezoutValuationIncidence`

and three vendored areas:

* `GaloisForLFunctions.QuantumAlg` — quantum algorithms.
* `GaloisForLFunctions.PNTPlus` — PrimeNumberTheoremAnd: Selberg sieve,
  Brun–Titchmarsh, Perron/Mellin calculus, Wiener–Ikehara, zeta bounds, and the
  prime number theorem with a `(log x)^{1/10}`-exponent error term.
* `GaloisForLFunctions.QECLean` — quantum error correction: the Pauli and
  binary-symplectic layer, the stabilizer-code framework, and concrete code
  families (toric, rotated surface, Steane, Shor, bivariate-bicycle).

Import this module when checking whether the areas still build together.
Prefer the area-specific umbrella while developing inside one theorem program.
-/
import GaloisForLFunctions.RHTower
import GaloisForLFunctions.HTGeometry
import GaloisForLFunctions.Hurwitz
import GaloisForLFunctions.U0
import GaloisForLFunctions.Bottcher
import GaloisForLFunctions.HilbertMetric
import GaloisForLFunctions.SelbergClass
import GaloisForLFunctions.BiScaleUncertainty
import GaloisForLFunctions.BezoutValuationIncidence
import GaloisForLFunctions.QuantumAlg
import GaloisForLFunctions.PNTPlus
import GaloisForLFunctions.QECLean
import GaloisForLFunctions.FullyProvenNewTargets
import GaloisForLFunctions.KummerRootApplications
import GaloisForLFunctions.HTGeometry.NevanlinnaCharacteristicLowerBound
