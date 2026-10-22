import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinWhittakerBesselTail
import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative

/-!
# Argument derivative of the arbitrary-order Schlaefli Bessel carrier

The corpus modified Bessel carrier was differentiable in its complex order and satisfied an exact
order recurrence, but it had no derivative theorem in its positive real argument.  Literal Maass
raising and lowering act on the Whittaker argument, so an abstract order-shift claim cannot replace
this missing identity.

Differentiating the Schlaefli integral under a local integrable dominator and using the hyperbolic
product-to-sum law gives

`d/ds K_nu(s) = -(K_(nu+1)(s) + K_(nu-1)(s))/2`.

The proof constructs the local majorant from the same derivative kernel at half the base argument;
positivity of the Schlaefli phase makes it uniform on a full neighborhood.  This closes the
special-function differentiation input required to expand the two actual Maass steps into a finite
word of Bessel-order shifts.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [BESSEL ARGUMENT DERIVATIVE]`
-/
