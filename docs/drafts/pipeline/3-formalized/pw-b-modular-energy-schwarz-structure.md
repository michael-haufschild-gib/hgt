# PW-B completed modular-energy Schwarz structure

- **Route:** PW-B
- **Status:** formalized Lean premise
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularEnergySchwarz`

`energyConj` is the literal componentwise conjugation of the modular value,
real-direction derivative, and imaginary-direction derivative. Lean proves it
anti-linear, isometric, involutive, antiunitary, and maps every completed energy
vector back into `energyDomain`. The proof transports the actual smooth,
compact, PSL2Z-invariant core through conjugation and extends stability over
its closed span. It also proves conjugation covariance of the full cutoff,
forcing vector, and canonical finite-energy `weakResponse`, the last by exact
weak-form transport and nonreal-resolvent uniqueness.

**Proof-chain consequence:** forcing-to-finite-energy-weak-response Schwarz,
the separately glued smooth field, and the literal angular direct-minus-image
kernel are closed. Remaining bottlenecks are the time-reduced source coefficient,
the ordered CTP source integral, and critical-fibre cancellation. No source
cancellation or PW magnitude identity is claimed.

**Verification:** the angular-Schwarz module audit passed before the current
time-source additions. The new radial and residual source identities were
independently audited in dependency-closed leaf files with `lake env lean`;
the parent-module audit exceeded its 55-second cap without a diagnostic and
must be rerun once current formal activity clears. The umbrella import is
wired; no umbrella build was run.
