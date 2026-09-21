# PW-B completed modular-energy Schwarz structure

- **Route:** PW-B
- **Status:** formalized Lean premise
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularEnergySchwarz`

`energyConj` is the literal componentwise conjugation of the modular value,
real-direction derivative, and imaginary-direction derivative. Lean proves it
anti-linear, isometric, involutive, antiunitary, and maps every completed energy
vector back into `energyDomain`. The proof transports the actual smooth,
compact, PSL2Z-invariant core through conjugation and extends stability over
its closed span. It also proves conjugation covariance of the full cutoff,
forcing vector, and canonical finite-energy `weakResponse`, the last by exact
weak-form transport and nonreal-resolvent uniqueness.

**Proof-chain consequence:** source-to-response Schwarz is closed. The sole
remaining Schwarz bottleneck is transport through the literal ordered CTP
source integral, then critical-fibre cancellation. No source cancellation or
PW magnitude identity is claimed.

**Verification:** `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMModularEnergySchwarz.lean` passed.  The umbrella import is wired; no umbrella build was run.
