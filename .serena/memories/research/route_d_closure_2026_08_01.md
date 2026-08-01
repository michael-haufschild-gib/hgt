# Route D closure/classification (2026-08-01)

## New formal results
- `formal/GaloisForLFunctions/RHTower/PrimeMellinJetEulerSubsetLiftNoGo.lean`: exact finite-Euler-subset norm laws force pairwise zero real covariance; nonsummable positive local energy makes finite-packet norms unbounded. Specialization excludes bounded positive-log prime Mellin-jet lifts even with arbitrary off-diagonal outputs and a fixed Gamma/polar base.
- `formal/GaloisForLFunctions/RHTower/PrimeArchMomentRepresentationRigidity.lean`: any unrestricted positive measure matching all normalized prime-archimedean moments is finite, implies RH, equals the canonical compact Xi-divisor pushforward, and is automatically carried by [0, 2/41]. Existence, unique existence, and RH are equivalent. Any Euclidean spectral node realization has the same pushforward.
- Both imported by `formal/GaloisForLFunctions/RHTower.lean`.
- Stage-3 cards: `route-d-euler-subset-positive-lift-no-go.md` and `route-d-unrestricted-moment-carrier-rigidity.md`.

## Exact frontier
Diagonal lifts, finite-subset-natural off-diagonal lifts, fixed Gamma/polar base corrections, naive positive reciprocity quotients, and alternative positive moment carriers are closed. The only surviving Route D mechanism is a genuinely global signed prime-Gamma boundary/domain defect formed before positivity, followed by a source-derived resolvent-flux identity. That identity pins the quotient divisor to Xi; its positivity is global Weil positivity and is exactly RH. No independent Route D producer below that theorem is known. Do not claim RH proof.

## Verification
- Both target files pass `lake env lean <file>`.
- Final module builds passed; jobs 8746 and 9435.
- `scripts/formal_tools.py lint --check-generated` passed after regenerating indexes.
- Public capstones use only `propext`, `Classical.choice`, `Quot.sound`.
- No numerical computation was used.
