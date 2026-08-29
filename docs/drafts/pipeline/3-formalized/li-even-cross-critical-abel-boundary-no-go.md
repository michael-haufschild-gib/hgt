# LI even-cross critical Abel boundary no-go

- **ID:** LI-CAB1.NG
- **Stage:** 3-formalized
- **Lean module:** `GaloisForLFunctions.RHTower.LiEvenCrossCriticalAbelBoundaryNoGo`
- **Corpus source:** `LiEvenSquarePrimeGammaCrossBalanceCriterion`, `XiShiftedHardEdgePrimeGammaSourceDisintegration`, `CayleyLaguerreFourier`, `OddEulerCombTemperedAdmissionWall`

## Result

For the zeroth LI common-reversal channel at hard-edge mass `1/2`, Lean proves

`g(x) = (1/2)x^2/(x^2+1/4)^2`

and

`Fourier(g)(xi) = (pi/2) exp(-|xi|/2) (1-|xi|/2)`.

The literal absolute prime-leg weight satisfies the exact identity

`(Lambda(n)/sqrt(n)) * ||Fourier(g)(log n)||`
`= (pi/2) * (Lambda(n)/n) * |1-log(n)/2|`

and is not summable. Separate absolute summation followed by prime--Gamma subtraction is therefore impossible at the critical LI boundary.

## Positive survivor

For every LI mode `n`, the critical filtered cross density is exactly

`(1-u(x)^2) U_n(u(x))^2 / 2`,

where `u(x)=(1/4-x^2)/(1/4+x^2)`. Lean proves `u(x)^2 <= 1` and hence unconditional pointwise nonnegativity of every mode. The only surviving producer is the completed Abel prime--polar--Gamma finite part.

## RH chain

The open next theorem has a fixed non-circular passport:

`completed Abel prime--polar--Gamma finite part >= 0 for every mode`
`=> LI common-reversal cross capitals >= 0`
`=> positive even paired Li coefficients >= 0`
`=> RiemannHypothesis`.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossCriticalAbelBoundaryNoGo.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossCriticalAbelBoundaryNoGo`: passed.
- Umbrella import added to `GaloisForLFunctions/RHTower.lean`.
- Capstone axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Global formal lint still reports pre-existing unreachable modules outside this work; this module is wired and contains no forbidden declarations.
