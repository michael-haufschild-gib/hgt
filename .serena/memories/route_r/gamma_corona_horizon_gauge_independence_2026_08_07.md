# Route R Gamma-corona horizon gauge independence (2026-08-07)

Formal module: `formal/GaloisForLFunctions/RHTower/RouteRGammaCoronaHorizonGaugeIndependence.lean`.
Formalized card: `docs/drafts/pipeline/3-formalized/route-r-gamma-corona-horizon-gauge-independence.md`.

## New theorem
The local/global singular-corona criterion is independent of every nonzero corona horizon:
`routeRTwoThreeGammaCorona_global_eq_local_at_iff_port_eq_zero`.

Constructed intrinsic ordered-prime horizon
`routeRCrossPrimeArithmeticHorizonCoefficient(p,q)=1/(p*q)`.
Proved square summability, every coordinate nonzero, orientation-swap symmetry, exclusion from finite arithmetic core, and nonzero singular-corona class.

`routeRTwoThreeGammaCorona_original_globalization_iff_arithmetic` proves the all-divisor original encoded-horizon globalization theorem iff its intrinsic arithmetic-horizon version.

## Conjecture loop
- C23 swap kills odd port: falsified; ordered witnesses are independent.
- C24 full permutation naturality selects nonzero horizon: falsified; invariant l2 vector is zero.
- C25 arithmetic selects unique horizon: falsified; many (pq)^(-s) choices.
- C26 horizon is gauge, not data: paper- and Lean-proved.

## Frontier
Removed arbitrary Encodable horizon normalization from open RH-bearing obligation. Remaining core is unchanged scalar source law: derive singular Cartier/Stokes annihilation of `routeRTwoThreeGammaCartierTransportPort rho` from pre-divisor rational-adelic/Euler-Gamma structure. This work does not prove port vanishing or RH.

## Audit
`lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.RouteRGammaCoronaHorizonGaugeIndependence` passed; `scripts/formal_tools.py lint` passed. Principal theorem axioms: `[propext, Classical.choice, Quot.sound]`. Umbrella wired.