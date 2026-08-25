# Route P prime/Gamma wall explicit cold no-go (2026-08-25)

## Result

Formalized unconditional source-native theorem excluding scalar-rescaled Xi germ matches for every aperture d >= 1:

`RHTower.forall_one_le_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt`.

Module:
`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauExplicitColdNoGo.lean`

Card:
`docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-xi-tau-explicit-cold-no-go.md`

## Quantitative chain

- `sum_p log(p)/p^3 < 25 log(2)/96`.
- For every d >= 1, normalized prime-2 wall mass is (>12/25).
- Cubic Stokes coherence expectation is (>9/40).
- Prime/Gamma wall projective Fredholm two-jet real part is (>9/80).
- Xi projective invariant is (<9/80), contradicting equality of scalar-rescaled logarithmic germs.

Tail proof splits primes 3,5,7,11 and dominates p>11 by
`(1/13) sum_{n>11} log(n)/n^2 <= (log 11 + 1)/143`.
Rational log certificates:
`log 3 < 6/5`, `log 5 < 17/10`, `log 7 < 2`, `log 11 < 5/2`, `log 2 > 2/3`.

## Verification

Direct targeted Lean check passed. Five public declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
Formal lint reports no issue in new module; remaining errors are unrelated umbrella reachability.

## Survivor/open core

Together with punctured wild-boundary no-go, any scalar-rescaled match is confined below aperture one and outside the already-excluded d -> 0+ collar. Global coherence monotonicity remains unjustified. Next real open core is bounded intermediate aperture, likely requiring changed even Stokes data or a non-circular source-to-Xi comparison.

Related memories:
- `mem:route-p/prime-gamma-wall-xi-tau-boundary-neighborhood-no-go-2026-08-25`
- `mem:route-p/prime-gamma-wall-xi-tau-cold-boundary-no-go-2026-08-25`
- `mem:route-p/wild-saddle-stokes-parity-quadratic-anomaly-2026-08-25`
