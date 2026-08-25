# Route P prime/Gamma wall Xi correction-curvature law (2026-08-25)

## Result

Formalized the positive rigidity survivor forced by scalar-rescaling no-gos:

- `routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_zero`
- `iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_one`
- `iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two`
- `zero_lt_re_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two_of_one_le`
- `eventually_zero_lt_re_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two`

Module:
`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionCurvature.lean`

Card:
`docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-xi-malgrange-correction-curvature.md`

## Mathematical delta

Normalize wall irregular time by `c_Xi = normalizedPrimeArchMoment 0 / 2`, forcing equality of first logarithmic tau jets. The correction germ `A_d = log Xi - log D_d(c_Xi ·)` satisfies

`A_d(0)=0`, `A_d'(0)=0`, and
`A_d''(0)=2 c_Xi^2 (P_wall(d)-P_Xi)`.

Existing source inequalities imply `Re A_d''(0)>0` for every `d>=1` and eventually as `d→0+`. Thus any viable irregular-RH realization needs genuine even Stokes/Malgrange data; scalar clock normalization and constant tau gauge cannot absorb the defect.

This is a positive classification/rigidity theorem, not RH closure and not yet a source-derived construction of the correction. Novelty remains unverified.

## Verification

Direct targeted `lake env lean` passed. Five public theorems have axioms only `[propext, Classical.choice, Quot.sound]`. Formal lint accepts new reachable module; repository lint remains nonzero for unrelated reachability failures. Scratch files removed. Frontier map remained read-only.

## Next live core

Audit `SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel` and related source-only quadratic anomaly against required correction curvature. Exact question: can an independent prime--Gamma even Stokes channel produce the projective defect without Xi-fed parameters?

Related memories:
- `mem:route-p/prime-gamma-wall-xi-tau-explicit-cold-no-go-2026-08-25`
- `mem:route-p/wild-saddle-stokes-parity-quadratic-anomaly-2026-08-25`
