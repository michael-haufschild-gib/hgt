# Suzuki critical rooted Bianchi cofinal no-go — formalization certificate

## Status

`[LEAN-PROVED] [UNCONDITIONAL] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`

## Paper source

`./suzuki-critical-rooted-bianchi-cofinal-no-go.md`

## Lean source

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRootedBianchiCofinalNoGo.lean`

## Formal theorem surface

- `suzukiRootedBianchiPrimeMassAt_neg_half`: exact critical inverse-translation identity
  `b_(-1/2)(p)=Lambda(p)/sqrt(p)`.
- `log_two_mul_primeHarmonic_le_suzukiCriticalRootedBianchiPrimeMass`: prime-harmonic comparison.
- `not_summable_suzukiCriticalRootedBianchiPrimeMass`: critical diagonal diverges.
- `suzukiCriticalRootedBianchiPrimeAmplitude_sq`: square-root feature has exact critical mass.
- `vonMangoldtGammaRenormalizedBoundaryCoordinate_neg_half_prime`: source connector identifying
  feature with existing uniquely renormalized complete Gamma-conormal boundary coordinate.
- `not_summable_sq_suzukiCriticalRootedBianchiPrimeAmplitude`: no unrenormalized critical
  `ell^2` Gram vector.
- `summable_const_mul_sq_suzukiCriticalRootedBianchiPrimeAmplitude_iff`: scalar-renormalization
  rigidity; constant residual is square-summable iff it vanishes exactly.
- `not_summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_neg_half_prime`: no-go stated
  directly on existing corpus source coordinate.

## Scientific result

Original `SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM` architecture cannot pass raw rooted Bianchi leg to
independent critical Hilbert limit.  Exact source normalization lands at divergent weight
`Lambda(p)/sqrt(p)`.  Even scalar correction fails unless leading coefficient cancels exactly.

Finite aperture survives.  Corrected frontier is
`SUZUKI-FINITE-APERTURE-RENORMALIZED-MIDPOINT-GRAM`: form prime-dependent Volterra/Gamma/polar
residual coordinate before squaring, prove finite compound kernel is Gram, then pass already
cancelled kernel cofinally.

RH is not claimed proved.

## Verification

- Direct Lean check: passed with
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRootedBianchiCofinalNoGo.lean`.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or RH premise.
- Forbidden-token scan: clean.
- Repository formal lint: passed.
- Final targeted build: passed with
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` (9443 jobs).
- No numerical computation and no prime-number theorem used.
