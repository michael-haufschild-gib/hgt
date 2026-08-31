# Gamma-sewn diffuse-prime recovery and Sonin zeroth-moment weld

- **ID:** GSDP-S0
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md`; Gamma-sewn recovery × Sonin positive-moment frontier
- **Statement:** Vanishing local prime apertures can retain fixed aggregate prime-log action, locally faithful Gamma coefficients, positive Sonin order, and exact completed zeroth-moment landing on one source-selected effective aperture.

## Goal

Test whether diffuse prime recovery can cross the corpus small-aperture firewall and feed a fixed positive Sonin operator without losing coefficients or source order.

## Gates

- [x] 0 → 1 in-progress: pre-divisor schedule uses only prime labels, logarithmic source weight, and one unit collar
- [x] 1 → 2 fully-proven: PNT gives fixed total action and vanishing quadratic phase; Sonin aperture continuity transports every trace moment
- [x] 2 → 3 formalized: Lean modules `GammaSewnSynchronizedRecoveryDiffusePrimeWard` and `FrankensteinDiffusePrimeSoninZerothMomentWeld`; direct checks, targeted leaf builds, and axiom audits pass
- [ ] 3 → 4 publication-ready: needs higher-moment frontier resolution

## Approach

Use aperture `τ/(N+1)` on primes below `N`. PNT gives total phase tending to `τ`, while local apertures and quadratic phase vanish. The recovery ratio tends to the strict factor `τ/(2 sinh(τ/2))`; its universal normalization restores the exact Xi-Ward tangent. The source-native effective Sonin aperture

`a_N = τ/(N+1) · (1 + Σ_{p<N} log p)`

is positive and tends to `τ`. Sonin Hilbert-Schmidt continuity then transports every intrinsic energy moment along `a_N`. Zeroth-moment surjectivity selects one `τ>0` for which the completed zeroth moment lands exactly, while every finite Sonin trace-Hankel quadratic stays nonnegative.

## Exact frontier

This is not RH. It closes local coefficient faithfulness, noncollapsing effective aperture, source positivity/order, and zeroth completed-moment normalization simultaneously. Remaining producer is exact equality

`soninAllPrimeEnergyMoment τ r = normalizedPrimeArchMoment r`

for every `r>0` at the same selected `τ`. Corpus compactness proves any full asymptotic weld must already be such an exact positive-aperture match, so changing schedules cannot bypass this higher-moment obstruction.

## Failed pivots and sharp survivors

- Directly using local aperture as Sonin aperture is impossible: every Sonin moment weld has a positive aperture floor.
- Ordinary normalization restores the Ward coefficient but removes finite-cutoff contraction; unnormalized recovery retains strict damping.
- Polarized two-boundary positivity is false off RH: mixed incidence converges to negative orientation energy.
- Fixed-vector Kōthe landing is impossible near a Xi zero; only dual/corona boundary carriers survive.
- Strong positive survivor: aggregate prime-log action, not local aperture, is the fixed Sonin coordinate.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/GammaSewnSynchronizedRecoveryDiffusePrimeWard.lean`
- `lake env lean GaloisForLFunctions/RHTower/FrankensteinDiffusePrimeSoninZerothMomentWeld.lean`
- `lake build GaloisForLFunctions.RHTower.FrankensteinDiffusePrimeSoninZerothMomentWeld`
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`
- Umbrella import wired; umbrella build intentionally not run.

## Log

- 2026-08-31 — diffuse PNT schedule, recovery tradeoff, effective Sonin aperture, and exact zeroth-moment weld formalized.
