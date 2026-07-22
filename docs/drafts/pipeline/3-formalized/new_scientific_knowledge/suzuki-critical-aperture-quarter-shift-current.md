# Suzuki critical aperture quarter-shift current — formalized core certificate

## Status

`[LEAN-PROVED CORE] [UNCONDITIONAL] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`

## Paper source

`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-critical-aperture-quarter-shift-current.md`

## Lean source

`formal/GaloisForLFunctions/RHTower/SuzukiCriticalApertureQuarterShiftCurrent.lean`

## Formal theorem surface

- `suzukiCriticalApertureBoundaryAtom_succ`: actual Gamma-boundary/innovation atom has exact fixed
  quarter-shift depth ratio.
- `norm_suzukiCriticalApertureDepthRatio_lt_one`: positive aperture makes ratio strictly
  contractive.
- `suzukiCriticalApertureBoundaryAtom_eq_base_mul_ratio_pow`: exact geometric depth law.
- `summable_suzukiCriticalApertureBoundaryAtom`: valuation-depth current is summable.
- `tsum_suzukiCriticalApertureBoundaryAtom_eq_resolvent`: exact source resolvent `T_0/(1-rho)`.

## Scientific result

Critical Gamma boundary is not a standalone Hilbert vector, but actual source pairing with
true-aperture innovation completes exactly as contractive quarter-shift resolvent.  This supplies
first corpus-native power-scale critical mechanism and fixes Gamma/aperture subchannel of marked
Weil--Robin frontier.

Absolute completion over primes is paper-proved and remains Lean gate; certificate claims exact
per-prime depth core only.  RH is not claimed proved.

## Verification

- Direct Lean check passed.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or RH premise.
- Forbidden-token scan: clean.
- Final targeted build passed:
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` (`9450/9450`).
- Repository lint reached module but remains red on six unrelated concurrent unreachable modules.
