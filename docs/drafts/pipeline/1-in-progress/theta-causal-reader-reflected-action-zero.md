# The causal square-rate reader annihilates the reflected theta half

- **ID:** theta-causal-reader-reflected-action-zero
- **Stage:** 1-in-progress
- **Type:** THEOREM / ROUTE NO-GO, `[NOVELTY UNVERIFIED]`
- **Date:** 2026-07-11
- **Statement:** In shifted heat coordinates, the reflected completed-theta half is supported on
  `(-1,0)`, so every causal square-rate reader has exactly zero reflected action.

## Goal

Compute the reflected completed-theta term consumed by the now-formalized causal reader.  Decide
whether it produces a nontrivial source-side sign or charge.  The claim is source-pure: it uses only
the completed theta split, the exact coordinate change `y = exp(u) - 1`, and the proved causal
support of the reader.

## Approach

1. Transport the reflected logarithmic half through `y = exp(u) - 1`.  Its domain `u < 0` becomes
   `-1 < y < 0`.
2. Pair that profile with `thetaHeatRateSourceReaderL2 n hn`.
3. Use `thetaHeatRateSourceReaderL2_hasAELowerSupport` to show the integrand vanishes almost
   everywhere.
4. Combine the exact zero with `xiThetaPositiveSourcePerronCharge_tendsto_zero` and the existing
   translation-coboundary theorem to decide the RH route.

## Gates

- [x] 0 → 1: exact support calculation isolated; no divisor or RH-equivalent hypothesis enters.
- [ ] 1 → 2: complete paper proof and route verdict.
- [ ] 2 → 3: Lean theorem, targeted build, axiom audit, and lint.
- [ ] 3 → 4: not expected; the result is a route obstruction rather than a publication claim.

## Log

- 2026-07-11 — created in progress after the report's proposed reflected-charge move was compared
  with the completed theta, causal-reader, Perron-source, and boundary-coboundary theorem surfaces.
