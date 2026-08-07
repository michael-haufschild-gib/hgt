# Exact prolate density converges to the arcsine leakage law

- **ID:** prolate-dunster-exact-arcsine-leakage-limit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Frankenstein corpus synthesis: Prolate Dunster transfer + CCM radial leakage
- **Statement:** Every endpoint-normalized exact radial prolate family with `c -> +infinity` and `s -> 0` has exterior tail mass converging to the positive arcsine leakage tail.

## Goal
Compose the corpus's global exact-to-Bessel `L1` estimate with its Bessel weak limit and identify the result with the independently constructed CCM radial leakage measure. This creates a literal positive cross-route carrier, without assuming RH or a zero-location statement.

## Gates
- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem, exact-file source check, axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper + novelty audit

## Approach
For fixed `a > 1`, the matching point `1 + 9/(8c^2)` is eventually below `a`. The existing exact-to-Bessel estimate bounds the tail `L1` distance by `2C/c`, hence by zero in the limit. The existing Bessel theorem converges to `integral_(a,infinity) profileDensity`; `profileDensity = radialLeakageDensity / pi`. Triangle inequality gives the exact limit.

## No-go closure
- **Exact killing theorem/mechanism:** Pending hostile audit after construction.
- **Strongest positive survivor:** Pending.
- **New insight:** Potential positive measure shared by prolate and CCM carriers.
- **Status:** Paper proof and Lean composition in progress.

## Log
- 2026-08-07 — C9 degree-tail conjecture falsified as an exact RH equivalent. C10 originated from newly added corpus modules.
