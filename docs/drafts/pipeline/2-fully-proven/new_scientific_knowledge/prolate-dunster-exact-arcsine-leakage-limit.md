# Exact prolate density converges to the arcsine leakage law

- **ID:** prolate-dunster-exact-arcsine-leakage-limit
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean source-checked)
- **Source:** Frankenstein corpus synthesis: Prolate Dunster transfer + CCM radial leakage
- **Statement:** Every endpoint-normalized exact radial prolate family with `c -> +infinity` and `s -> 0` has exterior tail mass converging to the positive arcsine leakage tail.

## Goal
Compose the corpus's global exact-to-Bessel `L1` estimate with its Bessel weak limit and identify the result with the independently constructed CCM radial leakage measure. This creates a literal positive cross-route carrier, without assuming RH or a zero-location statement.

## Gates
- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: final exact-module `lake build` intentionally deferred to dependency-closed RH audit
- [ ] 3 -> 4 publication-ready: standalone paper + novelty audit

## Approach
For fixed `a > 1`, the matching point `1 + 9/(8c^2)` is eventually below `a`. The existing exact-to-Bessel estimate bounds the tail `L1` distance by `2C/c`, hence by zero in the limit. The existing Bessel theorem converges to `integral_(a,infinity) profileDensity`; `profileDensity = radialLeakageDensity / pi`. Triangle inequality gives the exact limit.

## Paper proof `[PROVED HERE]`
Let `B_i` be the regular Bessel density and `E_i` the exact prolate density. Since `c_i -> +infinity`, the Dunster matching point tends to `1`, so it lies below every fixed `a > 1` eventually. The global transfer theorem gives

`integral_(a,infinity) |E_i - B_i| <= 2 C / c_i -> 0`.

The Bessel weak-limit theorem gives

`integral_(a,infinity) B_i -> integral_(a,infinity) profileDensity`.

The integral triangle inequality therefore gives the same limit for `E_i`. The independent CCM identity `profileDensity(x) = radialLeakageDensity(x) / pi` identifies the limit with the normalized CCM leakage tail. No RH, zero-location, spectral-sign, or numerical premise occurs.

## No-go closure
- **Exact killing theorem/mechanism:** The leading weak limit is universal: it depends only on `c -> infinity`, `s -> 0`, endpoint normalization, and the radial ODE. It contains no Xi-divisor coordinate. Any attempt to infer RH directly from its positivity erases precisely the finite-bandwidth normal data that could distinguish zero locations.
- **Strongest positive survivor:** Exact prolate and CCM leakage carriers share a literal positive asymptotic measure. Any RH-facing continuation must retain a signed, renormalized finite-bandwidth defect relative to this common positive background.
- **New insight:** Reinterpret leakage as background state and divisor information as transverse defect. This avoids asking a universal positive limit to perform spectral selection.
- **Status:** Paper dependency closed. Lean theorem `tendsto_integral_Ioi_radialProlateDensity_to_ccmLeakage` in `ProlateCCMArcsineWeakLimit.lean`; exact-file source check passes; axiom audit `[propext, Classical.choice, Quot.sound]`. Final module build deferred by research build discipline.

## Log
- 2026-08-07 — C9 degree-tail conjecture falsified as an exact RH equivalent. C10 originated from newly added corpus modules.
- 2026-08-07 — Concurrent corpus addition supplied exact prolate weak limit; added missing direct CCM leakage identification and completed hostile audit.
