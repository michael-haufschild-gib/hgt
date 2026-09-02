# HB full Jost-divisor spectral no-go

- **ID:** HB-JOST-DIV-SPEC-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM · HB ROUTE-CLASS KILL
- **Source:** `rh-current-frontier-map.md` · HB literal full third-order same-pole projection
- **Statement:** Full BM radial Jost divisor is exactly two strictly damped QNM towers; no arbitrary complex finite-variation causal spectrum supported there supplies persistent `-AIME`.

## Goal
Kill every meromorphic radial pole-supported completion of HB same-pole remainder. Remaining producer must use non-polar peripheral/threshold singular support or leave finite variation.

## Gates
- [x] 0 → 1 in-progress: exact Jost functions and arbitrary-spectrum no-go already Lean-closed; converse divisor classification is missing
- [x] 1 → 2 fully-proven: reciprocal-Gamma zero classification, affine branch solution, damping, dominated-convergence weld
- [x] 2 → 3 formalized: direct Lean and targeted leaf build green
- [ ] 3 → 4 publication-ready: standalone theorem/proof/certificate

## Approach
Classify reciprocal-Gamma zeros by nonpositive integers; solve two affine radial equations to obtain exactly `QNMPlus` or `QNMMinus`; use existing strict damping on Xi fibres; feed a.e. Jost support into arbitrary finite-variation causal spectral decay.

## Novelty audit
Birmingham--Mokhtari (2006, 2007) derive exact hypergeometric QNM frequencies and stability. Sberna et al. (2022) study AIME; Green et al. (2024) study QNM bilinear projection. Search through 2026-08 found no converse full-Jost-divisor plus arbitrary-measure AIME/RH no-go weld. Frequency formula itself is not claimed novel.

## Certificate
`d4HBFullJostDivisorFiniteVariationAIMECountertermRouteKilled` in
`ThetaCuspHawkingBMFullJostDivisorSpectralNoGo.lean`; direct Lean PASS; targeted build
`12185/12185` PASS; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired.
