# HB completed balanced spin-two external-leg no-go

- **ID:** HB-EXTLEG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RH frontier HB same-pole third-order burden
- **Statement:** Unamputated canonical completed balanced spin-two source vanishes on every Xi projecting leg, so arbitrary multiplicative radial/left response cannot cancel nonzero AIME.

## Goal
Kill canonical completed Plebanski--Maass vertex as full HB same-pole counterterm.

## Gates
- [x] 0 → 1: corpus source→projection chain fixed
- [x] 1 → 2: external `XiC(z)^2` zero gives dependency-closed proof
- [x] 2 → 3: `d4HBUnamputatedCompletedBalancedSpinTwoSourceRouteKilled`; targeted build and axioms audit pass
- [ ] 3 → 4: publication package

## No-go closure
- **Kill:** projecting parameter is `rho-1/2 = I*z`; completed vertex contains `XiC(z)^2=0`; nonzero AIME pole survives every multiplicative radial/left factor.
- **Survivor:** external-leg derivative/residue amputation, or non-factorizing source-to-left-QNM incidence.
- **Novelty audit:** corpus search found no prior external-leg theorem; primary-paper search found separate BM QNMs, AIME, QNM bilinear projection, and AdS4 Plebanski vertex, not this weld.
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMCompletedBalancedSpinTwoExternalLegNoGo.lean`; axioms only `propext`, `Classical.choice`, `Quot.sound`.
