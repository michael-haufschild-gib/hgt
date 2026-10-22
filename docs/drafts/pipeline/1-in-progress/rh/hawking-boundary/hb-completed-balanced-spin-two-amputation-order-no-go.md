# HB completed balanced spin-two amputation-order no-go

- **ID:** HB-AMP-ORDER
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RH frontier HB same-pole third-order burden; HB-EXTLEG survivor
- **Statement:** If projecting Xi zero has support multiplicity `m`, every derivative-amputated completed balanced spin-two source of grade `<2m` vanishes and cannot cancel nonzero AIME; grade `2m` is live exactly when explicit side factor is nonzero.

## Goal
Classify derivative external-leg amputation and kill all subcritical grades, including ordinary first-derivative LSZ.

## Gates
- [x] 0 → 1: corpus Xi-multiplicity and completed-vertex chain fixed
- [x] 1 → 2: product-jet proof gives exact `2m` threshold and side-factor survivor
- [x] 2 → 3: `d4HBDerivativeAmputatedCompletedBalancedSpinTwoSourceRouteKilled`; targeted build and axioms audit pass
- [ ] 3 → 4: publication package

## No-go closure
- **Kill:** completed projecting external leg occurs twice. Its square has exact zero order `2m`; arbitrary radial/left scale cannot revive any grade `<2m`, so opposite simple QNM AIME pole survives.
- **Survivor:** multiplicity-matched grade `2m`. Its vertex jet is nonzero iff `Bochner(u,v)·XiC(2u+v)·XiC(2u-v) ≠ 0`; remaining HB burden is literal radial/left-QNM incidence and equality of this normalized jet with `-AIME`.
- **Novelty audit:** corpus search found multiplicity/product-jet infrastructure but no completed balanced-vertex threshold; primary-paper search found no Xi-multiplicity/LSZ/HB weld.
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMCompletedBalancedSpinTwoAmputationOrderNoGo.lean`; build `12886/12886`; axioms only `propext`, `Classical.choice`, `Quot.sound`.
