# T2 adaptive cubic energy supercritical no-go (2026-08-30)

Formalized new T2 result.

Module:
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalAdaptiveCubicEnergyNoGo.lean`

Card:
`docs/drafts/pipeline/3-formalized/t2-adaptive-cubic-energy-supercritical-no-go.md`

Main theorems:
- `exists_woldNatResidual_power_rate_twoThirds_of_squareEnergy`: for `1/2<t<3/2`, `WoldNatResidualSquareEnergy t` gives exact eventual rate `|R_N| ≤ B N^{-2t/3}`.
- `woldNatResidualSquareEnergy_mono`: energy downward monotonicity for positive-weight radii.
- `not_woldNatResidualSquareEnergy_of_threeQuarter_lt`: unconditional closed theorem `3/4<t → ¬WoldNatResidualSquareEnergy t`.

New math: adaptive radius `H_N=ceil(N^(1-2t/3))` balances finite Cauchy averaging and Wold logarithmic persistence drift. Exact endpoint rate follows with no epsilon loss. For arbitrary `t>3/4`, lower to `u=(3/4+min(t,1))/2`; transport rate `2u/3>1/2` to ordered prime-log height and contradict closed half-density obstruction.

Verification:
- direct `lake env lean`: PASS
- targeted `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAdaptiveCubicEnergyNoGo`: PASS
- axioms: `[propext, Classical.choice, Quot.sound]`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- global lint: new module reachable/clean; unrelated concurrent unreachable-module failures remain.

Frontier map untouched. No computations used.