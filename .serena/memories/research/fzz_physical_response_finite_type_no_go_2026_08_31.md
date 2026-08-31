# FZZ physical-response finite-type no-go (2026-08-31)

Qualifying route-class kill for FZZ-P. Corpus-driven conjecture proved and formalized: canonical pole-filled Schwarzschild response `P(z)=regularizedRiemannZeta(z+2)` has no finite exponential type.

Lean module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildPhysicalResponseFiniteTypeNoGo`.
Closed capstone: `RHTower.fzz_regularFiniteTypePhysicalResponse_route_noGo`.

Core new theorem chain:
- `analyticOrderAt_blackHolePoleFilledJetInterpolation_shift_eq_xi`: for each Xi divisor point in `0<Re rho<1`, `ord_(rho-2) P = ord_rho xi`.
- `xiZeroCount_le_blackHolePoleFilledJetInterpolation_shiftedDivisor`: full multiplicity transfer gives `xiZeroCount T <= divisorMass(P, closedBall 0 (T+2))`.
- Riemann--von Mangoldt lower growth `T log T` contradicts linear divisor mass for finite-exponential-type nonzero entire functions.
- Existing all-order entire interpolation is also nonunique for every scale convention.

Exact scope: kills regular finite-exponential-type physical-response selection branch, not maximal order-one `exp(O(r log r))`, singular/non-entire responses, or source-deformed categories. Positive survivor: any regular category containing physical response must allow at least Xi divisor density, hence cannot impose finite exponential type.

Verification: `lake env lean` passed; targeted `lake build ...PhysicalResponseFiniteTypeNoGo` passed 11016/11016; axiom audit only `propext`, `Classical.choice`, `Quot.sound`. Global formal lint only reported unrelated concurrent unwired modules; new module is wired in `RHTower.lean`.

Docs: `docs/drafts/pipeline/3-formalized/fzz-physical-response-finite-type-no-go.md`; failed card `docs/drafts/pipeline/5-failed/fzz-regular-finite-exponential-type-response-selection.md`.