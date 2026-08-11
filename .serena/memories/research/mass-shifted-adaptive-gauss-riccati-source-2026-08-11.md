# Mass-shifted adaptive Gauss/Riccati arithmetic source (2026-08-11)

Route: `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, equations (9.3.427)–(9.3.435).

## Formalized findings

1. For current monic admission `P_n`, adaptive source `S_n=(XP_n)X(XP_n'+P_n)`, and current `(n+1)`-node Gaussian rule:
   `L(S_n)-Q_n(S_n)=(n+1)h_(n+1)`.
   Hence `Q_n(S_n)=h_n(E_n-(n+1)beta_(n+1))>0`.
2. Current Christoffel completion:
   `E_n/(16 beta_(n+1))=(n+1)/16+Q_n(S_n)/(16h_n beta_(n+1))`, positive bulk.
3. Cumulative current flux `F_n=2sum_(j<n)alpha_j+alpha_n`, dissipation `D_n`, and adaptive energy satisfy:
   `2E_n=D_n+alpha_n F_n+2n alpha_n^2`.
   Since `F_n'=-D_n`, literal source `A_n^sharp=2h_nE_n` gives
   `F_n'=alpha_nF_n+2nalpha_n^2-A_n^sharp/h_n`.
4. Weighted Cauchy:
   `F_n^2<(2n+1)D_n`, so `(2n+1)F_n'<-F_n^2`.
   With `U_n=F_n/(2n+1)`, universal degree-free contraction `U_n'<-U_n^2`.
5. Generic finite-time blow-down barrier proves a function satisfying this on a complete right ray is strictly positive. Fixed-block far-right shifted-Xi positivity therefore gives unconditional `U_n>0` throughout every fixed-degree terminal positive chamber, without a recession rate.

## Lean modules

- `HTGeometry.FiniteGaussQuadrature`
- `HTGeometry.AdaptiveOrthogonalSourceGaussDecomposition`
- `RHTower.XiShiftedCanonicalAdmissionGaussEdgeArithmeticSource`
- `RHTower.XiShiftedCanonicalAdmissionGaussRiccatiSource`

All wired into umbrellas. Direct Lean checks and targeted build pass. Axiom audit capstones: only `propext`, `Classical.choice`, `Quot.sound`. No computation.

## Open core

Current source, adaptive observer loss, current scale, and terminal current-flux sign are complete. Remaining obstruction is cross-degree/frozen-current admission compatibility: transport frozen crossing history against later current admission uniformly as degree changes, or prove adjacent-degree compatibility preventing cofinal shape holonomy. RH not proved.

Pipeline cards:
- `docs/drafts/pipeline/3-formalized/mass-shifted-adaptive-source-gauss-edge-decomposition.md`
- `docs/drafts/pipeline/3-formalized/mass-shifted-adaptive-source-riccati-flux-law.md`
