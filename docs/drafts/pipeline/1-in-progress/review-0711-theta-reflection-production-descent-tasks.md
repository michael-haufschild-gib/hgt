# Review-0711 §2.1 — theta, reflection, weights, production, descent (A25–A33)

- **ID:** review-0711-a25-a33
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per task
- **Source:** `docs/reports/review-0711/obstacles-summary.md` §2.1, last table; `route-obstacles.md` S6, S7, S10.
- **Statement:** solve and formalize unconditionally each task A25–A33, easiest first.

## Ownership
- A33 (cubic residue at `4/3`): an outside agent is compiling `MetaplecticMobiusDescent/` cubic files and a scratch `hgt-cubic-nonzero-residue.lean` (2026-11-07 13:44). Do not touch MMD until that work stops.
- Peers: hgt-52 holds A9–A14, hgt-53 holds A15–A24 and A34, hgt-c6 holds A1–A8.

## Status
| # | Task | Status | Lean |
|---|---|---|---|
| A25 | Physical all-`n` Hecke moments | in progress | — |
| A26 | Weyl law; metric of `L²` data; regularity at `r=1`; scalar sector | open | — |
| A27 | Local AdS₄ isometry; modular Lax–Phillips; Zagier–Sarnak; Kramers–Kronig | open | — |
| A28 | Reciprocal quadric traces = vanishing-cycle traces | open | — |
| A29 | Mixed Young projections at small rank | open | — |
| A30 | Best stencil exponent under RH | open | — |
| A31 | Discrete Beurling one-off and FE defect | open | — |
| A32 | Manin at higher genus | open | — |
| A33 | Cubic residue `R≠0`, cubic theta, Gauss-sum coefficients | owned elsewhere | — |

## A25 plan
Classical `T_n F(x,y) = n^{-1/2} Σ_{ad=n} Σ_{b<d} F((ax+b)/d, ay/d)`. On `1`-periodic `F`: `T_{mn}=T_mT_n` for coprime `m,n` (CRT on `a′b+db′`), `T_pT_{p^k}=T_{p^{k+1}}+T_{p^{k−1}}`. Induction from `heckeOp_cuspLeg` gives `T_nE_u=W_u(n)E_u`. At a resonance the constant term is one Weyl power, so `T_n Λ^Y E_u = Σ_{ad=n}(d/a)^u Λ^{Yd/a}E_u`, a sum of translations of the stationary cutoff family; the Poisson Gram kernel gives `⟨T_n t_Y, T_m t_Y⟩ = ‖t_Y‖² ∫ P_{−Re u}(t−Im u) W_{it}(n) W_{it}(m) dt` and `⟨T_n t_Y,t_Y⟩ = μ_n(u)‖t_Y‖²` for `Y ≥ n`.

## Log
- 2026-11-07 — created; survey of A25–A33 done.
