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
| A25 | Physical all-`n` Hecke moments | done | `ResonantStates/EveryHeckeOperatorIsDiagonalOnEisenstein`, `ResonantStates/TheHeckeAlgebraHasThePoissonSpectralMeasure`; card `3-formalized/pm-every-hecke-operator-has-the-poisson-spectral-measure.md` |
| A26 | Weyl law; metric of `L²` data; regularity at `r=1`; scalar sector | regularity at `r=1` done; rest open | `BlackHoleRingdown/TheMetricOfAPulseIsRegularAcrossTheHorizon`; card `3-formalized/bhr-pulse-metric-regular-across-the-horizon.md` |
| A27 | Local AdS₄ isometry; modular Lax–Phillips; Zagier–Sarnak; Kramers–Kronig | AdS₄ quotient done; KK already in corpus (`TheScatteringMatrixIsABlaschkeProduct`: inner = Blaschke, no outer/singular factor); Lax–Phillips, Zagier–Sarnak open | `BlackHoleRingdown/TheModularBlackHoleIsAQuotientOfAntiDeSitter`; card `3-formalized/bhr-modular-black-hole-is-a-quotient-of-anti-de-sitter.md` |
| A28 | Reciprocal quadric traces = vanishing-cycle traces | Lean side in corpus (`reciprocalQuadric_card_even_extension`); identification needs ℓ-adic vanishing cycles (SGA7), absent from Mathlib | — |
| A29 | Mixed Young projections at small rank | done at rank ≤ 4 | `ArithmeticCastelnuovoSeveri/Representation/MixedYoungProjectionsAtSmallRank`; card `3-formalized/acs-mixed-young-projections-at-small-rank.md` |
| A30 | Best stencil exponent under RH | open (research): rate = LP value with extremal fake prime measure dual; a `T^{1/2+ε}` sawtooth bound gives only `1/3` | — |
| A31 | Discrete Beurling one-off and FE defect | done | `ArithmeticPositiveDuality/ADiscreteBeurlingOneOff`; card `3-formalized/apd-a-discrete-beurling-one-off.md` |
| A32 | Manin at higher genus | open (research): true curves need Jacobian heights over `F_q(T)`; the graph test is decided (slow resonance for `q ≥ 4`, `universal_damping_not_forced_at_genus_two`) | — |
| A33 | Cubic residue `R≠0`, cubic theta, Gauss-sum coefficients | owned by outside agent; `TheCubicResidueIsNonzero` landed | — |

## A27 Zagier–Sarnak plan
`h ∈ C_c(ℍ)`, `f = Σ_{γ∈SL₂ℤ} h∘γ`, `A_h(y) = ∫₀¹ f(x+iy)dx`, `R_h(s) = ∫_ℍ h E(·,s) dμ`.
1. Unfolding, `Re s > 1`: `∫₀^∞ A_h(y) y^{s−2} dy = 2R_h(s)`: split `Σ_{γ}` over `Γ/Γ_∞ × ℤ`, assemble the strips `Tⁿ(strip)` into `ℍ`, substitute `w = γ₀z`, invert cosets. No fundamental domain needed.
2. `R*_h(s) = ∫ h E*(·,s)`, `E* = Λ(2s)E`, holomorphic on `Re s > 1/4` minus `{1}`.
3. Converse: if `A_h(y) = c + O(y^{3/4−ε})` then `M(s) = ∫₀^{Y₀}(A_h − c)y^{s−2}` is holomorphic on `Re s > 1/4+ε`, `R*_h = Λ(2s)(M + cY₀^{s−1}/(s−1))/2` on `Re s > 1`, hence on the connected set `Re s > 1/4+ε, s≠1`; at `s₀ = ρ/2` the right side vanishes. `E*(·,s₀) ≢ 0` (constant term `Λ(2−2s₀)y^{1−s₀} ≠ 0`), so some `h` has `R*_h(s₀) ≠ 0`: contradiction unless `Re ρ ≤ 1/2`.
4. Forward (RH ⇒ rate): Mellin inversion and shift to `Re s = 1/4+ε`; needs rapid decay of `R*_h` (Δ-symmetry) and `1/ζ(2s) ≪ |t|^ε` under RH.

## A25 plan
Classical `T_n F(x,y) = n^{-1/2} Σ_{ad=n} Σ_{b<d} F((ax+b)/d, ay/d)`. On `1`-periodic `F`: `T_{mn}=T_mT_n` for coprime `m,n` (CRT on `a′b+db′`), `T_pT_{p^k}=T_{p^{k+1}}+T_{p^{k−1}}`. Induction from `heckeOp_cuspLeg` gives `T_nE_u=W_u(n)E_u`. At a resonance the constant term is one Weyl power, so `T_n Λ^Y E_u = Σ_{ad=n}(d/a)^u Λ^{Yd/a}E_u`, a sum of translations of the stationary cutoff family; the Poisson Gram kernel gives `⟨T_n t_Y, T_m t_Y⟩ = ‖t_Y‖² ∫ P_{−Re u}(t−Im u) W_{it}(n) W_{it}(m) dt` and `⟨T_n t_Y,t_Y⟩ = μ_n(u)‖t_Y‖²` for `Y ≥ n`.

## Log
- 2026-11-07 — created; survey of A25–A33 done.
