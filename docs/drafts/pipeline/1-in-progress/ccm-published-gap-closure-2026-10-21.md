# CCM published-result gap closure (from `docs/reports/ccm-comparison-us-vs-sota.md`)

- **ID:** `ccm-published-gap-closure-2026-10-21`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / FORMALIZATION PROGRAM
- **Source:** `docs/reports/ccm-comparison-us-vs-sota.md` §"Published results still lacking"; parent ledger
  `ccm-primary-literature-to-lean-parity.md`
- **Statement:** Close, unconditionally in Lean (no premises, no axioms, no computations), the four
  published CCM results the report could not locate end-to-end.

## Targets (report priority order) and plan

| # | Published result | Plan | Status |
|---|---|---|---|
| T2 | CCM 2023 Thm 4.6: `θ_S : Sonin_λ(ℝ) ≃ Sonin_λ(X_S)` for every finite `S`, Fourier compatible | `θ_S = w_S ∘ E_S`, `E_S = ∏_{p∈S}(1 − p^{-1/2}ϑ(p))` (Neumann-invertible, `‖p^{-1/2}ϑ(p)‖<1`); `E_S^{±1}` preserve `ran(1−P_λ)`; `F_S θ_S = θ_S F` ⇒ `Sonin_λ(X_S) = θ_S(Sonin_λ(ℝ))` | **Lean-closed** (`FieldOneFiniteStageThetaSoninIsomorphism`); finite-S Hardy–Titchmarsh square still to add (T2b) |
| T4 | CCM 2023 Thm 5.2(iv): Jacobi/Gamma data = even metaplectic representation | build sl₂ operators from Jacobi coefficients, identify on even Hermite basis | open |
| T3 | CCM 2025 Thm 5.10: `D_log^{(λ,N)}` self-adjoint, `det_reg(D_log − z) = −i λ^{−iz} ξ̂(z)` | finite-rank perturbation of `diag(2πn/L)`; define regularized determinant explicitly; no simple-even premise laundering | open |
| T1 | CC 2020 Thm 1: `W_∞(g∗g*) ≥ Tr(ϑ(g)Sϑ(g)*)`, supp `g ⊆ [2^{-1/2},2^{1/2}]`, `ĝ(i/2)=ĝ(0)=0` | `1−P−P̂ = S + D`, `D = P∨P̂ − P − P̂` trace class; prove `Tr(ϑ(g)Dϑ(g)*) ≥ 0` analytically (paper uses numerics) | open |

## Gates
- [x] 0 → 1  in-progress: targets identified, attack per target sketched
- [ ] 2 → 3  formalized: each target's Lean theorem, `lake env lean` clean, axioms audited, wired

## Log
- 2026-10-21 — created; corpus survey: T2 has literal `X_S`, `F_S`, Def. 4.5 Sonin space
  (`FieldOneFiniteStageClassSonin`), θ-core/Euler identification; missing the isomorphism theorem.
- 2026-10-21 — T2 closed: `fieldOneFiniteStageSoninThetaEquiv S λ : Sonin_λ(ℝ) ≃L[ℂ] Sonin_λ(X_S)`,
  `fieldOneFiniteStageSemilocalSonin_eq_map_literalTheta`, whole-L² Fourier compatibility
  `fieldOneFiniteStageClassFourierUnitary_literalTheta`. Mechanism: `w_∞`, `w_S` carry both cutoffs to
  `1_{u≤λ}` (split point of `(k,u)` has module `u`); `1 − p^{-1/2}U_p^*` maps the closed vanishing
  space onto itself (restricted Neumann unit). Direct `lake env lean` clean; axioms
  `propext, Classical.choice, Quot.sound`; wired into `RHTower.lean`; olean built single-threaded.
  Open: T2b = finite-S dual Hardy–Titchmarsh square `υ_S ∘ E_S = ι'_S ∘ υ_∞` (one-prime case exists in
  `HardyTitchmarshSemilocalSquare`).
