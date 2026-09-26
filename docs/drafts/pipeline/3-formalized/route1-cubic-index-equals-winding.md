# Route 1 core identity: cubic relative index of a smooth phase equals its winding number

- **ID:** route1-cubic-index-winding
- **Stage:** 3-formalized
- **Type:** THEOREM [L] (classical: Gohberg–Krein / Fedosov); no novelty claim
- **Source:** route1.md program steps 1 and 3; ledger F438–F440 (`Tr T_D = |wind u_D|`, [P]); frontier TG
- **Statement:** For a smooth unimodular `u : S¹ → S¹`, with `P` the Hardy projection on `L²(S¹)` and `U = M_u`, the pair `(U†PU, P)` has Hilbert–Schmidt displacement and cubic trace `Tr(U†PU − P)³ = −wind(u)`. The sign is fixed by the monomial case.

## Why (route 1)
The route's integer is the relative index of the boundary-phase projections. With this theorem and the argument principle, `Tr T_(D,x) = N(D)` (zeros of ξ in `D`) becomes [L], and the corpus's operator-norm criterion (`RestrictedUnitaryDatum.relativeIndex_eq_zero_of_seams`) applies to the actual phases.

## Plan (modules)
1. `CircleHardyRestrictedUnitary`: the Hardy projection on `Lp ℂ 2 haarAddCircle` via `fourierBasis`; the multiplication unitary `M_u` for a continuous unimodular `u`; Fourier matrix entries `⟨e_n, M_u e_k⟩ = û(n−k)`; Hilbert–Schmidt commutator when `Σ|j||û_j|² < ∞` (implied by `C¹`).
2. `CircleMonomialCubicIndex`: `u = z^m` gives index `−m` (or `m`, by convention).
3. `CircleCubicIndexHomotopy`: continuity in `t` for `u_t = z^m e^{itψ}`, via corpus `traceNorm_restrictedUnitaryCubicDefect_tendsto`; the integer-valued index is constant on `[0,1]`.
4. `CircleCubicIndexWinding`: the lift `u = z^m e^{iψ}`, so index = −wind.
5. `CircleArgumentPrincipleIndex`: for `F` holomorphic near a closed disc, nonzero on the circle, the index of `F/|F|` equals −(zeros inside).

## Log
- 2026-09-26 — card opened; starting module 1.
- 2026-09-26 — closed [L]. The plan changed: the corpus trace cocycle (`opTrace_ccmCircleMultiplier_mul_quantizedDifferential`) made the monomial/homotopy modules unnecessary. Three modules, all wired in `RHTower.lean`, `lake build --old` green, axioms `[propext, Classical.choice, Quot.sound]`:
  1. `RHTower.CircleHardyPhaseTraceIndex`.
     - `opTrace_restrictedProjectionDisplacement_eq_relativeIndex`: for projections with trace-class displacement `D`, `Tr D = Tr D³ = ind`, by `Tr(DC²) = −Tr(DC²)`.
     - `CCMCirclePhase.datum`: Hardy projection plus phase multiplier as a `RestrictedUnitaryDatum`.
     - `relativeIndex_eq_windingMoment`: `ind(U†PU, P) = Σ_{k≥1} k|û_k|² − Σ_{k≥1} k|û_{−k}|²`, for `Σ|k||û_k| < ∞`.
  2. `RHTower.CirclePhaseFourierMomentIntegral`.
     - `fourierCoeff_circleLift_deriv`: `\hat{f'}(n) = 2πin \hat f(n)`.
     - Parseval: `tsum_conj_fourierCoeff_mul_fourierCoeff`.
     - A C² periodic unimodular function is a `CCMCirclePhase` (first moments summable via Parseval for `f''`).
     - `relativeIndex_toPhase_eq_integral`: `ind = (2πi)⁻¹ ∫₀¹ f̄ f'`.
  3. `RHTower.CircleArgumentPhaseRelativeIndex`.
     - `DiscArgumentDatum.relativeIndex_eq_zeroCount`: `F` holomorphic near `closedBall c R`, zero-free on `|z−c| = t < R`, `U = M_{F/|F|}` on the circle. Then `ind(U†PU, P) = Σ_{ρ inside} ord_ρ F`.
     - `opTrace_cubicDefect_eq_zeroCount`: `Tr(U†PU − P)³ = N`.
     - The Toeplitz compression `P M_u P` has index `−N` (corpus `index_compressionPMap_eq_neg_relativeIndex`).
- Consequence for route 1: the integer identity `Tr T = N(D)` is [L] for every holomorphic boundary phase. What remains of route 1 is the budget alone, i.e. the seam bound `‖(1−P)U†P‖ < 1` (corpus `relativeIndex_eq_zero_of_seams`). For `F = ξ` on a strict-right circle this is RH on that disc (step 2 ⇔ RH [L]).
