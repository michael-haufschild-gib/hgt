# Horizontally simple zeros beyond 0.5087 via the off-line moment tradeoff

- **ID:** HS-TRADEOFF
- **Stage:** 1-in-progress
- **Type:** PARTIAL PRODUCER (route WD, density version of ordinate injectivity)
- **Parent:** `rh-goal-loop-opus-2026-09-29.md` cycles 109–110; source idea `1-in-progress/horizontal-lamzouri-inequality-loop.md` (H3 "Zeta tradeoff", paper)
- **Target:** `liminf (#singleton fibres up to T)/N(T) ≥ HD(1) − κ'·λ·2π·μ − ε`. Here `μ = limsup Σ(β−½)⁺/T` (corpus `0.21`, MUST via `ZetaOffLineMomentExplicit`) and `κ' = sup_x (1 − 2K(x)²/B(x))⁺/x` for the actual Zeta23 window. Expected `≈ 0.6725 − 0.045 ≈ 0.63` cumulatively, or `≈ 0.58` from dyadic `0.42T`. The corpus now has `0.5087` (`(3HD1−1)/2`).

## Mechanism (paper, checked)
- Mixed point `x` (a simple on-line zero sharing its ordinate with an off-line pair at displacement `ε`):
  - Its packet cost is `≥ 2K²/B − 1`, with `K = ∫φ²cosh(εu)/∫φ²` and `B = ∫φ²cosh²(εu)/∫φ²`. This is exact by sampled Parseval and the overlap criterion (`lens_overlap_cost_ge` with `C = I₀I₂/J²`).
  - Abstract inequality (`four_mass_sub_energy_le`): `#H ≥ seam − Σ_M (1 − 2K²/B)⁺`.
- Window:
  - `φ_D² = cos(√2λu/L)·taper²`.
  - Scale-free sharp profile `cos(cs)` on `[−½,½]`, `c = √2λ`.
  - `K(x) = (2r x sinh(x/2) + c² cosh(x/2))/(x²+c²)` with `r = (c/2)cot(c/2) ≈ 0.8275`.
  - `B = (1 + K(2x))/2`.
  - Deficit `d(x) = 1 − 4K(x)²/(1+K(2x))`, about `1 − 8r/x` for large `x`. Numerically `sup d/x ≈ 0.034` near `x ≈ 15`.
  - The taper costs `O(xw/L) → 0`.
- Loss: `Σ_M d(ε_x λL) ≤ κ' λ L Σ_{pairs} b ≤ κ'λ·2π·μ·N`.

## Bricks
1. `absorbed_block_count_deficit`: block count with per-mixed-point deficits (no sign hypothesis).
2. Exact window ratio: cost `≥ 2J²/(I₀I₂) − 1` (variant of `lens_overlap_cost_ge`).
3. Window integrals for `φ_D`: lower bound `2J²/(I₀I₂) ≥ (1 − δ_T)·R(εL)`.
4. Explicit inequality `1 − R(x) ≤ κ'x`, `x ≥ 0`, with `κ' = 1/25` (slack over 0.034).
5. Assembly: seam with deficits, `Σ b` via the off-line moment, Zeta23 endgame (`thmD_count_of_seam`), dyadic → cumulative.

## Log
- 2026-10-01 — card opened; brick 1 started.
- 2026-10-01 — bricks 1–4 compile (`lake env lean`, no warnings):
  - `HorizontalSimplicityDeficitCount`
  - `HorizontalShiftOverlapExact` (`shift_overlap_cost_exact`)
  - `HorizontalTradeoffHyperbolicBounds` (`deficit_le`, `window_constant_ge`, Padé `tanh`)
  - `HorizontalTradeoffWindowDeficit` (`phiD_window_deficit_le`: `1 − 2J²/(I₀I₂) ≤ εL/12 + 20w/L`)
  - Crude `κ' = 1/12`: flat comparison, window constant `θcos²θ/sinθ ≥ 3/5`. Projected cumulative constant `HD(1) − 2π·0.21/12 = HD(1) − 7π/200 ≈ 0.5625` (> 0.5087).
- 2026-10-01 — brick 5a/5b compile:
  - `HorizontalSimplicityDeficitSeam` (`seam_horizontal_deficit`, `offMoment`, `overlapRatio`)
  - `HorizontalSimplicityDeficitThmD` (`thmD_horizontal_deficit_lam_abstract`)
  - Remaining: ζ instance, weighted moment `W(a,b) = Σ(β−½)l⁺(γ)` (additive), dyadic → cumulative (`Assembly.dyadic`), `λ → 1` (`eps_form_HD`), corpus moment `0.21T`, RvM `T l(T) ≤ (2π+ε)N(T)`, singleton-fibre bridge.
- 2026-10-01 — **CLOSED in Lean (MUST-634).** `horizontalSingleton_density_tradeoff : HD 1 − 7π/200 ≤ liminf xiSingletonFiberRatio`, about 0.5625.
  - Modules: `HorizontalSimplicityWindowSums` (additive `logMoment`, `NisoH_add`) and `HorizontalSimplicityTradeoffDensity` (dyadic block bound, `Assembly.dyadic`, `eps_form_HD`, `ξ` bridges).
  - All eight modules are wired after `HorizontallyIsolatedSimpleZeros`. Collision sweep: 0 collisions (`sinh_le_mul_cosh` is reused from `CothInfra`). Axioms are standard.
  - Next lever: sharpen `κ'`. The crude flat comparison loses the factor `cos θ` in `I₂` and is lossy in `deficit_le`. The exact window gives `κ' ≈ 0.034`, i.e. density ≈ `0.6725 − 0.045 = 0.63`.
- 2026-10-01 — **Sharpened to `HD(1) − 7π/400 ≈ 0.6175` (MUST-636).**
  - `window_weight_comparison` keeps the factor `cos θ` in `I₂`, so the window constant is `θcotθ ≥ 4/5`.
  - `deficit_sharp` (`κ = 1/24`) uses Padé on `[0,5]` and `eʸ ≥ y⁴/24` on `[5,24]`.
  - Side condition: `L ≥ 24 w e²⁵`, which holds eventually.
  - The seam takes a general slope `κ`. Crude `κ = 1/12` modules were replaced, not kept. Axioms are standard; collisions 0.
  - Remaining window slack: `1/24` against the numerical `≈ 0.038` of the exact window, worth ≤ 0.005. Further gains need the off-line moment constant.
