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
- 2026-10-01 — **Moment `0.21 → 0.17`; density `HD(1) − 17π/1200 ≈ 0.628` (MUST-638).**
  - `Sieve/TwistedSelbergMollifier`: Selberg `Λ²` weights for density `n^{−s}` (PNT+ `SelbergSieve`, no new sieve code), `gcdPowKernel_mono`, gcd form `≤ 1/Σ m^{−s}`.
  - `ZetaGateProductAFEWeightedHighBlock`: weight-generic high block and dyadic law (any real `|w| ≤ 1`, `N ≤ U^{1/15}`, main-term factor `F → c`).
  - `ZetaOffLineMomentSelbergWeights`: `s = 1 + 2R/log(U−1)`, constant `e^{2R}/(1−e^{−2R/15})`, `R = 5/2`, `μ ≤ 17/100`.
  - `horizontalSingleton_density_of_moment`: density `HD(1) − πμ/12` for any moment `μ ≤ 1`.
  - Cap at `θ = 1/15`: `μ ≈ 1/6`. Next lever is the mollifier length, not the weights.
- 2026-10-01 — All moment consumers parametrized by `μ` (`…_of_moment` in `XiLaguerreShadowDensity`, `XiSliceCoeffDensity`, `XiHadamardSignDensity`, `XiCriticalScaleDiscSeamExplicitDensity`, `SpeiserEventualEquivalence`, `SpeiserCleanHeights`); `0.21` versions kept as instances. `ZetaOffLineMomentSelbergDensities`: `μ = 17/100` gives `33/50` (Laguerre, slice, Speiser), `33/100` (Hadamard area), `49/100` (disc seams). Dependents rebuilt; collisions 0; axioms standard.
- 2026-10-01 — **Critical-scale tail law (MUST-641).** `ZetaCriticalScaleTailFromGate`: wide Littlewood consumer (left zeros charged), reflection identity, `4πΣ(β−½−R/log V)⁺ ≤ (log c − 2R + η)V` from any gate. `ZetaCriticalScaleTailSelberg`: `g(R) = −log(1−e^{−2R/15})`, zero count beyond `2R/log V` `≤ (g+η)V log V/(4πR)`, bad critical-scale discs `≤ (3K+4)(g+η)/(2π)`.
- 2026-10-01 — **Mollifier length `U^{1/9}` (MUST-644): `μ ≤ 7/50`, singleton `≥ HD(1) − 7π/600 ≈ 0.636`.** Deep left-line shift to `Re w = −9/20`, pair error `u^{−33}` for `N ≤ u^{13}`, high blocks `a ≥ U^{7/8}`, `‖Ψ‖² ≤ 9e^{4R/9}N` in the middle/low ranges. Tail consequences refactored to `…_of_tail` (any tail law). Note: `RHTower.integrable_mul_cexp` is declared in three other agents' modules (`IsolatedDeepZeroHodgeIndex`, `WindowTransformSamplingParseval`, `WeilFullConeHerglotzRightHalfPlane`), so the singleton consequence lives in its own module `HorizontalSingletonDensityNinth`.
