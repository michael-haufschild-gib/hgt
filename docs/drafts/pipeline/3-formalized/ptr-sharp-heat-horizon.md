# Sharp heat-producer horizon (PTR Euler-horizon producer)

- **ID:** ptr-sharp-heat-horizon
- **Stage:** 3-formalized
- **Type:** THEOREM (paper sketch → Lean programme); positive survivor of opus loop rows 181/193, PTR rows 73–74
- **Statement:** For every `ε > 0` there is `X₀` such that for all `0 < t ≤ 1/8`, every zero `z` of the
  de Bruijn–Newman deformation `H_t` with `|Re z| ≥ max(X₀, 2π·exp((1 + √3/2 + ε)/t))` is real.
  The corpus has `2π e^{40/t}` (`riemannHeat_zeros_real_of_le_re`, KiKimLeeEffectiveReality).
- **Honest scope:** RH-blind. The threshold constant `c` (zeros real once `t log(X/2π) ≥ c`) is
  `1/(1−2μ)` under the subconvexity exponent `μ ≤ 1/6`, `1 + √3/2` under convexity, and `> 1` for any
  window method. `c < 1` needs information about where the zeros lie (opus rows 172, 175, 181, 193; PTR row 82).

## Paper proof (scaling version of the corpus KKL argument)

Notation as in KiKimLeeRelativeBounds: `α = ½log(X/2π)`, `a = α + iπ/4`, `F(w) = ξ(½+w+iX)`,
`g_t(v) = (4πt)^{−½}e^{−v²/4t}`, `Q(y) = ∫_0^∞ g_t(w−y)F(w)dw`, `u = y + 2tα`, `c = 2tα`,
`P = ‖F(u)‖e^{−tα²}`. Completing the square, `g_t(w−y)e^{wα} = g_t(w−u)e^{yα+tα²}`.

1. **Slope model near σ = 1.** For `1 < σ ≤ X/32`:
   `‖ξ'/ξ(σ+iX) − a‖ ≤ ‖ζ'/ζ(σ+iX)‖ + 1/60 + O(1/X) ≤ 1/(σ−1) + 3`,
   using `‖ζ'/ζ(σ+iX)‖ ≤ −ζ'/ζ(σ) ≤ 1/(σ−1)+1` for `σ ≤ 2` and `≤ 2` for `σ ≥ 2`.
   Window start `w₁ = ½ + ε₁` gives a model error `η₁ = 1/ε₁ + 3` on `[w₁, W]`.
2. **Model error.** `∫ g_t(w−u)(e^{η₁|w−u|} − 1) ≤ 2η₁√(4t/π)·e^{tη₁²}`, which → 0 as `t → 0`.
3. **Strip `0 < w ≤ w₁`.** Use Stirling (`‖Γ(a+iy)‖ ≤ y^{a−b}e^{6(b−a)/y}‖Γ(b+iy)‖`), convexity
   (`‖ζ(σ+iX)‖ ≤ C_η X^{(1+η−σ)/2}`, ZetaConvexityBound), and `‖ζ(½+u+iX)‖ ≥ c₀(ε)` for
   `½+u ≥ 1+ε`. These give `‖F(w)‖ ≤ C·e^{α(w−u)}X^{(½+η−w)/2}‖F(u)‖`. The strip term relative to `P`
   is `≤ C′ t^{−½} max_w exp((1/4t)[−(u−w)² + 2c(½+η−w)])`. With the worst `y = −½` and
   `θ = ½−w ∈ [−ε₁, ½]`, the bracket is `−(c−1+θ)² + 2c(θ+η)`. It decreases in `θ`, so it is worst at
   `θ = ½`, and it is negative iff `(c−½)² > c(1+2η)`, i.e. `c > 1+η+√((1+η)²−¼)` (→ `1+√3/2`).
4. **Lower tail** (model below `w₁`): `≤ e^{−(u−w₁)²/4t}`, with `u − w₁ ≥ c − 1 − ε₁ > 0`.
5. **Far region** `w > W = c + α²`: unchanged from the corpus (`kklRC`, `kklRB`).
6. **Assembly:** `re_mul_conj_pos_of_estimates` as in `re_slope_mul_conj_pos`. All errors → 0 as
   `t → 0` with `c` fixed above the threshold. For `t ∈ [t₁, 1/8]` use the corpus uniform result
   (`KiKimLeeUniformReality`).

## Lean plan (new modules; corpus modules untouched)

- [x] M1 `XiHorizontalSlopeNearOne`: `norm_logDeriv_riemannZeta_le_inv_sub_one_add_two`, `norm_logDeriv_xi_sub_horizontalSlope_le_near` (Lean, wired).
- [x] M2 `XiLineNearOneWindow`: `norm_xiLineDeriv_sub_le_near`, `norm_xiLine_sub_model_le_near` (window `[½+ε, X/32−½]`, error `1/ε+3`; Lean, wired).
- [x] M3 `XiLineStripConvexity`: `exists_norm_xiLine_le_strip_convexity` (`‖F(w)‖ ≤ K X^{(½+η−w)/2}(X/2π)^{(w−u)/2}‖F(u)‖`; Lean, wired).
- [x] M4 `XiLineStripGaussianSharp`: `strip_bracket_le` (worst case `y=−½, w=0`), `gaussDensity_mul_norm_xiLine_le_sharp`, `sharp_strip_terms_le` (all three strip terms `≤ P·sharpStripErr`, with `e^{−m/4t}`, `m ≤ c²−2c(1+η)+¼`; Lean).
- [x] M5 (`HeatGaussianScaledModelError`, `KiKimLeeSharpTerms`, `KiKimLeeSharpFarTerms`) the remaining errors near the window start `½+η`: lower tail (Chernoff with β = α/2: excess `(α/2)(1+η−¾c)`), model error with a `√t` bound `∫g_t(v)(e^{η₁|v|}−1) ≤ 2η₁√t e^{2tη₁²}` (Cauchy–Schwarz; the corpus bound `2η e^{t(1+η)²}` is not small), near versions of `windowMass_le` and `far_terms_le`. **Caveat (found while planning M5):** the far region cannot use the near model on the whole window, because its error `η₁ = 1/η+3` acting over length `≍ α²` gives `e^{η₁α²}`. Use a split model instead: `η₁` on `[u, 9/2]` (a constant factor `e^{9η₁/2}`) and the corpus `1/8` model on `[9/2, W]`. The model-error and window-mass terms are Gaussian-localised, so `η₁` is harmless there.
- [x] M6 `KiKimLeeSharpReality`: `re_slope_mul_conj_pos_sharp`.
- [x] M7 `KiKimLeeSharpHorizon`: `exists_sharp_params`, `sharp_error_bounds`, `eventually_sharp_errors_small`, `riemannHeat_ne_zero_sharp`, **`riemannHeat_zeros_real_sharp`**.

## Log
- 2026-10-12: card created (PTR cycle 95). Paper sketch above; Lean M1 next.
- 2026-10-12: M1–M4 in Lean (four modules, standard axioms). The worst exponent is at the critical line `w = 0` with `y = −½`, giving threshold `c² − 2c(1+η) + ¼ > 0`. Next: M5, then the assembly M6 and the uniform theorem M7 (split `c ≥ 40` → corpus effective KKL; `t ≥ t₁` → corpus uniform KKL).
- 2026-10-12: **Formalized.** `RHTower.DeBruijn.riemannHeat_zeros_real_sharp`: for every `ε > 0`, `∃ X₀`, `∀ 0 < t ≤ 1/8`, every zero `z` of `H_t` with `|Re z| ≥ max(X₀, 2π e^{(1+√3/2+ε)/t})` is real. Ten new modules, standard axioms, wired into the RHTower umbrella. The lint gate flags only other agents' modules. Case split by `c = t log(X/2π)`: `c ≥ 40` uses the corpus effective KKL; `c₀ ≤ c < 40` uses the sharp window, with every error bounded by a function of `α` alone on `t ∈ [c₀/2α, 20/α]`. No separate small-`t` regime is needed.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 paper proof (above)
- [x] 2 → 3 formalized (`riemannHeat_zeros_real_sharp`)
- [ ] 3 → 4 not pursued

## No-go closure (the `c < 1` wall)
- Strongest positive survivor (paper, heuristic): the heat horizon constant measures the zero-free strip. At height `X`, `H_t` acts on the `n`-th approximate-functional-equation term as a cosine shift of depth `t log(X/(2πn)) ∈ [c/2, c]` (PTR row 100). A real sea pushes a zero of depth `y₀` to the axis in heat time `≍ y₀/log X` (row 101), so `c* ≍ 2Θ − 1` with `Θ = sup β`, and `c* = 0` under RH.
- Lean status: not formalized. A rigorous survival lower bound for a deep zero under the flow is missing: Rouché with Cartan bounds gives only `X^{−C}`, and the cluster-sum Lyapunov argument is not dependency-closed.
- 2026-10-12: **Simplicity added.** `RHTower.DeBruijn.riemannHeat_zeros_real_simple_sharp` (module `KiKimLeeSharpSimpleZeros`): above `max(X₀, 2π e^{(1+√3/2+ε)/t})`, zeros of `H_t` are real and simple, with one `X₀` for all `0 < t ≤ 1/8`. This is the full Ki–Kim–Lee statement at the convexity constant. `KiKimLeeSharpHorizon` was refactored so the window positivity is exposed as `re_slope_pos_sharp_window`, which also covers the corpus regime `t log(X/2π) ≥ 40`. Standard axioms; wired.
