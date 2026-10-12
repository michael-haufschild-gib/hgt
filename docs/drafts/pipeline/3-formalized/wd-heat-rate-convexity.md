# WD heat rate 1/log t from the convexity bound

- **ID:** wd-heat-rate-convexity
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** `wd-goal-loop-2026-10-09.md` row 292 (improves row 285: constant 100 → 1 + δ)
- **Statement:** For every δ ∈ (0, 1] there is t₀ with T_{2m}(λ, 0, t) > 0 for all |t| ≥ t₀, λ ≥ (1+δ)/log|t| and all m.

## Paper proof
1. √(2π)·n!·T_n = (1/√λ)∫e^{−x²/(2λ)}S^{(n)}(x)dx; even n, even integrand (done in Lean).
2. x ≥ ½: S^{(n)}(x) ≥ 0 (absolute monotonicity from ½ + Taylor shift).
3. Window W = [κ − w, κ] (κ = λL ≥ 1 + δ): lower bound for S^{(n)}(x)/n!:
   - n ≤ c log t: S(x+w)/S(x) = e^{h₁w}E(w), h₁ = L(x) ∈ [log(t/2) − 2C, log t + 2C], E = exp(ψ) with ψ(w) = O(|w|·M') on |w| ≤ η (Euler disc bound |L(w) − L(x)| ≤ M'); coefficients |e_k| ≤ e^{ηM'}η^{−k}, e₁ = 0; hence S^{(n)}(x)/n! ≥ S(x)h₁^n/(2 n!) for n ≤ c h₁.
   - n ≥ c log t: saddle at centre x (x + R ≥ ½ + 2η automatically): S^{(n)}(x)/n! ≥ S(x+R)Λ^{−1/2}/(40πR^n), R L(x+R) = n.
4. |x| ≤ ½ + η: Cauchy on |z − x| = r with |S(z)| ≤ C S(½+2η) t^{−η} on |Re z| ≤ ½ + η (convexity × Gamma decay, `norm_xi_split_le`) and ≤ C S(|Re z|) beyond; r = max(η, n/L): |S^{(n)}(x)| ≤ C S(½+2η)·max(n!η^{−n}, √n L^n t^{−η}).
5. Compare: positive ≳ S(½+2η)L^n t^{κ/2 − ½ − 2η}/poly(L), negative ≲ S(½+2η)L^n·poly(L); κ > 1 + 4η suffices.

## Paper proof as formalized (window x ∈ [1+δ/2, 1+δ], η = δ/8)
- Euler points x₀ ∈ [1, 2], 1 ≤ n ≤ log t: D_n(x₀) = Re S^{(n)}(x₀)/n! ≥ S(x₀)L′ⁿ/n!·1/(40π√(2 log t)), L′ = log(t/2) − 2C_{1/8}. Cumulant regime n ≤ c₁ log t gives S(x₀)h₁ⁿ/(2n!); the saddle regime (R ∈ [c₁/2, 2]) gives S(x₀+R)/(πRⁿ)·Λ^{−1/2}/40, and S(x₀+R) ≥ S(x₀)e^{L′R}, e^{L′R}/Rⁿ ≥ (eL′/n)ⁿ ≥ L′ⁿ/n!.
- Weighted window: S(x)e^{−x²u/(2κ)} ≥ S(½+δ/4)e^{u(δ/4−δ²/8)−2(log 2+2C_{δ/8})}, since x − ½ − δ/4 − x²/(2κ) ≥ δ/4 − δ²/8 on the window.
- Inner region |x| < ½: Cauchy on radius r = N/(u+2C_{δ/8}); on that circle |S| ≤ C S(½+δ/4)e^{(u+2C)r−δu/8} (strip bound for |Re z| < ½+η, growth bound beyond). So |S^{(N)}(x)|/N! ≤ C S(½+δ/4)e^{N−δu/8}((u+2C)/N)ᴺ.
- Integral: ∫h ≥ (b−a)P − 2cB for h ≥ P on [a, b], h ≥ −B on (−c, c), h ≥ 0 elsewhere. With N! ≤ e√N(N/e)ᴺ and ((u+2C)/L′)ᴺ ≤ e^{2c′}, the window wins once e^{δu/4} > Ku.
- Orders N ≥ log t: quarter-log window plus heat expansion; m = 0: zero-order positivity; larger λ: heat shift with positive weights; negative t: height symmetry.

## Lean
- `RHTower/XiSliceHeatGaussianDerivativeRepresentation`: `xiSliceHeatTransfer_eq_integral_iteratedDeriv`.
- `RHTower/XiSliceEulerGrowthAndMonotonicity`: `xiSliceReal_growth_euler`, `iteratedDeriv_xiSliceProduct_nonneg_of_half_le`.
- `RHTower/XiSliceStripGrowthBounds`: `exists_norm_xiSliceProduct_le_strip`, `norm_iteratedDeriv_xiSliceProduct_le`.
- `RHTower/XiSliceEulerCumulantLowerBound`: `iteratedDeriv_xiSliceProduct_ge_cumulant`.
- `RHTower/XiSliceSaddleQuantitativeBounds`: `integral_ge_of_arc_bounds_scaled_upto`, `iteratedDeriv_xiSliceProduct_ge_of_saddle_shift`, `factorial_le_exp_one_mul_sqrt_mul_pow`, `pow_mul_exp_le_exp`.
- `RHTower/XiSliceEulerDerivativeLowerBound`: `exists_iteratedDeriv_xiSliceProduct_ge_euler`.
- `RHTower/XiSliceHeatRateOnePlusDelta`: `integral_ge_of_window`, `exists_norm_iteratedDeriv_xiSliceProduct_le_inner`, `xiSliceReal_mul_gauss_ge_window`, `heat_window_comparison`, `exists_xiSliceHeatTransfer_pos_low_order`, `exists_xiSliceHeatTransfer_pos_at_heat_one_add_over_log`, **`exists_xiSliceHeatTransfer_pos_heat_one_add_over_log`**.
- `#print axioms`: propext, Classical.choice, Quot.sound. All modules wired into `GaloisForLFunctions.RHTower`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3

## Log
- 2026-10-11 — created; Lean step 1 (`RHTower/XiSliceHeatGaussianDerivativeRepresentation`) done.
- 2026-10-12 — fully formalized (ledger row 293). The method is capped at κ = 1 by convexity; Weyl subconvexity would give κ > ¾; below ½ the inner region carries zero information.
