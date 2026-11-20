# Mod-4 phase cancellation in column Hasse–Davenport, cube-twisted columns, and cubic cross-phase collapse

- **ID:** osmt-cube-twisted-columns-and-cross-phase-collapse
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** `docs/reports/review-1911/todo.md` #12 · `formal/GaloisForLFunctions/OrderSixMetaplecticTheory/CubeTwistedColumnsAndCrossPhaseCollapse.lean`
- **Statement:** In `rowRoot_column_hasseDavenport`, the mod-4 Weil factor `\overline{r(n₁ n₂^2 k^3, c)} r(n₁ k, c)` equals `1` identically, yielding the phase-free column identity `(g_c^{(1)}(n₁ n₂^2 k^3)/|c|) G̃(-2 n₁ n₂) G̃(n₁) = (g_c^{(3)}(n₁ k)/|c|) G̃(-2 n₁ n₂ c) G̃(n₁ c)`; for any `a ∈ O` and `d` prime to `c`, `g_c^{(1)}(a d^3) = (d/c)_2 g_c^{(1)}(a)`, collapsing the coupled twist column `\overline{χ_c(n₁ n₂^2 k^3)} (c/d)_2 Φ(c) G̃(-2 n₁ n₂) G̃(n₁)` to `r(d, c) (g_c^{(3)}(n₁ k d)/|c|) G̃(-2 n₁ n₂ c) G̃(n₁ c)`; and across `c = ∏_{π ∈ s} π`, `g_c^{(1)}(1) g_c^{(3)}(1)` factors over `s` with purely cubic cross-phase `∏_{π ∈ s} ∏_{q ∈ s \setminus \{π\}} (q/π)_3^2`.

## Goal
Simplify `rowRoot_column_hasseDavenport` by proving exact cancellation of its mod-4 quadratic bicharacter factor, absorb external quadratic twists `(c/d)_2` into cube-multiplied column shifts `a ↦ a d^3`, and prove the ordered-pair local-to-global Gauss product formula showing that `g_c^{(1)}(1) g_c^{(3)}(1)` has purely cubic cross-phases.

## Gates
- [x] 0 → 1  in-progress: exact interfaces in `TheColumnsAreShiftedThetaProducts.lean` and `TheQuadraticPhaseIsABicharacterModuloFour.lean` verified
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `CubeTwistedColumnsAndCrossPhaseCollapse.lean`, `lake --old env lean` green, standard axioms only

## Paper Proof (`[PROVED HERE]`)

1. **Exact cancellation of the mod-4 Weil factor in `rowRoot_column_hasseDavenport`.**
   - On odd classes (`x ∉ (2)`, i.e. `IsCoprime x 2`), `quadraticPhase_sq` gives `r(x, c)^2 = 1`, so `r(x, c) ∈ {±1}` and `\overline{r(x, c)} = r(x, c)`.
   - By `quadraticPhase_mul_left`, `r(n₁ n₂^2 k^3, c) = r(n₁, c) r(n₂, c)^2 r(k, c)^3 = r(n₁, c) · 1 · r(k, c) = r(n₁ k, c)`, whence `\overline{r(n₁ n₂^2 k^3, c)} r(n₁ k, c) = r(n₁ k, c)^2 = 1`. Substituting into `rowRoot_column_hasseDavenport` removes all mod-4 phases.

2. **Conjugate-symbol column absorption and cube-multiplied column shift (`conj_sexticSymbol_mul_rowRootNumber`, `sexticGauss_mul_cube`, `orderB_coupled_column_collapse`).**
   - For primary `c ≠ 0` prime to `2` and `a` prime to `c`, `χ_c(a) g_c^{(1)}(a) = g_c^{(1)}(1)` and `\overline{χ_c(a)} χ_c(a) = 1`, giving `\overline{χ_c(a)} (g_c^{(1)}(1)/|c|) = g_c^{(1)}(a)/|c|`.
   - For any `a ∈ O` and `d` prime to `c`, `χ_c(d^3) g_c^{(1)}(d^3 a) = g_c^{(1)}(a)` (`sexticSymbol_mul_sexticGauss`). Since `χ_c(d^3) = χ_c(d)^3 = (d/c)_2` (`symbol_cube` and `quadSymbol_sq`) and `(d/c)_2^2 = 1`, multiplying by `(d/c)_2` gives `g_c^{(1)}(a d^3) = (d/c)_2 g_c^{(1)}(a)`.
   - When `d` is also primary and prime to `2`, quadratic reciprocity `(c/d)_2 = r(d, c) (d/c)_2` turns `\overline{χ_c(n)} (c/d)_2 Φ(c)` into `r(d, c) g_c^{(1)}(n₁ n₂^2 (kd)^3)/|c|`, and the phase-free Hasse–Davenport column identity collapses the product with `G̃(-2 n₁ n₂) G̃(n₁)` to `r(d, c) (g_c^{(3)}(n₁ k d)/|c|) G̃(-2 n₁ n₂ c) G̃(n₁ c)`.

3. **Symmetric prime-product Gauss factorization and cubic cross-phase collapse (`sexticGaussPow_prod_eq`, `sexticGauss_mul_quadGauss_prod_cubic_cross`).**
   - Inducting over `s` via `sexticGaussPow_mul`, inserting `π ∉ t` multiplies by `(χ_π(∏_t q) χ_{∏_t q}(π))^j = (∏_{q ∈ t} χ_π(q)^j)(∏_{q ∈ t} χ_q(π)^j)`, matching the ratio of `∏_{x ∈ s} ∏_{y ∈ s \setminus \{x\}} χ_x(y)^j` between `insert π t` and `t`.
   - Taking `j = 1` times `j = 3` at `h = 1` combines the cross-factors into `χ_x(y)^4 = (χ_x(y)^2)^2 = (y/x)_3^2` (`sexticSymbol_sq_eq`), eliminating all quadratic cross-signs.

## Log
- 2026-11-20 — complete paper proof recorded in `2-fully-proven`.
