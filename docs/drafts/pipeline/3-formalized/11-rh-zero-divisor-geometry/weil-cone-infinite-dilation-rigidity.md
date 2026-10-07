# Infinite-type dilation rigidity of the Weil cone

- **ID:** weil-cone-infinite-dilation-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional, standard axioms)
- **Source:** loop rows 528–531; MUST-800 (`WeilConeDilationRealnessRigidity`, finite support)
- **Statement:** Let `a : ℕ → ℝ` with `Σ |a(n)| n^{−1/2+δ} < ∞` for some `δ > 0`, and let `v` be regular. If `Λ ⋆ a + v` is full-cone Weil-positive, then `a = δ₁` and `v = 0`. Within this class a Weil-positive completion exists iff RH.

## Why it is new
- The finite-type card (`2-fully-proven/11-rh-zero-divisor-geometry/weil-cone-finite-type-uniqueness`) covers only finitely supported `a`. Its open item L106′ is infinite type.
- The corpus abscissa rigidity (`WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_rpow_summable`) needs a deviation of absolute abscissa `< 1`. `Λ ⋆ (a − δ₁)` has abscissa exactly 1, so it is not covered.
- The ζ′-moment method of the finite card does not extend to infinite Dirichlet series without new convergence control.

## Paper proof
1. **Continuation.** `A(s) = Σ a(n) n^{−s}` converges absolutely on `Re s ≥ ½ − δ`. On `Re s > 1`: `Σ lam(n) n^{−s} = −A ζ'/ζ + E`. The master identity `ζ(Φ − G − 1/(s−1) + E) = A ζ'` holds on `Re s > ½` by analytic continuation, as in `WeilFiniteTypeContinuation.zeta_mul_eq`, with `A` analytic on `Re s > ½ − δ`.
2. **Realness.** At a simple critical zero `ρ`, `Φ` has a boundary pole with residue `A(ρ)`. `boundary_pole_of_re_nonneg` makes it real, so `Im A(ρ) = 0`.
3. **Almost periodicity.** `D(z) = A(½ + iz) − A(½ − iz)` is analytic on `|Im z| < δ`. On `|Im z| ≤ r < δ` it is the uniform limit of finite exponential sums, so its real translates are totally bounded there (`HasCompactImStripTranslates`).
4. **Uniform large values.** If `D ≢ 0` on ℝ, then for each `r₀ > 0` there is `m₀ > 0` such that every interval `[x, x + r₀]` contains `t` with `|D(t)| ≥ m₀`.
   - Otherwise, translates `D(· + x_j)` that are `< 1/j` on `[0, r₀]` have a uniformly convergent subsequence on the substrip.
   - The limit is analytic and zero on `[0, r₀]`, hence zero on the substrip.
   - But every translate has the same supremum as `D`.
5. **Linear count.** Apply Jensen (`sum_divisor_le_of_bounds`) with centre `t`, inner radius `2r₀` and outer radius `4r₀ < r`. Each window of length `r₀` then holds at most `log(M/m₀)/log 2` real zeros of `D`. So `D` has `O(T)` real zeros in `[0, T]`.
6. **Contradiction.** By step 2, `D` vanishes at every simple critical ordinate. Zeta23 gives at least `T log T/(72π)` of them (`eventually_superlinear_xiSimpleCriticalZeroCount`). Hence `D ≡ 0` on ℝ.
7. **Coefficients.** `0 = D(t) = Σ_n a(n) n^{−1/2}(n^{−it} − n^{it})`, absolutely convergent. The Bohr mean of `D(t) n₀^{it}` is `a(n₀) n₀^{−1/2}` for `n₀ ≥ 2`, so `a(n₀) = 0`. Then `A(1) = 1` gives `a(1) = 1`.

## Lean plan (bricks)
- [x] B1 strip a.p. of absolutely convergent exponential sums (reusable, HTGeometry)
- [x] B2 uniform large values on windows (reusable)
- [x] B3 linear real-zero count via Jensen (reusable)
- [x] B4 receiver: strip a.p. function vanishing on simple critical ordinates is zero on ℝ
- [x] B5 master identity and residue realness for infinite `a` (RHTower)
- [x] B6 Bohr coefficient extraction and the main theorem

## Log
- 2026-10-06: card created (Opus loop row 531).
- 2026-10-06 22:35: FORMALIZED, the complete theorem, standard axioms.
  - Modules: `RHTower/WeilConeInfiniteDilationRigidity.lean` (`RHTower.WeilInfiniteDilation.eq_delta_of_weilPositiveFull`, `riemannHypothesis_of_weilPositiveFull_dilation`) and `HTGeometry/ImStripAlmostPeriodicZeroDensity.lean` (B1 `hasCompactImStripTranslates_tsum`, B2 `HasCompactImStripTranslates.exists_window_lowerBound`, B3 `…exists_linear_realZero_count`). Both are built with `lake --old build` and wired into `RHTower.lean` and `HTGeometry.lean`. STATUS MUST-801.
  - B6 does not use Bohr means. `D ≡ 0` on the strip gives `A(s) = A(1−s)` near the line. Gluing gives a bounded entire function, constant by Liouville; `LSeries.tendsto_atTop` and `LSeries_eventually_eq_zero_iff'` then give the coefficients.
  - A parallel session had started duplicate unwired modules for B1–B4; they were removed after this entry.
- 2026-10-06 22:50: corollaries `eq_delta_and_eq_zero_of_weilPositiveFull` (`v = 0` through `WeilFiniteType.regularPart_eq_zero`) and `exists_dilation_weilPositive_iff` (existence in the class ⟺ RH), standard axioms. Moved to `3-formalized/11-rh-zero-divisor-geometry/`.
- Lean map: B1 `hasCompactImStripTranslates_tsum`; B2 `HasCompactImStripTranslates.exists_window_lowerBound`; B3 `card_le_sum_divisor_of_analyticOnNhd`, `HasCompactImStripTranslates.exists_linear_realZero_count`; B4 `RHTower.eqOn_zero_of_compactImStripTranslates_of_simpleCritical`; B5 `WeilInfiniteDilation.master_identity`, `dilSeries_one_eq_one`, `exists_boundary_quotient`, `dilSeries_im_eq_zero_of_critical_simple`; B6 `hasCompactImStripTranslates_seriesReflectionDefect`, `dilSeries_reflect`, `dilSeries_eq_const` (Liouville), `eq_delta_of_weilPositiveFull`.
- 2026-10-06 22:50: the three parallel duplicate modules were deleted, together with their build artifacts. B1–B6 live only in the wired modules above.
