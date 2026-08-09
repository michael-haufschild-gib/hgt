# Interfinity geometry — all six cards formalized (stage 3)

All six cards moved to `docs/drafts/pipeline/3-formalized/interfinity-geometry/`, each with a
`-formalized.md` companion.  Gates `2 → 3` flipped.  `GaloisForLFunctions.MainTheorems` builds;
`scripts/formal_tools.py lint --check-generated` is clean.

## Lean surface

32 modules in `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/` (sub-umbrella
`InterfinityGeometry.lean`, imported by `HTGeometry.lean`), plus
`RHTower/ArithmeticMixedRateStableQuotient.lean` and
`RHTower/ArithmeticThreeChartStableBoundary.lean`.

## Built because mathlib has none

- `HadamardDivision.lean` — Hadamard's lemma for `C^∞` on ℝ: `h s = h 0 + s·r s` with `r` smooth,
  via `hadamardAvg k G s = ∫₀¹ tᵏ G(ts) dt` and differentiation under the integral.
- `ParametricSmoothness.lean` — `contDiff_paramAvg`: `x ↦ ∫₀¹ F x t dt` preserves every finite
  order.  The induction must be stated as `∀ {G : Type (max u v)} …` because the codomain changes
  to `E →L[ℝ] G` at each step; structural recursion hits a universe mismatch.
- `SpectralComplexGamma.lean` — `∫₀^∞ (e^{-wt}−1)t^{a-1} = Γ(a)w^{-a}` (−1<a<0) and
  `∫₀^∞ e^{-wt}t^{a-1} = Γ(a)w^{-a}` (a>0) for `Re w > 0`.  Recipe: integrability by splitting
  `Ioi 0 = Ioc 0 δ ∪ Ioi δ` with `δ = min 1 (1/(‖w‖+1))`; holomorphy by
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `ball w (w.re/2)` with bound
  `e^{-(w.re/2)t} t^a` (= corpus `integrableOn_expScaled`); then
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` at `z₀ = 1`, frequency supplied by
  `Tendsto (↑·) (𝓝[>] 1) (𝓝[≠] (1:ℂ))`.
- `SpectralEulerConstant.lean` — `∫₀¹(e^{-t}−1)/t + ∫₁^∞ e^{-t}/t = −γ`.  Route: split
  `Γ(a) = A a + B a + 1/a` for −1<a<0 (`integral_Ioi_rpow_of_lt` gives `∫_{Ioi 1} t^{a-1} = −1/a`),
  `continuousAt_of_dominated` at `a = 0` for both halves, and `Γ(a) − 1/a = slope Γ 1 (a+1) → Γ'(1)`
  using mathlib's `Real.hasDerivAt_Gamma_one`.
- `SpectralComplexLogConstant.lean` — `∫₀¹(e^{-wt}−1)/t + ∫₁^∞ e^{-wt}/t = −γ − Log w`.  Cheaper
  than a second identity theorem: both sides have derivative `−1/w` (the two derivative integrals
  glue to `∫_{Ioi 0} e^{-wt} = w⁻¹`, which is `cgammaOrdIntegral 1 w`), so
  `Convex.is_const_of_fderivWithin_eq_zero` plus the single evaluation at `w = 1` finishes.

## Traps hit

- `tendsto_eval_pi` takes the filter family as an explicit first argument.
- `tendsto_finset_prod` is deprecated → `tendsto_finsetProd`.
- `integrableOn_const` has two autoParams that aesop cannot discharge for `Ioo 0 1`; pass
  `(by simp) (by simp)`.
- `ChartFun.transport` needs `0 ≤ V`, so it is not total in `V`.  For limit statements define
  `ChartFun.evolve V := transport (max V 0) _` plus `finitePart_congr` (finite part depends only on
  `toFun`) and `finitePart_evolve`.
- `simpa` normalises `fun v => -(f v)` to `-f` and breaks `HasDerivAt` unification; build the
  positive statement first and apply `.neg` afterwards.

## Umbrella collisions found and fixed (other agents' modules)

`GaloisForLFunctions.HTGeometry` did not build.  Six duplicate declarations, none mine:
`jetPolynomial`, `jetVector` (renamed to `finiteJetPolynomial`, `finiteJetVector` in
`FiniteJetIndistinguishability`), `analyticMeroElement_congr`, `deriv_analyticMeroElement`
(suffixed `_inverseJet` in `LocalInverseHypertranscendence`), `quasiDividedDiff`,
`mul_quasiDividedDiff` (renamed `quasiTransformDividedDiff`, `mul_quasiTransformDividedDiff` in
`QuasiCauchyTransform`).  Rule for choosing: the error names the *importing* module as the one to
rename.  Also wired six orphan modules (`AbelianZetaGas.*`,
`FiniteDimensionalOperatorAlbertiLaw`, `SeparableBuresPositiveReporterLaw`, `QuadrantHolomorphic`)
into `HTGeometry.lean`.

394 `lake build` warnings remain project-wide; **zero** come from these 34 modules.
