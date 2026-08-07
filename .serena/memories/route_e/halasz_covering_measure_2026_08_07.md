# The covering step: large values occupy a proportion O(δ) of the range (2026-08-07)

Two modules, both green and axiom-clean, both in their umbrellas.

`HTGeometry/DiameterCoveringMeasure.lean` (general, no Dirichlet series):
- `volume_le_of_pairwise_dist_le` : pairwise-`w`-close set of reals ⇒ `volume ≤ 2w`. No measurability
  needed (outer-measure monotonicity only).
- `volume_inter_Icc_le_of_cells` : thin cell-by-cell (every interval of length `h`) ⇒
  `volume (A ∩ [-T,T]) ≤ (2T/h + 1)·2w`.
  **Use `⌊2T/h⌋ + 1` cells, NOT `⌈2T/h⌉`** — with `2T/h` an integer the ceiling count leaves the right
  endpoint uncovered (the `k < N` covering claim is then false at `t = T`).

`RHTower/Sieve/HalaszLargeValueWindow.lean` (appended):
- `volume_largeValues_le` : `volume {t ∈ [-T,T] : ‖F(σ+it)‖ > damped} ≤ (2T·log z/π + 1)·2√(2π²δ²/W)`,
  with cells of length `π/log z` (which is exactly what makes the window lemma's smallness hypothesis
  automatic). Since `logSqWeight z ≍ (log z)²/2`, the bound is `O(Tδ) + O(δ/log z)`.

Next: combine with `Sieve/DirichletMeasureLargeValues.integral_norm_dirPoly_halasz`
(`∫₀^T|F| ≤ V·T + M·|{|F| ≥ V}|`) to get the `t`-integral, then the Perron assembly
(`HTGeometry.SmoothWeightPerron`, arbitrary unimodular coefficients).

Lean note: `Real.le_sqrt` needs two nonnegativity args; `Nat.floor_le_floor` for monotonicity;
`div_div_eq_mul_div` converts `2T/(π/log z)` into `2T·log z/π`.

See `mem:route_e/halasz_large_value_window_2026_08_07`.
