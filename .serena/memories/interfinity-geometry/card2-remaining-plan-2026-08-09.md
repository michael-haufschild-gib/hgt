# Cards 2 and 3 — what is built and what is left (updated)

All modules live in `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/`, namespace
`GaloisForLFunctions.HTGeometry.Interfinity`, wired into `HTGeometry/InterfinityGeometry.lean`.
`lake build GaloisForLFunctions.HTGeometry.InterfinityGeometry` is green.

## Card 2 — items 1, 2, 3, 4 COMPLETE.  Only item 5 (complex time) is left.

Built:
* `SpectralHorizonCocycle.lean` — cocycle, `integrableOn_laplaceCochain_sq` (β > −2),
  `isCoboundary_iff` (β > 0), `observerLine`, `deathCut`, `stableRegion`, `deathCut_add`.
* `SpectralFinitePart.lean` — `ChartFun`, `ofContDiff`, `transport`, the three convergence lemmas.
* `SpectralPrimitiveIdentity.lean` — `finitePart`, `finitePart_transport_sub` (identity (6)),
  `tendsto_transported_finitePart` (stability for a > 0).
* `SpectralCutObstruction.lean` — `cutIntegral`, `tendsto_cutIntegral_atBot`,
  `not_tendsto_finitePart_of_nonpos` (no stable primitive for a ≤ 0).
* `HadamardDivision.lean` — **built from scratch (missing in mathlib)**: `hadamardAvg`,
  `hasDerivAt_hadamardAvg`, `contDiff_hadamardAvg`, `hadamard_eq` (Hadamard's lemma for C^∞ on ℝ),
  `expDefectFactor`, `laplace_defect_factor` (`e^{-Vs} − 1 = s · E_V(s)`).
* `SpectralFixedSubspace.lean` — `smoothTestSpace`, `smoothMul`, `eq_zero_of_fixed`,
  `fixed_eq_smul_deltaZero` (**item 4a: fixed subspace = ℝ·δ₀**), `deltaZero_fixed`.
* `SpectralGammaIntegral.lean` — `gammaDefect`, `integral_gammaDefect = Real.Gamma a`
  for −1 < a < 0 (integration by parts, both boundary terms vanish).
* `SpectralGammaScaling.lean` — `cutIntegral_scaling`, `tendsto_regularizedCut`,
  `integral_expScaled` (`∫₀^∞ e^{-Vs}s^a = V^{-(a+1)}Γ(a+1)`).
* `SpectralDeficientAsymptotics.lean` — `transportedFinitePart`, Hadamard split,
  `tendsto_transportedFinitePart` (**item 4b: V^a·η_a(e^{-V·}h) → cΓ(a)h(0)**).
* `SpectralLogarithmicHorizon.lean` — `cutIntegral_zero_split`,
  `tendsto_cutIntegral_zero_div_log`, `tendsto_transportedFinitePart_log`
  (**the a = 0 logarithmic contact law**).

### Card 2, item 5 (complex time) — the only gap
Needs `∫₀^∞ e^{-wt} t^{s-1} dt = Γ(s) w^{-s}` for `Re w > 0`.  Cheapest route: both sides are
analytic in `w` on the connected open right half-plane and agree on `w > 0` real, so the identity
theorem gives it; analyticity of the integral in `w` needs differentiation under the integral
(mathlib `hasFDerivAt_integral_of_dominated_loc_of_lip`, already used in
`ParametricSmoothness.lean`).  Then (10) `R^a T_z η_a → cΓ(a)e^{-iaθ}δ₀` follows exactly as in the
real case, and (11) `∂_θ arg = −a` is a one-line computation on `Γ(a)e^{-iaθ}`.
(12) additionally needs `∫₀¹ (e^{-t}−1)/t dt + ∫₁^∞ e^{-t}/t dt = −γ` (Euler–Mascheroni).

## Card 3 — items 2 (regions) and 3 (fixed faces) COMPLETE.

Built:
* `MultiTimeRegions.lean` — `multiObserverRegion`, `multiStableRegion`, product descriptions,
  openness, convexity, coordinatewise horizon widths.
* `ParametricSmoothness.lean` — **built from scratch (missing in mathlib)**: `paramAvg`,
  `partialFderiv`, `hasFDerivAt_paramAvg` (differentiation under the integral sign),
  `contDiff_paramAvg` (universe-fixed induction: `G : Type (max u v)` so `E →L G` stays in range).
* `MultiTimeHadamard.lean` — `scaleCoord`, `coordRemainder`, `coord_hadamard`
  (**Hadamard in one coordinate of several**).
* `MultiTimeFixedFaces.lean` — `zeroAt`, `faceChart`, `multiTestSpace`, `multiMul`,
  `multi_eq_zero_of_fixed`, `multi_eq_face` (**item 3: fixed subspace of the times in J is the
  face restriction**), `multi_eq_smul_delta` (deepest stratum = ℝ·δ₀).

### Card 3, remaining
* item 1: `b_V ∈ H_β` — the weighted `L²` norm factorizes over coordinates; needs the
  product-measure integrability of a product function (`MeasureTheory.Measure.pi`,
  `integral_fintype_prod_eq_prod` / `integrable_fintype_prod`).
* item 2 (second half): the iterated finite-part coboundary and the characterization of
  face-stable primitives as exactly `D_β` (tensor version of card 2 items 2 and the cut
  obstruction).
* item 4: the tensor finite part (6), sectorial asymptotics (7) — shares the complex-analysis
  dependency with card 2 item 5 — and the conormal phase (8).

## Lean traps hit (in addition to the earlier list)
- `ContDiff.differentiable` now wants `n ≠ 0`, `continuous_deriv`/`continuous_fderiv` want `n ≠ 0`
  or `1 ≤ n` depending on the lemma.
- `contDiff_succ_iff_deriv/fderiv` carry an extra `(n = ⊤ → AnalyticOn …)` obligation, vacuous for
  `n : ℕ` (`intro hcon; exact absurd hcon (by simp)`).
- Recursive `ContDiff` inductions whose codomain changes (`G ↝ E →L[ℝ] G`) must fix the universe:
  state `∀ {G : Type (max u v)} …` and use `induction n`.
- `Continuous.prodMk_right x : Continuous fun t => (x, t)`; `prodMk_left` is the other order.
- `Function.update_of_ne` (not `update_noteq`).
