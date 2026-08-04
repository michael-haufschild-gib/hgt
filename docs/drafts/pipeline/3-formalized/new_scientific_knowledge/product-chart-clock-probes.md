# Clock probes on a product chart: a principal part that varies in space

- **ID:** product-chart-clock-probes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** child of `two-species-conformal-clock-scale-law`; successor of
  `variable-speed-arbitrary-potential-clock-probes`
- **Statement:** A two-dimensional clock spacetime multiplied by a flat factor carries clock probes
  at every event, so its potential — and, on the conformal orbit, its conformal factor — is
  determined by the probes, in every dimension `2 + k` and for a principal part that varies in
  *space* as well as in time.

## Goal

Every earlier clock chart in the corpus has a principal part that varies at most in time: the
Klein–Gordon chart is constant, the cosmological chart varies along the leaves of a foliation, the
variable-speed (Hill) chart varies in the time coordinate alone. The closing note of the predecessor
card states the frontier verbatim:

> The principal part must still be independent of the point. A chart whose principal part varies in
> space needs genuine variable-coefficient hyperbolic theory — energy estimates in Sobolev spaces
> with commutator terms — of which mathlib has none.

The product construction crosses that frontier without any such theory. In two dimensions the
corpus already owns the *full* variable-coefficient inverse step, unconditionally: the Goursat
problem `∂ξ∂η u = (V/4) u` is solved for an arbitrary `C¹` potential, and — because in dimension two
the conformal law of the d'Alembertian degenerates to `□_{e^{2σ}g} = e^{-2σ} □_g` with no
differentiability hypothesis — the same probe serves every conformal rescaling of the surface, i.e.
every Lorentzian metric on it. Crossing a two-dimensional chart with a flat factor and then
rescaling the product conformally by an arbitrary smooth `σ` of **all** `2 + k` coordinates produces
a chart whose inverse metric varies in every coordinate, and the probe of the two-dimensional factor,
pulled back along the projection, is a probe of the product.

## Gates

- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (the two-dimensional inverse step and the conformal transfer are corpus
      theorems; the product step is the elementary block computation below)
- [x] 2 → 3  formalized — `formal/GaloisForLFunctions/HTGeometry/ProductChartDalembertian.lean`,
      `formal/GaloisForLFunctions/HTGeometry/ProductChartProbes.lean`; every theorem below builds and
      depends only on `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## Approach

Write `front : (Fin (n + k) → ℝ) → (Fin n → ℝ)` for the projection onto the first block.

1. **The product chart.** `M.prodFlat k` has inverse metric the block matrix `M.inverseMetric
   (front y) ⊕ 1` and density `M.density (front y)`. Smoothness, positivity and symmetry are
   entrywise.
2. **Coordinate transfer.** For `u` differentiable at `front y`:
   `∂_{castAdd i} (u ∘ front) y = (∂_i u)(front y)` and `∂_{natAdd i} (u ∘ front) y = 0`.
   Both are the chain rule for the continuous linear map `front`, whose transpose sends the
   coordinate vector `e_{castAdd i}` to `e_i` and `e_{natAdd i}` to `0`.
3. **Flux transfer.** On the preimage of a region where `u` is differentiable, the flux of the
   product chart in a front direction is the flux of `M`, composed with `front`; in a transverse
   direction it vanishes identically. The transverse block contributes nothing because the metric
   is block diagonal and `u ∘ front` is constant transversally.
4. **The d'Alembertian.** Splitting `∑_{a : Fin (n+k)}` by `Fin.sum_univ_add` and using 3,
   `(M.prodFlat k).dalembert (u ∘ front) y = M.dalembert u (front y)`, for `u` with differentiable
   partials on an open region containing `front y`. No hypothesis on the transverse behaviour is
   needed, and none on `u` beyond the regularity the chart calculus consumes.
5. **Probes.** Hence regular probes transport: `RegularOpenProbes M.dalembert V` implies
   `RegularOpenProbes (M.prodFlat k).dalembert (V ∘ front)`. The two-dimensional existence theorem
   is upgraded to record the regularity its Goursat construction already produces (the composite of
   the `C²` characteristic solution with the linear null frame), which is what the transfer
   consumes.
6. **Conformal orbit and scale law.** The corpus's conformal transfer then applies to the product
   chart with an arbitrary smooth `σ` on `Fin (2 + k) → ℝ`, and two species of different mass
   sharing one `C¹` two-dimensional potential reconstruct `e^{-2σ}` pointwise.

## Numbered statements

1. `prodFlat_dalembert_comp_front` — the d'Alembertian of the product chart on a transversally
   constant field is the d'Alembertian of the factor.
2. `differentiablePartialsOn_comp_frontMap` — regularity transports to the pullback.
3. `regularOpenProbes_prodFlat` — regular probes transport to the product chart.
4. `exists_clockProbe_on_two_dimensional` (strengthened) — the two-dimensional probe has
   differentiable partials on its region.
5. `regularOpenProbes_prodFlat_two_dimensional` — the product of the null chart with a flat factor
   carries regular probes for every `C¹` potential of the two-dimensional factor.
6. `regularOpenProbes_conformalRescale_prodFlat_two_dimensional` — and so does every conformal
   rescaling of it, by an arbitrary smooth factor of all coordinates.
7. `potential_eq_of_probes_prodFlat_two_dimensional` — the probes determine the potential
   everywhere.
8. `twoSpecies_scale_law_flatProductChart` — two species of different mass reconstruct the conformal
   factor pointwise.
9. `warpedProductChart`, `regularOpenProbes_warpedProductChart` — the two-dimensional block may
   carry a conformal factor of its own coordinates while the transverse block does not; this warped
   product is not a conformal rescaling of the flat product, and it carries regular probes.
10. `regularOpenProbes_conformalRescale_warpedProductChart` — the widest class reached: an arbitrary
    conformal factor on the two-dimensional block, a second arbitrary conformal factor on all
    `2 + k` coordinates, an arbitrary `C¹` potential on the factor.
11. `twoSpecies_scale_law_warpedProductChart` — there the two species reconstruct the *product* of
    the two conformal factors, `e^{-2σ}·e^{-2σ₂∘front}`.

## Lean names as built

| card statement | Lean name |
|---|---|
| 1 | `SmoothMetricChart.prodFlat_dalembert_comp_front` |
| 2 | `SmoothMetricChart.differentiablePartialsOn_comp_frontMap` |
| 3 | `SmoothMetricChart.regularOpenProbes_prodFlat` |
| 4 | `exists_clockProbe_on_two_dimensional`, `regularOpenProbes_two_dimensional` |
| 5 | `regularOpenProbes_flatProductChart` |
| 6 | `regularOpenProbes_conformalRescale_flatProductChart` |
| 7 | `potential_eq_of_probes_flatProductChart`, `potential_eq_of_probes_conformalRescale_flatProductChart` |
| 8 | `twoSpecies_scale_law_flatProductChart` |
| 9 | `warpedProductChart`, `regularOpenProbes_warpedProductChart` |
| 10 | `regularOpenProbes_conformalRescale_warpedProductChart` |
| 11 | `twoSpecies_scale_law_warpedProductChart` |

## What the layer reaches, and what it does not

The determined potential of the rescaled chart is not a function of the two-dimensional coordinates
alone: it is `e^{-2σ}(V∘front + w·□σ + w²·Γ(σ,σ))` with `w` the conformal weight, and that depends on
all `2 + k` coordinates. What the construction cannot reach is a potential whose *dependence* on the
transverse coordinates is prescribed independently of the conformal factor: a probe that is constant
in the transverse directions forces the potential of the unrescaled product to be transversally
constant wherever the probe is nonzero. Reaching those needs a probe that genuinely propagates in
`2 + k` directions, i.e. the higher-dimensional inverse step.

The frontier the predecessor card named — a principal part that varies in space — is crossed here,
but by a product argument rather than by variable-coefficient hyperbolic theory. A chart which is
*not* conformal to a product of a surface with a flat factor still needs energy estimates in Sobolev
spaces with commutator terms, of which mathlib has none.

## Log
- 2026-08-04 — created in 1-in-progress; approach settled, Lean layer under construction.
- 2026-08-04 — formalized; two new modules, the two-dimensional probe theorem strengthened to expose
  the regularity its Goursat construction already produced. Moved to 3-formalized.
