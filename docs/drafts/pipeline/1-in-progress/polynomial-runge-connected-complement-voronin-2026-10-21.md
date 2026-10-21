# Polynomial Runge theorem on compacts with connected complement; Voronin universality on such compacts

- **ID:** HT-polynomial-runge-connected-complement-2026-10-21
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, in progress)
- **Source:** Corpus grid-contour Runge framework (`HTGeometry/RungeGridContour`, `RungeSelection`, `RungeEdgeRiemann`, `RungeEdgeApprox`, `RungePolePush`, `RungeDensity`: approximation by functions analytic and differentially algebraic on a domain), `CauchyKernelPolynomialApprox` (far pole ⟹ polynomials), the compact-set universality chain `ZetaVoroninUniversalityOnCompactSets` (targets analytic and nonvanishing on a disc containing `K`).
- **Statement (target):** (i) **Polynomial Runge.** If `K ⊂ ℂ` is compact with `ℂ \ K` connected and `F` is analytic on an open set containing `K`, then `F` is uniformly approximable on `K` by polynomials (`ApproxOn K PolyFun F`). (ii) **Voronin universality for connected-complement compacts of the strip.** If moreover `K` lies in `1/2 < Re s < 1` and `g = exp ∘ F` (equivalently `g` analytic and nonvanishing on a simply connected open neighbourhood of `K`), then for every `ε > 0` the shifts `τ` with `sup_K |ζ(s+iτ) − g(s)| < ε` have positive lower density.

## Goal

The corpus search (`research "polynomial approximation compact connected complement Runge"`,
`"pole pushing Cauchy kernel polynomial approximation ApproxOn"`) finds the grid-contour Runge
theorem only in the differentially-algebraic form `approxOn_rungeDA_of_analyticOnNhd` (poles pushed
to a point outside the domain or to infinity in one step), the disc case (`DiscPolynomialDensity`),
the far-pole polynomial expansion (`tendstoUniformlyOn_cauchyKernel_poly`, `exists_infPush_small`),
and the one-step pole transfer (`exists_polePush_small`). No polynomial Runge theorem on a general
compact with connected complement exists. The compact-set universality theorem is limited to targets
analytic on a disc containing `K` exactly because the admissible joint targets are the closure of
the diagonal polynomial restrictions (`primeSpan = polyTupleSpan`); polynomial Runge removes the
disc.

## Route

1. `PolyFun` = polynomial functions; closure under sums, scalar multiples, products.
2. **Pole pushing along a connected complement.** For `w ∉ K`, `ApproxOn K PolyFun (z ↦ (z−w)⁻¹)`:
   the set of such `w` is open and relatively closed in `ℂ \ K` (one-step transfer
   `exists_polePush_small` with `‖w' − w‖ < d ≤ dist(K, w)`, powers of an approximable bounded
   function are approximable) and contains the far points (`exists_infPush_small`); connectedness
   of `ℂ \ K` (`IsPreconnected.subset_left_of_subset_union`) gives all of `ℂ \ K`.
3. **Edge integrals and the contour functional** are approximable by polynomials on `K`
   (Riemann sums `exists_edgeCauchyRiemann_approx`, with `K` itself in place of the tube), since
   the surviving edges avoid `K` (`hEdge_avoids_of_hCoeff_ne_zero`).
4. **The contour functional equals `2πi F` on all of `K`**: it does on points off the grid lines
   inside selected squares (`contourFunctional_eq`); it is continuous at every point of `K`
   (surviving edges are at positive distance from `K`; direct estimate of the parametric
   integral), and every point of `K` is in the closure of the open floor square, which is selected.
5. Assembly: `approxOn_polyFun_of_analyticOnNhd`.
6. Universality: approximate `F` on `K` by a polynomial `P` within `η`; `exp P` is entire and
   nonvanishing, so `exists_pos_density_zetaTargetReturnSet_of_differentiable_of_isCompact`
   applies; `‖exp F − exp P‖ ≤ 2 e^{sup_K ‖F‖} η` on `K`.

## Gates
- [x] 0 → 1  in-progress: route fixed by corpus search
- [ ] 1 → 2  paper proof complete
- [ ] 2 → 3  Lean compiled, wired, axioms standard
- [ ] 3 → 4  not pursued (user rule)

## Log
- 2026-10-21 — created after `riemannHypothesis_iff_zetaStronglyRecurrent` and
  `exists_pos_density_zetaTargetReturnSet_of_isCompact` (disc-analytic targets); corpus searched.
