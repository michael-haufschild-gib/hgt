# Polynomial Runge theorem on compacts with connected complement — Lean, 2026-10-21

`GaloisForLFunctions.HTGeometry.approxOn_polyFun_of_analyticOnNhd` in
`formal/GaloisForLFunctions/HTGeometry/PolynomialRungeOnConnectedComplement.lean` (wired into
HTGeometry.lean; axioms propext/Classical.choice/Quot.sound):
`IsOpen Ω → AnalyticOnNhd ℂ F Ω → IsCompact K → K ⊆ Ω → IsPreconnected Kᶜ → ApproxOn K PolyFun F`.
`PolyFun := Set.range (fun P : ℂ[X] => fun z => P.eval z)`; explicit form
`exists_polynomial_approx_of_analyticOnNhd : ∃ P, ∀ z ∈ K, ‖F z − P.eval z‖ ≤ ε`.

Built on the corpus grid-contour Runge framework (RungeGridContour / RungeSelection /
RungeEdgeRiemann / RungePolePush / RungeDensity, which only reach the DA class `RungeDA Ω`).
New pieces: `approxOn_mul_of_bounded`, `approxOn_polyFun_cauchyKernel_pow`,
`approxOn_polyFun_cauchyKernel_of_near` (one-step transfer via `exists_polePush_small`),
`approxOn_polyFun_cauchyKernel_of_far` (`exists_infPush_small`),
`approxOn_polyFun_cauchyKernel_of_isPreconnected_compl` (clopen argument in `Kᶜ`),
`approxOn_polyFun_edgeCauchyIntegral`, `approxOn_polyFun_gridH/gridV`,
`approxOn_polyFun_contourFunctional`, `differentiableAt_edgeCauchyIntegral`
(`HTGeometry.differentiableAt_intervalIntegral_of_bound`), `differentiableAt_contourFunctional`,
`grid_floor_le`, `grid_cell_of_lt`, `contourFunctional_eq_of_mem` (identity on every point of K
via the closure of the open floor square and `tendsto_nhds_unique`).

Consumers (RHTower): `ZetaVoroninUniversalityOnConnectedComplementCompacts`
(`exists_pos_density_zetaTargetReturnSet_of_isCompact_of_isPreconnected_compl`: K compact in the
strip with connected complement, g analytic nonvanishing on a simply connected open U ⊇ K),
`ZetaJointValueDensenessAtFinitelyManyPoints` (`exists_pos_density_forall_norm_zeta_sub_lt`).

Open: Mergelyan (continuous on K, analytic inside) — the textbook Voronin hypothesis.
