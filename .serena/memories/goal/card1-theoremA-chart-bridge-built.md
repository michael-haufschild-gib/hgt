# Card 1 (fixed-shell angular dephasing) — Theorem A after the chart bridge

Status 2026-08-19. All modules under `formal/GaloisForLFunctions/HTGeometry/`, axiom-clean.

## The chain, now complete up to one bookkeeping step
1. **Lemma A1 base** — `BellEndpointCompleteBasis.exists_endpointComplete_twoQubit_witness`
   (maximally entangled basis is endpoint complete; `reducedTransition ψ φ = reshape φ · (reshape ψ)ᴴ`).
2. **Lemma A2 unconditional** — `LocalExtensionQuadraticRateFlatCollapse.
   localExtension_quadraticRate_eq_zero_unconditional` (slice form, over `A × Bool`).
3. **Slice rate shape** — `LayerSliceQuadraticTrace.trace_sq_layerExtensionSlice`
   (`Tr H(z,g)² = Q₀(z) + g²Q_V`, no linear term) and
   `trace_sq_layerCrossPerturbation_ne_zero` (`Q_V ≠ 0` for a nonzero Hermitian channel).
4. **The chart slice** — `SelectedLayerSliceData` + `exists_selectedLayerSliceData`.
   NOTE: the pre-existing `SelectedLayerAnalyticRelationWitness` bakes the *linear* relation in as a
   field, so it cannot be reused for a quadratic one; the new slice carries only the geometry and
   is phrased against `C.branch i (selectedPairChartPoint …)` so chart identities restrict.
5. **Chart rigidity** — `ChartQuadraticRateEscape.chart_quadraticRate_eq_zero` /
   `exists_chart_quadraticRate_ne`. Identifications: `boolShift z b = if b then -(z/2) else z/2`,
   `layeredEnergy E (boolShift z) = layerSplitEnergy E z`,
   `selectedPairShiftLine (boolShift z₀) false true z = boolShift z`,
   `selectedLayerCoupling M false true = layerCrossPerturbation M`.
6. **`(14)`, the labeling orbit** — `ChartQuadraticRateOrbitEscape.exists_chartQuadraticOrbit_ne_zero`.
   Formed with the CARD's rate `κ Tr(H²)`, NOT `κ ∑ λ²` — that is what avoids the second Newton
   identity (a real mathlib gap). Each factor is the relation of `c ∘ π⁻¹`; chart rigidity refutes
   it; `exists_eqOn_zero_of_finsetProd_eqOn_zero` finishes.
7. **Globalisation to real parameters** (already built, constant *and* variable rate):
   `VariableRateMatrixObstruction`, `VariableRateAnalyticEscape`, `LabelOrbitPacketEscape`,
   `SymmetricDescentBaseChange` (`map_esymmAlgEquiv_symm` — the mathlib naturality gap).

## The single remaining step
Match, in ONE parameter space, the dense/residual maximally-projective set
(`PhysicallyRealizedTensorTreeSystem.tracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`,
giving `hE`, `hgap` via `MaximallyProjectiveEnergy.injective` and
`maximallyProjectiveEnergy_orientedGap_injective`) with the OPEN endpoint-completeness condition
(`eventually_forall_layerReducedTransition_ne_zero`, giving `hM`), and pick a point in the
intersection; `hbase` (simplicity of `layeredEnergy E (boolShift z₀)`) is then a finite-avoidance
choice of `z₀`. A nonempty open set meets a dense set — two lines once both are in the same space.

## Traps
- `set X := … with h` REWRITES THE TYPES OF EXISTING HYPOTHESES, so a chart `C : … E …` becomes a
  new `C` and old data (`D : … C✝ …`) no longer matches. Do not `set` anything that occurs in the
  type of a structure already in context.
- `Matrix ρ ρ ℂ` has no norm by default: `open scoped Matrix.Norms.Elementwise`.
- `AnalyticAt.comp` mis-unifies for entry projections; use `hentry.fun_comp_of_eq hmat rfl`.
