# Heat flow

Place new Riemann heat-flow modules here: local growth and factorization,
Gaussian transport, zero persistence and counting, collisions, and energy
evolution. Import modules as `GaloisForLFunctions.RHTower.Heat.<Module>`.
Declaration namespaces remain unchanged.

| Topic | Modules |
|---|---|
| Local source estimates | `HeatEulerAnchor`, `HeatLocalGrowth`, `HeatLocalZeroDensity`, `HeatLocalCofactor`, `HeatRelativeGlobalBounds` |
| Gaussian transport | `HeatReverseGaussian`, `HeatGaussianQuadraticError`, `HeatZeroFreeWindow` |
| Persistence and counting | `HeatMeanFieldPersistence`, `HeatMeanFieldZeroDensity`, `HeatShrinkingWindow`, `HeatZeroDisplacement`, `HeatUniformDepthZeroDensity` |
| Collisions and energy | `HeatExteriorForce`, `HeatForwardSimpleZeros`, `LocalizedHeatPairForce`, `HeatZeroSumContinuity` |

`HeatLocalizedEnergyEvolution.lean` is unfinished research, preserved from
the paused proof task. It is not exported by the umbrella. Its open work
is recorded in the [energy-flux card](../../../../docs/drafts/pipeline/1-in-progress/wd-heat-localized-energy-flux.md).

Finished modules are imported directly by
[`../../RHTower.lean`](../../RHTower.lean).
Historical heat modules remain at their existing paths until a separate
migration. Reusable analytic tools remain in `HTGeometry/`. New Ward/source
current modules belong in [`../WD/`](../WD/README.md).
