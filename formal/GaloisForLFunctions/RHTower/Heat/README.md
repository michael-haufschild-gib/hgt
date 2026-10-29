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
| Collisions and derivatives | `HeatExteriorForce`, `HeatForwardSimpleZeros`, `HeatLocalizedEnergyEvolution` |
| Localized dissipation | `LocalizedHeatPairForce`, `LocalizedHeatPacketFlux`, `HeatZeroSumContinuity`, `HeatLocalizedZeroObservables`, `HeatLocalizedEnergyDissipation` |

`HeatLocalizedEnergyDissipation` controls the actual multiplicity-weighted energy
through collisions, including heat time zero. For a nonnegative unit-window
cutoff bounded by W, with derivative bounded by V and Lipschitz constant M,

`E_w(b) − E_w(a) + 2∫ N_w ≤ (2M+2V+4W) C log X ∫ E_outer`

when `0≤a≤b≤1/8` and `b log X≤1`, for sufficiently large X. Here N_w is the
full weighted nonreal count; the outer cutoff equals one on the radius-two
force packet. A companion theorem bounds the upper right slope at every
admissible initial time. Uniform small-time nonreal counts remain open.

Finished modules are imported directly by
[`../../RHTower.lean`](../../RHTower.lean).
Historical heat modules remain at their existing paths until a separate
migration. Reusable analytic tools remain in `HTGeometry/`. New Ward/source
current modules belong in [`../WD/`](../WD/README.md).
