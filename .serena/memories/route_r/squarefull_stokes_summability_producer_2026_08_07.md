# Route R squarefull Stokes summability producer (2026-08-07)

New formal module: `RHTower/RouteRSquarefullStokesSummabilityProducer.lean`; imported by `RHTower.lean`.

Scientific delta: replace equality of singular squarefull-tail probabilities by normality of one explicit primewise diagonal Stokes boundary

`b_sigma(p) = p^(-2 sigma)/(1+p^(-sigma)) - p^(-2(1-sigma))/(1+p^(-(1-sigma)))`.

Proved unconditionally:
- `diagonalActivationMeasure_squarefull_toReal_eq_localMass`: each face is the actual local Euler activation probability of valuation depth >=2.
- `routeREulerGammaSquarefullStokesCoefficient_reflection`: reflection reverses sign.
- `summable_routeREulerGammaSquarefullStokesCoefficient_iff`: for `0<sigma<1`, `Summable b_sigma <-> sigma=1/2`.
- `routeREulerGammaSquarefullStokesSummable_iff_tailBalanced` and `_iff_port_eq_zero`.
- `routeRTwoThreeGammaArithmeticCorona_globalization_iff_squarefullStokesSummable`.

Exact remaining producer is `forall rho, RouteREulerGammaSquarefullStokesSummable rho`, i.e. prove l1/trace-class normality of this explicit diagonal coefficient from pre-divisor rational-adelic/Euler-Gamma Stokes structure.

Audit: foreground `lake env lean` passed; module-only `lake build` passed; axioms `[propext, Classical.choice, Quot.sound]`. Whole-tree lint failed only on four unrelated concurrent umbrella omissions: `ConstrainedProlateSpectralIdentification`, `ProlateFourierSignSectors`, `SlepianKernelScaledFubini`, `HTGeometry.SobolevWeightDecay`.

Conjecture loop: source Real marginal transport falsified; finite adelic tail coupling falsified; full hybrid current normal extension rejected because equivalent to balance; diagonal summability C4 survived and was formalized.

Card: `docs/drafts/pipeline/3-formalized/route-r-squarefull-stokes-summability-producer.md`. Related prior memory: `mem:route_r/squarefull_tail_gamma_cartier_index_2026_08_07`.