# Route U Kelvin-Gamma two-chart scalar-renormalization no-go (2026-08-15)

Formalized leaf: `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaKelvinTwoChartNoGo.lean`.

Closed unconditional theorems:
- `routeUHardEdgeKelvinGammaInteriorChart_tendsto`: gamma rate at a*exp(-1) minus at a*exp(1) tends to -1.
- `routeUHardEdgeKelvinGammaPhysicalBoundaryChart_tendsto`: boundary difference plus log(a) tends to gammaHardyPhaseRate(1)+log(2*pi)/2.
- `not_exists_routeUHardEdgeKelvinGammaGlobalScalarRenormalization`: no arbitrary scalar r : R -> R makes both chart expressions plus r converge to finite limits; no regularity premise.

Proof input: `gammaHardyPhaseRate_sub_log_conductor_tendsto_zero`. Interior convergence forces r finite; boundary convergence forces r-log finite, hence r tends to +infinity.

Classification: analytic asymptotic is classical BRIDGE; source-specific theorem is terminal no-go for global scalar Gamma completion after source-matched Kelvin-Laplace detailed balance. It does not prove RH or sign polar/prime terms.

Open core: completed prime-polar correction must be chart-local/non-scalar, logarithmic charge 0 on interior Mellin chart and 1 at fixed physical boundary. Derive and cancel this from literal polar evaluation plus von Mangoldt Fourier cross source for one fixed false-RH carrier.

Card: `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/route-u-kelvin-gamma-two-chart-renormalization-no-go.md`. Frontier updated.

Audit: scratch and leaf compile via `lake env lean`; exact missing leaf oleans built directly; umbrella import wired but umbrella not built. Axiom audit: only propext, Classical.choice, Quot.sound. No task-owned Lean/lint process remains.

Related: `mem:route_u_prime_gamma_nyquist_flux_2026_08_09`, `mem:route_u_kelvin_mellin_phase_2026_08_15`, `mem:route_u_prime_gamma_disintegration_2026_08_08`.