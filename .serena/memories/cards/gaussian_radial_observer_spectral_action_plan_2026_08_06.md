# Card gaussian-radial-observer-spectral-action-law — FULLY FORMALIZED

Card moved to `docs/drafts/pipeline/3-formalized/gaussian-radial-observer-spectral-action-law.md`,
status `[LEAN-PROVED]`.  Every displayed equation (1)–(10) is closed
unconditionally (axioms = propext / Classical.choice / Quot.sound only), including
existence + uniqueness of `μ_∞` and the literal `G_ω`/Haar presentation.

## Modules (all wired into `GaloisForLFunctions/HTGeometry.lean`)

| Module | Content |
|---|---|
| `GaussianRadialLaw.lean` | density of `stdGaussian` vs Lebesgue: `measure_pi_gaussianReal_eq_withDensity`, `map_withDensity_measurableEquiv`, `stdGaussian_eq_withDensity` |
| `GaussianRadialPolarLaw.lean` | (2),(10): `gaussianRadialDensity`, `gaussian_polar_constant`, `integral_stdGaussian_fun_norm` |
| `GaussianRadialActionKernel.lean` | `ρ̂_m`: `radialActionKernel`, `radialActionKernel_zero`, `tendsto_radialActionKernel_cocompact` |
| `GaussianRadialSpectralPacket.lean` | (7),(8) packet form |
| `ReplicaReporterSpectralExpansion.lean` | (5),(6),(7),(8),(9) operator form + `bohrMean_replicaReporter` |
| `GaussianRadialAngularMixture.lean` | `continuous_radialActionKernel`, `tendsto_integral_angularMixture` |
| `GaussianRadialCompletionLaw.lean` | `tendsto_integral_radial_bohrMean` (+ angular mixture) |
| `GaussianRadialContinuousReporter.lean` | `spectralStateCurve`, its almost-periodicity, `tendsto_integral_radial_bohrMean_continuous_reporter` |
| `GaussianRadialEndpointLaw.lean` | (1),(4): `endpointLaw`, `tendsto_endpointProbabilityLaw`, `tendsto_measure_endpointLaw_of_null_frontier` |
| `GaussianRadialLimitLaw.lean` | tightness + Prokhorov: `exists_completedEndpointLaw`, `completedEndpointLaw_unique` |
| `CompletedTimeBohrMean.lean` | `G_ω`/Haar: `clockPhaseWindowLaw`, `integral_clockPhaseWindowLaw`, `tendsto_clockPhaseWindowLaw_orbitClosureHaar`, `torusStateMap`, `integral_orbitClosureHaar_eq_bohrMean` |
| `GaussianRadialCompletedOrbitLaw.lean` | (3) literal: `completedOrbitLaw`, `tendsto_endpointProbabilityLaw_completedOrbitLaw`, `exists_tendsto_endpointProbabilityLaw_completedOrbitLaw` |

Also `quditStringOf_sum_family` added to `FiniteQuditHermitianStringBasis.lean`.

## Reusable assets created
- Density of `ProbabilityTheory.stdGaussian` against Lebesgue (mathlib has none).
- `map_withDensity_measurableEquiv`.
- Gaussian polar disintegration and the chi density with the exact `2^{1-m/2}/Γ(m/2)` constant.
- Radial Fourier kernel with Riemann–Lebesgue decay and contraction/continuity.
- Vector-valued `isBohrAlmostPeriodic_finsetSum`, `isBohrAlmostPeriodic_comp_of_range_subset`,
  `isBohrAlmostPeriodic_smul_const`.
- Complex-valued weak convergence transfer `tendsto_integral_of_tendsto_probabilityMeasure`.
- One-sided-window clock-phase law + equidistribution (corpus previously had only
  the symmetric `finiteTorusPhaseProbabilityMeasure`).

## Traps to remember
- Corpus `UnitAddTorus` lemmas are universe-0 (`d : Type`), not `Type*`.
- `IsBohrAlmostPeriodic` lives in the ROOT namespace `HTGeometry`.
- `ProbabilityMeasure` is NOT a subtype: use `ProbabilityMeasure.toMeasure_injective`.
- `integral_map` names the map `φ`, the integrand `f`.
- mathlib has NO lintegral-Fubini for `Measure.pi`.
