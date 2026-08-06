# Card: gaussian-radial-observer-spectral-action-law — formalization progress

Card: `docs/drafts/pipeline/2-fully-proven/gaussian-radial-observer-spectral-action-law.md`
(its "Formalization gate" section carries the full equation→declaration table).

## DONE — eqs (1),(2),(3),(4),(5),(6),(7),(8),(9),(10)
All unconditional; axioms = propext/Classical.choice/Quot.sound; umbrella builds.

| Module | Key declarations |
|---|---|
| `GaussianRadialLaw.lean` | `measure_pi_gaussianReal_eq_withDensity`, `map_withDensity_measurableEquiv`, `euclideanGaussianDensityReal`, `stdGaussian_eq_withDensity` |
| `GaussianRadialPolarLaw.lean` | `gaussianRadialDensity`, `gaussian_polar_constant`, `integral_stdGaussian_fun_norm` |
| `GaussianRadialActionKernel.lean` | `radialActionKernel`, `radialActionKernel_eq_integral_stdGaussian`, `radialActionKernel_zero`, `tendsto_radialActionKernel_cocompact` |
| `GaussianRadialSpectralPacket.lean` | `radialSpectralPacket`, `integral_radialSpectralPacket`, `tendsto_integral_radialSpectralPacket_atTop`, `tendsto_mul_atTop_cocompact` |
| `ReplicaReporterSpectralExpansion.lean` | `outerProduct`, `replicaReporter`, `replicaDetuning`, `replicaCoefficient`, `replicaReporter_spectral_expansion`, `integral_replicaReporter_radial`, `tendsto_integral_replicaReporter_radial_atTop`, `bohrMean_replicaReporter`, `tendsto_integral_replicaReporter_radial_bohrMean` |
| `GaussianRadialAngularMixture.lean` | `norm_radialActionKernel_le_one`, `continuous_radialActionKernel`, `tendsto_integral_angularMixture`, `tendsto_integral_replicaReporter_angularMixture` |
| `GaussianRadialCompletionLaw.lean` | `tendsto_integral_trigPolyChar_radial`, `tendsto_integral_radial_bohrMean`, `tendsto_integral_radial_bohrMean_angularMixture` |
| `GaussianRadialContinuousReporter.lean` | `exists_trigPolyChar_approx_of_isBohrAlmostPeriodic`, `tendsto_integral_radial_bohrMean_of_almostPeriodic`, `isBohrAlmostPeriodic_finsetSum`, `isBohrAlmostPeriodic_comp_of_range_subset`, `isBohrAlmostPeriodic_smul_const`, `spectralStateCurve`, `isBohrAlmostPeriodic_spectralStateCurve`, `tendsto_integral_radial_bohrMean_continuous_reporter` |
| `GaussianRadialEndpointLaw.lean` | `tendsto_integral_radial_bohrMean_real`, `endpointLaw`, `endpointProbabilityLaw`, `integral_endpointLaw`, `tendsto_endpointProbabilityLaw`, `tendsto_measure_endpointLaw_of_null_frontier` |

Also `quditStringOf_sum_family` in `FiniteQuditHermitianStringBasis.lean`.
All wired into `GaloisForLFunctions/HTGeometry.lean`.

## Technical facts
- mathlib has NO density of `stdGaussian` vs Lebesgue and NO lintegral-Fubini for
  `Measure.pi`; route = `Measure.pi_eq` + `Measure.restrict_pi_pi` +
  `integral_fintype_prod_eq_prod` + `ofReal_integral_eq_lintegral_ofReal`.
- `integral_fun_norm_addHaar` (HaarToSphere) makes the polar law cheap.
- `Real.tendsto_integral_exp_smul_cocompact` needs no integrability hypothesis.
- `Matrix (Fin k → Fin D)` IS the k-fold tensor power ⇒ reuse `quditStringOf`.
- `IsBohrAlmostPeriodic` lives in the ROOT namespace `HTGeometry`.
- Corpus Bohr assets used: `bohrMean`, `bohrMean_sub`, `bohrMean_le_bohrMean`,
  `norm_bohrMean_le_bohrMean_norm`, `bohrMean_const_real`, `bohrMean_ofReal`,
  `exists_bound_of_isBohrAlmostPeriodic`, `isBohrAlmostPeriodic_add/_neg/_const`,
  `uniformContinuous_of_isBohrAlmostPeriodic`,
  `hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic`,
  `exists_trigPoly_spectrum_approx` (BohrBochnerFejerApprox),
  `expChar`/`bohrMean_sum_expChar`/`isBohrAlmostPeriodic_expChar` (KroneckerWeylDensity).
- mathlib portmanteau: `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`,
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.
- `integral_map` names the map `φ`, the integrand `f`.

## REMAINING (single gap)
Existence half of "there is a unique probability measure `μ_∞`":
build `μ_∞` from the positive normalized functional `F ↦ bohrMean (F ∘ curve)`
by Riesz representation (mathlib `RieszMarkovKakutani`), or equivalently as
`Haar(T).map Ψ` where `T` is the closure of the frequency torus orbit and
`Ψ z = ∑ z_i • w_i`.  The second route would simultaneously close the
`∫_{G_ω} … dν_ω = bohrMean` identification; corpus starting points are
`CompletedObserverTimeTorus.lean` (`orbitClosureHaar`,
`orbitClosureHaar_mFourier_integral`) and `BohrOrbitHaarLaw.lean`.
Uniqueness of `μ_∞` is immediate from (3).
