# Card: gaussian-radial-observer-spectral-action-law — formalization progress

Card: `docs/drafts/pipeline/2-fully-proven/gaussian-radial-observer-spectral-action-law.md`
(its "Formalization gate" section now carries the full mapping table).
Parent scalar layer: `HTGeometry/GaussianSpectralPacketActionLaw.lean`.

## DONE — eqs (2),(3),(5),(6),(7),(8),(9),(10)
All unconditional; axioms = propext/Classical.choice/Quot.sound; umbrella builds.

| Module | Key declarations |
|---|---|
| `GaussianRadialLaw.lean` | `measure_pi_gaussianReal_eq_withDensity`, `map_withDensity_measurableEquiv`, `euclideanGaussianDensityReal`, `stdGaussian_eq_withDensity` |
| `GaussianRadialPolarLaw.lean` | `gaussianRadialDensity`, `gaussian_polar_constant`, `integral_stdGaussian_fun_norm` |
| `GaussianRadialActionKernel.lean` | `radialActionKernel`, `radialActionKernel_eq_integral_stdGaussian`, `radialActionKernel_zero`, `tendsto_radialActionKernel_cocompact` |
| `GaussianRadialSpectralPacket.lean` | `radialSpectralPacket`, `integral_radialSpectralPacket`, `tendsto_integral_radialSpectralPacket_atTop`, `tendsto_mul_atTop_cocompact` |
| `ReplicaReporterSpectralExpansion.lean` | `outerProduct`, `replicaReporter`, `replicaDetuning`, `replicaCoefficient`, `replicaReporter_spectral_expansion`, `integral_replicaReporter_radial`, `tendsto_integral_replicaReporter_radial_atTop`, `bohrMean_replicaReporter`, `tendsto_integral_replicaReporter_radial_bohrMean` |
| `GaussianRadialAngularMixture.lean` | `norm_radialActionKernel_le_one`, `continuous_radialActionKernel`, `tendsto_integral_angularMixture`, `tendsto_integral_replicaReporter_angularMixture` |
| `GaussianRadialCompletionLaw.lean` | `trigPolyChar_eq_radialSpectralPacket`, `tendsto_integral_trigPolyChar_radial`, `integrable_comp_norm_of_bounded`, `tendsto_integral_radial_bohrMean`, `tendsto_integral_radial_bohrMean_angularMixture` |

Also `quditStringOf_sum_family` added to `FiniteQuditHermitianStringBasis.lean`.
All wired into `GaloisForLFunctions/HTGeometry.lean`.

## Technical facts worth remembering
- mathlib has NO density of `stdGaussian` vs Lebesgue and NO lintegral-Fubini for
  `Measure.pi`; the route is `Measure.pi_eq` + `Measure.restrict_pi_pi` +
  `integral_fintype_prod_eq_prod` + `ofReal_integral_eq_lintegral_ofReal`.
- `MeasureTheory.integral_fun_norm_addHaar` (HaarToSphere) makes the polar law cheap.
- `Real.tendsto_integral_exp_smul_cocompact` needs no integrability hypothesis;
  rescale frequency by 2π and use `cocompact_eq_atBot_atTop`.
- `Matrix (Fin k → Fin D)` IS the k-fold tensor power ⇒ reuse `quditStringOf`.
- Corpus Bohr layer used: `bohrMean`, `bohrMean_sub`, `bohrMean_le_bohrMean`,
  `norm_bohrMean_le_bohrMean_norm`, `bohrMean_const_real`,
  `exists_bound_of_isBohrAlmostPeriodic`, `expChar`/`bohrMean_sum_expChar`
  (`KroneckerWeylDensity`), `exists_trigPoly_spectrum_approx`
  (`BohrBochnerFejerApprox`).  NOTE: `IsBohrAlmostPeriodic` lives in the ROOT
  namespace `HTGeometry`, not `GaloisForLFunctions.HTGeometry`.

## REMAINING
1. eq (4): assemble `μ_∞` as a Borel measure on projective state space (Riesz)
   and deduce the continuity-set/portmanteau statement.
2. Identify `∫_{G_ω} … dν_ω` (Haar on the compact monothetic closure) with
   `bohrMean` — construct `G_ω` and its Haar measure; corpus has
   `CompletedObserverTimeTorus.lean` (`orbitClosureHaar`) as the starting point.
3. Bridge lemma: continuous `F` composed with the a.p. curve is a.p. and
   Bochner–Fejér approximable (feeds `tendsto_integral_radial_bohrMean`).
