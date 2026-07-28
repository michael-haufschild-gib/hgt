# Claim trace — Energy sets how far a quantum future can be hidden

Article: `local-horizon-quantum-return-law-main.tex`  
Audit date: 2026-07-28

Rule: every mathematical statement in Article must reduce to declarations
below. Literature, motivation and explicit scope exclusions are not theorem
claims.

## Universal bounded-generator law

| Article claim | Formal declaration |
|---|---|
| \(e^{zG}x\) has the stated absolutely convergent power series on every complete complex normed space | `boundedGeneratorOrbit_series_hasSum` |
| Every continuous scalar response has coefficients \(z^m\ell(G^m x)/m!\) | `boundedGeneratorResponse_series_hasSum` |
| Equality of first \(N\) scalar response coefficients cancels the series head exactly | `boundedGeneratorResponse_difference_eq_tail_of_prefix` |
| Every inexact scalar response jet splits exactly into a finite observed head and complete unobserved tail | `boundedGeneratorResponse_difference_eq_prefix_add_tail` |
| \(\|(G^m)x\|\le\|G\|^m\|x\|\) | `boundedGenerator_pow_apply_norm_le` |
| Difference of two order-\(m\) Krylov vectors is at most \(2\Lambda^m\|x\|\) | `boundedGenerator_pow_sub_norm_le` |
| Universal factorial scalar-response bound | `boundedGeneratorResponse_difference_norm_le_of_prefix` |
| Universal exact exponential-tail response bound | `boundedGeneratorResponse_difference_norm_le_of_prefix_exactTail` |
| Arbitrary coefficient-error profile contributes the exact finite weighted calibration sum | `boundedGeneratorResponse_difference_norm_le_of_approx_prefix` |
| Full-vector orbit bound, if used | `boundedGeneratorOrbit_difference_norm_le` |
| Under \(\|z\|\Lambda\le N/(3e)\), factorial tail is bounded by \((e/3)^N\) | `factorialTail_linear_bound_exp_three`, `factorialTail_le_exp_three_pow` |
| Geometric scalar-response bound below linear scale | `boundedGeneratorResponse_linear_bound` |
| Persistent response separation along \(N\to\infty\) eventually forces \(\|z\|\Lambda>N/(3e)\) | `persistentBoundedGeneratorSeparation_forces_linear_scale` |
| At \(\|z\|\Lambda\le N/e\), exact exponential tail is at most \(2/\sqrt{2\pi N}\) | `real_exp_sub_sum_le_twice_first_at_critical`, `factorial_first_term_le_inv_sqrt_at_critical`, `real_exp_sub_sum_le_inv_sqrt_critical` |
| Exact-prefix response gap at the \(N/e\) boundary is at most \(4\|\ell\|\|x\|/\sqrt{2\pi N}\) | `boundedGeneratorResponse_critical_bound` |
| Inexact-prefix response gap at the boundary is calibration sum plus \(4\|\ell\|\|x\|/\sqrt{2\pi N}\) | `boundedGeneratorResponse_approx_prefix_critical_bound` |
| Persistent response separation eventually forces \(\|z\|\Lambda>N/e\) | `persistentBoundedGeneratorSeparation_forces_critical_scale` |
| Result has no finite-dimensional, inner-product, self-adjointness or normality premise | exact type and hypotheses of the declarations above |

## Nearest-neighbour spatial conversion

| Article claim | Formal declaration |
|---|---|
| Endpoint Krylov iterate is supported inside distance equal to iterate order | `endpointIterate_supported` |
| Local matrix equality through radius \(R\) fixes iterates through \(R+1\) | `endpointIterate_eq_of_local` |
| Self-adjointness splits endpoint moment order \(a+b\) into inner product of iterates \(a,b\) | `inner_endpointIterate_eq_powerMoment_add` |
| Radius-\(R\) equality fixes endpoint moments through \(2R+2\) | `endpointPowerMoment_eq_of_local` |
| Power-series return amplitude equals endpoint matrix element of standard operator exponential | `endpointExponentialAmplitude_eq_inner_exp` |
| Radius-\(R\) amplitude difference obeys dimension-free factorial bound | `localCausalHorizon_amplitude_bound` |
| Radius-\(R\) probability difference obeys \(4e^{\Lambda|t|}(\Lambda|t|)^{2R+3}/(2R+3)!\) | `localCausalHorizon_probability_bound` |
| Persistent fixed probability gap forces \(\Lambda_R|T|>(2R+3)/(3e)\) eventually | `persistentCofinalSeparation_forces_linear_energyTime` |
| Common real energy-origin shifts preserve nearest-neighbour structure, self-adjointness and local equality | `energyGaugeShift_nearestNeighbor`, `energyGaugeShift_selfAdjoint`, `energyGaugeShift_local` |
| Common real energy-origin shifts preserve return probability exactly | `energyGaugeShift_exp_apply`, `energyGaugeShift_returnProbability` |
| Probability causal bound holds for any common centred norm certificate | `localCausalHorizon_probability_bound_gauge` |
| Persistent fixed gap forces the same linear law for centred, gauge-invariant norm radii | `persistentCofinalSeparation_forces_linear_centeredEnergyTime` |
| At centred action \(\Lambda|t|\le(2R+3)/e\), probability gap is at most \(8/\sqrt{2\pi(2R+3)}\) | `localCausalHorizon_probability_bound_critical_gauge` |
| Persistent fixed probability gap eventually forces \(\Lambda_R|T|>(2R+3)/e\) | `persistentCofinalSeparation_forces_critical_centeredEnergyTime` |
| Noisy centred moment protocol has probability budget \(2\sum_{m<N}|t|^m\eta_m/m!+8/\sqrt{2\pi N}\) | `boundedGeneratorResponse_approx_prefix_critical_bound`, `endpointExponentialAmplitude_eq_inner_exp`, `energyGaugeShift_returnProbability`, `normSq_sub_normSq_abs_le` |

## Exact complete-future construction

| Article claim | Formal declaration |
|---|---|
| Parity-conditioned and full binomial measures match every energy moment below spectral depth | `parity_energyMoment_eq_full`, `interpolated_energyMoment_eq_full`, `scaled_interpolated_energyMoment_eq` |
| Interpolated target return is exactly \(p\) at parameter \(\sqrt p\) | `scaledInterpolatedProbability_target` plus `Real.sq_sqrt` in `exists_uniformWindowExponent_endpointN_record` |
| Strict pre-target interval discrepancy decays as a sine power | `amplitude_difference_window_bound`, `interpolatedAmplitude_difference_norm`, `interpolated_probability_difference_le_amplitude` |
| One additive exponent \(a(H/T,\delta)\) works for every moment order | `exists_uniformWindowExponent_endpointN_record` |
| Canonical Krylov realization is nearest-neighbour | `canonicalKrylovPathHamiltonian_nearestNeighbor`, `exists_canonicalInterpolatedPathPhase` |
| Matching moments force exact canonical local entries | `canonicalKrylovCompression_local_eq_of_moments_cross_of_sizes`, `endpointLocalMatrixEq_of_prefix` |
| Every member is self-adjoint | self-adjoint clauses in `exists_canonicalInterpolatedPathPhase` and `exists_linearEnergy_completeLocalFutureSet` |
| Every member is unitarily intertwined with one common diagonal Hamiltonian and hence isospectral including multiplicity | intertwining clauses in `exists_linearEnergy_completeLocalFutureSet` |
| Constructed trajectory is literal standard operator-exponential evolution | `finiteIndexDiagonal_exp_apply`, `scaledClock_exp_interpolatedClock`, `fixedProtocol_exp_apply`, `FixedEndpointPathModel.stateAt_eq_exp` |
| Constructed return probability is literal endpoint exponential probability used in converse | `FixedEndpointPathModel.returnProbability_eq_exponential` |
| Midpoint-centred diagonal energy norm is at most \(\pi n/(2T)\) | `centeredAngularEnergy_abs_le`, `centeredScaledClockHamiltonian_norm_le` |
| Unitary fixed-protocol conjugate has same centred norm ceiling | `fixedProtocolHamiltonian_centered_norm_le` |
| Dimension index obeys \(n\le4R+2a+5\) | dimension clause of `exists_linearEnergy_completeLocalFutureSet` |
| One norm-bounded local record has compatible target set exactly \([0,1]\) | `exists_linearEnergy_completeLocalFutureSet` |
| One dimension, baseline and spectrum work simultaneously for all \(p\in[0,1]\) | quantifier order and set equality in `exists_linearEnergy_completeLocalFutureSet` |
| Every \(p<1\) canonical representative has every adjacent bond nonzero | `finiteKrylovBasis_forward_entry_ne_zero`, `finiteKrylov_conjugate_forwardConnected` |
| Constructed \(p=1\) representative has a zero bond beyond common prefix | endpoint block clauses in `LocalHorizonQuantumReturnLaw.lean` and `endpoint_paritySupport_forces_path_disconnection` |
| Every tridiagonal fixed-protocol perfect-return realization at the parity endpoint must contain a zero bond | `endpoint_paritySupport_forces_path_disconnection` |
| In every fixed particle-number sector, second quantization of every fixed-protocol member has one common complete subset-sum spectrum | `fixedProtocol_intrinsicFermionicSpectrum`, `fixedProtocol_fullFermionicSpectrum` |

## Exact asymptotic law

| Article claim | Formal basis |
|---|---|
| Every future-complete record contains a unit-gap pair | set equality to `Set.Icc (0 : ℝ) 1` in `exists_linearEnergy_completeLocalFutureSet`; endpoint members \(0,1\) |
| Such pairs require \(\Lambda_RT>(2R+3)/e\) eventually | `persistentCofinalSeparation_forces_critical_centeredEnergyTime` |
| Future-complete records exist with centred \(\Lambda_RT\le\frac{\pi}{2}(4R+2a+5)\) | `exists_linearEnergy_completeLocalFutureSet` |
| Necessary and sufficient order is \(\Theta(R)\) at fixed \(H/T,\delta\) | conjunction of preceding lower and upper declarations |
| Restoring physical units gives \(\Lambda T/\hbar\) | dimensional restoration of the formally dimensionless parameter; no added mathematical content |

## Infinite boundary

| Article claim | Formal declaration |
|---|---|
| Real coordinate multiplication on its maximal square-summability domain is self-adjoint | `maximalRealDiagonal_selfAdjoint` |
| Infinite phase ladder uses countably many positive populated weights and injective energies | clauses of `exists_infiniteLocalHorizonWitness` |
| Infinite Hamiltonian is norm-unbounded | clause of `exists_infiniteLocalHorizonWitness` |
| Infinite return amplitude factorizes into finite amplitude times phase-ladder factor | `infiniteAngularInterpolatedAmplitude_eq_mul` and associated factorization declarations in `InfinitePhaseLadderLocalHorizonLaw.lean` |
| Ladder factor has modulus at most one and equals one at target | clauses used in `exists_infiniteLocalHorizonWitness` |
| Lifted moments are triangular combinations of base moments | `phaseLadderMoment_decomposition` |
| Every requested finite matched moment block survives | `infiniteAngularInterpolated_moments_eq` |
| Every finite witness has an exact populated countably infinite unbounded lift | `exists_infiniteLocalHorizonWitness` |

## Physical realization and falsification

| Article claim | Formal declaration |
|---|---|
| Every self-adjoint nearest-neighbour one-particle Hamiltonian is exact one-excitation block of Hermitian particle-number-preserving local XX occupation matrix | `localSpinChain_singleExcitation_block` |
| Complete future interval transfers to one-excitation local spin-chain setting | `one_fixed_local_spin_chain_every_future_probability` |
| Violation of probability bound contradicts conjunction of its hypotheses | direct contrapositive of `localCausalHorizon_probability_bound` |

## Explicit nonclaims

No Article theorem asserts:

- indeterminism or randomness of individual outcomes;
- superluminal signalling;
- experimental realization or device feasibility;
- best numerical constants;
- interacting quantum field theory;
- gravity, black holes, inflation or cosmology;
- causal bounds for unbounded generators.

These exclusions must remain in Article.
