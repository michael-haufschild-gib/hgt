# Linear energy law for hidden quantum futures

- **ID:** local-horizon-quantum-return-law
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Date:** 2026-07-28
- **Article:** `local-horizon-quantum-return-law-main.tex`

## Scientific question

What asymptotic energy--time scale is necessary and sufficient for a
nonvanishing future response to remain hidden beyond an increasing exact
local or response record?

## Answer

Linear scale is necessary and sufficient.

### Universal necessity

For every complete complex normed space, every bounded generators \(G,K\),
every vector \(x\), every continuous scalar probe \(\ell\), and every
\(z\in\mathbb C\), equality
\[
 \ell(G^m x)=\ell(K^m x),\qquad 0\le m<N,
\]
with \(\|G\|,\|K\|\le\Lambda\), forces
\[
 |\ell(e^{zG}x)-\ell(e^{zK}x)|
 \le
 2\|\ell\|\|x\|e^{\|z\|\Lambda}
 \frac{(\|z\|\Lambda)^N}{N!}.
\]
If \(\|z\|\Lambda\le N/(3e)\), the right side is at most
\[
 2\|\ell\|\|x\|(e/3)^N.
\]
Therefore any fixed positive response gap along \(N\to\infty\) eventually
requires
\[
 \|z\|\Lambda>N/(3e).
\]

This includes finite and bounded infinite-dimensional generators,
self-adjoint, non-normal and dissipative linear descriptions. It assumes
only the scalar response prefix, not equality of Krylov vectors.

### Spatial quantum necessity

For a self-adjoint nearest-neighbour path, exact endpoint-local agreement
through radius \(R\) fixes endpoint power moments through \(2R+2\). Hence
for any common real energy origin \(c\) with
\(\|J-cI\|,\|K-cI\|\le\Lambda\),
\[
 |P_J(t)-P_K(t)|
 \le
 4e^{\Lambda|t|}
 \frac{(\Lambda|t|)^{2R+3}}{(2R+3)!}.
\]
If a fixed positive target gap persists along \(R\to\infty\), then eventually
\[
 \Lambda_R|T|>\frac{2R+3}{3e}.
\]

### Matching achievability

For every \(T>0\), \(0\le H<T\) and \(\delta>0\), one integer
\(a=a(H/T,\delta)\) works for every radius \(R\). At that radius there is one
finite isospectral self-adjoint nearest-neighbour family, one endpoint
preparation and return test, one exactly common local Hamiltonian record,
and \(\delta\)-close return probabilities throughout \([-H,H]\), whose
target-time compatible return set is exactly \([0,1]\). Every member obeys
\[
 \left\|J_p-\frac{\pi n_R}{2T}I\right\|
 \le\frac{\pi(4R+2a+5)}{2T}.
\]

Thus complete hidden-future capacity has exact asymptotic order
\[
 \Lambda_R T=\Theta(R).
\]

## Formal closure

### `LocalHamiltonianCausalHorizonLaw.lean`

- `endpointPowerMoment_eq_of_local`
- `localCausalHorizon_amplitude_bound`
- `localCausalHorizon_probability_bound`
- `localCausalHorizon_probability_bound_gauge`
- `energyGaugeShift_returnProbability`
- `factorialTail_linear_bound_exp_three`
- `persistentCofinalSeparation_forces_linear_energyTime`
- `persistentCofinalSeparation_forces_linear_centeredEnergyTime`
- `finiteIndexDiagonalHamiltonian_norm_le`
- `scaledClockHamiltonian_norm_le`
- `fixedProtocolHamiltonian_norm_le`
- `fixedProtocolHamiltonian_centered_norm_le`
- `exists_localCompatibleFutureSet_eq_Icc`

### `OptimalLocalFutureEnergyLaw.lean`

- `exists_uniformWindowExponent_endpointN_record`
- `FixedEndpointPathModel.norm_le`
- `finiteIndexDiagonal_exp_apply`
- `scaledClock_exp_interpolatedClock`
- `fixedProtocol_exp_apply`
- `FixedEndpointPathModel.stateAt_eq_exp`
- `FixedEndpointPathModel.returnProbability_eq_exponential`
- `exists_linearEnergy_completeLocalFutureSet`

The exponential bridge proves constructed return probabilities are literally
the operator-exponential probabilities used by the converse.

### `UniversalBoundedGeneratorCausalHorizonLaw.lean`

- `boundedGeneratorOrbit_difference_norm_le`
- `boundedGeneratorResponse_series_hasSum`
- `boundedGeneratorResponse_difference_eq_tail_of_prefix`
- `boundedGeneratorResponse_difference_norm_le_of_prefix`
- `boundedGeneratorResponse_linear_bound`
- `persistentBoundedGeneratorSeparation_forces_linear_scale`

### Infinite and spectral dependencies

- `MaximalRealDiagonalSelfAdjoint.lean`
- `InfinitePhaseLadderLocalHorizonLaw.lean`
- `InfinitePhaseLadderMomentTransfer.lean`
- `SpectralMeasureExactReturnClassification.lean`

The populated countably infinite witness is maximal self-adjoint and
unbounded. The universal lower law covers all bounded infinite-dimensional
generators. Their conjunction identifies unbounded norm as the required
cofinal resource.

## Novelty boundary

Classical ingredients:

- operator-exponential remainders;
- Stirling bounds;
- Krylov/Jacobi tridiagonalization;
- truncated moment transfer;
- Lieb--Robinson locality;
- quantum speed limits.

Closest conceptual collision:

- Manos, Weilenmann and Navascués, *Timed demolition measurements*,
  arXiv:2507.06912v2 (2026), proves broad extrapolation fog banks and
  superexponential precision requirements.

Surviving new conjunction:

1. exact scalar-record causal theorem for every bounded generator and probe;
2. explicit linear energy--parameter necessity from persistent response;
3. exact spatial conversion \(N=2R+3\) for local path returns;
4. one fixed-protocol, isospectral, future-complete nearest-neighbour family;
5. uniform linear upper energy bound;
6. matched \(\Theta(R)\) necessary-and-sufficient resource law;
7. bounded infinite-dimensional lower law plus exact unbounded populated
   infinite saturation.

Searches on 2026-07-28 found no source stating this matched law. Search
cannot establish priority.

## Claims excluded

- no indeterminism;
- no superluminal signalling;
- no experimental demonstration or device feasibility claim;
- no interacting-QFT, gravity, black-hole, inflation or cosmology claim;
- no claim for unbounded generators in the universal causal theorem;
- no claim that the displayed constants are best constants.

## Publication gate

Remaining work:

1. complete claim trace from every mathematical Article sentence to a closed
   theorem;
2. conduct hostile specialist and Nature editorial reviews against novelty,
   outstanding importance, interdisciplinary reach, arresting character,
   immediate implications and far-reaching implications;
3. repair every valid objection;
4. run formal lint, individual foreground Lean audits and final module build;
5. visually inspect final PDF.

Promotion is forbidden until hostile review recommends publication rather
than rejection.
