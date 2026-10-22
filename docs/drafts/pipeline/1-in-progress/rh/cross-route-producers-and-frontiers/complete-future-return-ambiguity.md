# Complete future-return ambiguity

- **ID:** complete-future-return-ambiguity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** strengthened positive survivor of finite-window recurrence route

## Statement

For every \(m\in\mathbb N\), \(T>0\), \(0\le H<T\) and \(\delta>0\), one
fixed normalized pure state and fixed return projector admit nonnegative
self-adjoint Hamiltonians \(K_p\), simultaneously for every \(p\in[0,1]\),
such that all \(K_p\) are unitarily equivalent and:

1. fixed-state energy moments are identical through order \(m\);
2. survival probabilities lie within \(\delta\) of one baseline record
   on all of \([-H,H]\);
3. the survival probability of \(\psi_p\) at \(T\) is exactly \(p\).

The endpoint pair uses the minimum \(n+1\) distinct energy levels compatible
with nontrivial agreement of moments \(0,\ldots,n-1\).

## Construction

For \(j=0,\ldots,n\),
\[
q_j=2^{-n}{n\choose j},\qquad
r_j=q_j[1+(-1)^{n-j}],\qquad
w_{p,j}=(1-\sqrt p)q_j+\sqrt p\,r_j.
\]
Use angular energies \(E_{j,T}=\pi j/T\). Then
\[
A_p(t)=A_0(t)+\sqrt p
\left(\frac{e^{i\pi t/T}-1}{2}\right)^n,
\]
so
\[
P_p(T)=p,\qquad
|A_p(t)-A_0(t)|
=\sqrt p\,\left|\sin\frac{\pi t}{2T}\right|^n.
\]
Alternating binomial moments vanish below order \(n\). A square Vandermonde
system gives the support converse.

## Formal anchors

Module:
`formal/GaloisForLFunctions/RHTower/ParityConditionedForecastingInstability.lean`

- `angularEnergy_eq`
- `angularEnergy_nonneg`
- `scaledClockHamiltonian_selfAdjoint`
- `interpolatedClock_norm`
- `scaledInterpolatedClockAt_norm`
- `scaledInterpolatedClock_survivalAmplitude`
- `exists_unitary_fixedClock_to_interpolatedClock`
- `fixedProtocolHamiltonian_selfAdjoint`
- `fixedProtocolHamiltonian_intertwines`
- `fixedProtocol_energyMoment_eq_full`
- `one_fixed_return_protocol_every_future_probability`
- `finiteKrylovVector_linearIndependent`
- `finiteKrylovBasis_nearestNeighbor`
- `fixedProtocolHamiltonian_krylov_nearestNeighbor`
- `one_fixed_nearestNeighbor_chain_every_strict_future_probability`
- `interpolatedProbability_target`
- `scaled_interpolated_energyMoment_eq`
- `universal_every_future_return_probability`
- `one_record_compatible_with_every_future_probability`
- `parity_pair_attains_minimal_spectral_support`
- `every_forecaster_has_half_error`

Closed-endpoint nearest-neighbour module:
`formal/GaloisForLFunctions/RHTower/EndpointKrylovNearestNeighborRealization.lean`

- `endpointActiveWeight_pos`
- `endpointActiveWeight_sum`
- `endpointBlockBasis_nearestNeighbor`
- `endpointKrylovUnitary_fixedClock`
- `fixedProtocolHamiltonian_endpoint_nearestNeighbor`
- `one_fixed_nearestNeighbor_chain_every_future_probability`

Perfect-return path-rigidity module:
`formal/GaloisForLFunctions/RHTower/PerfectReturnPathRigidity.lean`

- `connected_nearestNeighbor_eigenvector_endpoint_ne_zero`
- `nearestNeighbor_endpointOrthogonal_eigenvector_forces_disconnection`
- `endpoint_paritySupport_forces_path_disconnection`
- `finiteKrylov_conjugate_forwardConnected`
- `endpoint_return_connectedness_dichotomy`

Permutation-invariant qubit module:
`formal/GaloisForLFunctions/RHTower/PermutationInvariantQubitClockRealization.lean`

- `symmetricOccupationWeight_sum`
- `symmetricOccupationKet_permutation_invariant`
- `uniformQubitFieldEnergy_eq_sum_onsite`
- `uniformQubitFieldEnergy_permutation_invariant`
- `symmetricInterpolatedQubit_survivalAmplitude`
- `symmetricOccupationKet_energyMoment`
- `one_uniform_qubit_field_every_future_probability`

Local occupation module:
`formal/GaloisForLFunctions/RHTower/FermionicSpinChainRealization.lean`

- `xxOccupationMatrix_isHermitian`
- `xxOccupationMatrix_eq_zero_of_card_ne`
- `localSpinChain_singleExcitation_block`
- `one_fixed_local_spin_chain_every_future_probability`

Intrinsic fermionic-sector module:
`formal/GaloisForLFunctions/RHTower/FermionicFockIsospectrality.lean`

- `secondQuantization`
- `secondQuantization_apply_ιMulti_eigen`
- `orderedFermionicSubsetEnergy_eq`
- `fixedProtocol_intrinsicFermionicSpectrum`
- `one_fixed_nearestNeighbor_freeFermion_every_future_probability`

Targeted foreground compilation passes. Final axiom, lint and umbrella-build
audits remain.

## Collision and significance audit

Manos–Weilenmann–Navascués (arXiv:2507.06912 v2, 2026) already establishes
severe quantum extrapolation instability, complete future uncertainty
through “fog-bank” datasets, and binomial/power hard instances. Therefore
generic forecasting impossibility, need for structural priors, and continuum
future uncertainty are not available novelty claims.

Surviving distinction is the conjunction of:

- survival probability rather than arbitrary demolition measurements;
- one fixed state and return projector;
- one exactly common spectrum across unitarily equivalent Hamiltonians;
- exact nearest-neighbour one-particle realizations for every
  \(p\in[0,1]\), with an active--spectator block at \(p=1\);
- a sharp converse that every tridiagonal fixed-protocol realization at
  \(p=1\) must contain a zero path coupling;
- a connected Krylov representative for every \(p<1\), giving an exact
  connected/disconnected endpoint dichotomy;
- exact embedding as the one-excitation block of a Hermitian
  particle-number-preserving local occupation matrix;
- complete common subset-sum spectra for intrinsic second quantization in
  every fermion-number sector;
- a dual one-Hamiltonian realization;
- an explicit dual realization in one fixed permutation-invariant uniform
  onsite field on qubits, with symmetric pure preparations;
- continuous whole-window agreement;
- every exact terminal return probability;
- arbitrary finite energy-moment matching;
- minimum common spectral support.

This conjunction appears new and eliminates unknown preparation as the
obstruction in the fixed-protocol theorem. Nature significance remains
below threshold because conceptual result is close to Manos et al., the
fixed-protocol many-body extension is free and inhomogeneous, the
homogeneous dual protocol varies preparation, and there is no experiment or
new quantitative physical prediction.

## Gates

- [x] continuum construction and paper proof
- [x] unconditional targeted formal compilation
- [x] scaled shared-Hamiltonian pure-state realization
- [x] fixed-state, fixed-projector, isospectral-Hamiltonian realization
- [x] direct-collision audit and narrowed novelty
- [x] manuscript contains no formal-method novelty claim
- [x] nearest-neighbour chain realization for every \(p<1\)
- [x] exact particle-number-preserving occupation-space embedding
- [x] intrinsic second quantization and common all-sector subset-sum spectra
- [x] combined nearest-neighbour/free-fermion theorem for every \(p<1\)
- [x] nearest-neighbour endpoint realization at \(p=1\)
- [x] proof that every tridiagonal fixed-protocol endpoint realization is
      necessarily disconnected
- [x] connected Krylov representatives for every \(p<1\), completing the
      exact connectivity dichotomy
- [x] combined nearest-neighbour/free-fermion theorem for every
      \(p\in[0,1]\)
- [x] fixed permutation-invariant uniform-field qubit realization in the
      varying-preparation protocol
- [ ] identify the explicit full occupation matrix with intrinsic
      second quantization, beyond their proved one-excitation agreement
- [ ] final axiom/lint/umbrella-build audit
- [ ] experiment or new physical prediction
- [ ] hostile Nature review passes

## Nearest-neighbour research plan

Literature route: finite inverse spectral theory identifies a positive
atomic spectral measure with an irreducible Jacobi matrix.  Here all
interpolated weights are strictly positive for \(0\leq\theta<1\), so the
Krylov vectors
\[
 |\psi_\theta\rangle,\ K|\psi_\theta\rangle,\ldots,K^n|\psi_\theta\rangle
\]
form a Vandermonde-independent basis.  Gram--Schmidt beginning at
\(|\psi_\theta\rangle\) makes multiplication by \(K\) tridiagonal.  Pulling
that basis back to the fixed endpoint state gives a nearest-neighbour
one-particle chain with the same spectrum and the same fixed return
probability.  Required proof chain:

1. strict positivity of \(w_{\theta,j}\) for \(\theta<1\);
2. Vandermonde independence of the full Krylov family;
3. the first Gram--Schmidt vector is exactly \(|\psi_\theta\rangle\);
4. self-adjointness plus nested Krylov spans annihilates matrix entries
   beyond the first off-diagonals;
5. package the result into the universal finite-window theorem.

Endpoint \(\theta=1\) has zero spectral weights. It is handled as a
reducible chain: an active parity-support Jacobi block plus uncoupled
missing eigenmodes. For odd \(n\), active and spectator sectors have equal
size; their concatenated basis gives a tridiagonal block Hamiltonian with
the fixed endpoint state and complete common spectrum.

This reducibility is sharp. A tridiagonal path with all forward couplings
nonzero admits no nonzero eigenvector orthogonal to its first endpoint:
coordinatewise induction through the eigenvalue equation forces such a
vector to vanish. The parity endpoint omits every even spectral mode, and
transporting one such mode through any admissible unitary produces a
nonzero endpoint-orthogonal eigenvector. Hence every tridiagonal endpoint
realization has a zero path coupling.

## Log

- 2026-07-28 — endpoint pair generalized to every \(p\in[0,1]\), arbitrary
  finite energy-moment matching and sharp support.
- 2026-07-28 — scaled Hamiltonian, normalized evolved states and survival
  overlaps made explicit.
- 2026-07-28 — direct collision with Manos et al. recorded; broad novelty
  claims removed.
- 2026-07-28 — preparation dependence eliminated by unitary transport:
  one fixed state/projector, identical Hamiltonian spectrum, matching
  fixed-state moments and every terminal probability.
- 2026-07-28 — Vandermonde-cyclic Krylov bases give exact tridiagonal
  fixed-endpoint representatives for every terminal probability \(p<1\).
- 2026-07-28 — parity-support Krylov block plus diagonal spectator block
  closes exact tridiagonal locality at \(p=1\); closed-interval one-particle,
  occupation and intrinsic Fock capstones compile.
- 2026-07-28 — endpoint cyclicity gives the converse rigidity law: every
  tridiagonal fixed-protocol \(p=1\) realization has a zero path coupling;
  targeted compilation and axiom audit pass.
- 2026-07-28 — nonzero leading Gram--Schmidt coefficients force every
  adjacent Krylov coupling to be nonzero for \(p<1\); exact connectedness
  dichotomy compiles and passes axiom audit.
- 2026-07-28 — dual theorem embedded in one fixed uniform onsite qubit
  field invariant under every site permutation; symmetric pure
  preparations retain exact amplitudes, moments and all terminal values.

## Many-body lift research plan

The remaining locality criticism cannot be closed by merely renaming the
one-particle Jacobi matrix a spin chain.  The candidate physical lift is the
number-conserving open XX chain.  Its one-excitation block is the Jacobi
matrix, while its fermionic Fock spectrum consists of all subset sums of the
one-particle energies.  The full claim is admissible only after the following
dependency-closed chain is formal:

1. define the finite occupation-basis spin space and one-excitation embedding;
2. define the nearest-neighbour number-conserving XX Hamiltonian from onsite
   and adjacent hopping coefficients;
3. prove that its restriction to the one-excitation sector is exactly the
   supplied tridiagonal Hamiltonian;
4. construct the finite fermionic Fock eigenbasis and prove that the
   many-body energies are precisely the subset sums of the one-particle
   energies, including multiplicities;
5. prove that unitary equivalence of the one-particle Hamiltonians induces
   unitary equivalence of the full Fock Hamiltonians;
6. lift the fixed preparation and return projector and recover the same
   survival record and terminal probability;
7. package the universal theorem for every horizon, tolerance, finite moment
   order and target probability.

Intermediate scope gate: after items 1--3 only, the paper may say that the
construction is realized in the one-excitation sector of a local XX chain.
Items 4--5 are now proved twice: by an explicit transported exterior
Hamiltonian and, more strongly, by intrinsic normalized antisymmetrized
second quantization with a complete Slater eigenbasis. The paper may say
that every intrinsic fermion-number sector has one common complete
subset-sum spectrum. It must not yet identify that intrinsic operator with
the separately defined full occupation matrix; their equality is proved
only on the one-excitation block. Translation invariance and interaction
remain separate conditions and must not be implied.

- 2026-07-28 — many-body/free-fermion lift opened after hostile review;
  exact one-excitation block and full Fock isospectrality separated as
  independent proof gates.
- 2026-07-28 — intrinsic \(d\Gamma\) constructed as normalized
  antisymmetrized slotwise action; Slater subset-sum spectrum proved for
  every fixed-protocol candidate and every particle number.
- 2026-07-28 — universal nearest-neighbour/free-fermion capstone proved for
  every terminal probability in \([0,1]\); explicit occupation matrix and
  intrinsic Fock lift remain intentionally unmerged outside the
  one-excitation sector.
