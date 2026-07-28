# Local-horizon quantum return law

- **ID:** local-horizon-quantum-return-law
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Date:** 2026-07-28
- **Source:** positive strengthening of `complete-future-return-ambiguity`

## Exact target

For every local radius \(R\), target time \(T>0\), strict observation
horizon \(0\le H<T\), tolerance \(\delta>0\), and terminal probability
\(p\in[0,1]\), construct finite nonnegative self-adjoint nearest-neighbour
Hamiltonians \(J_p\) on one fixed path, with one fixed endpoint state
\(e_0\) and return projector, such that:

1. every \(J_p\) has the same complete spectrum, including multiplicities;
2. all onsite terms and bonds in the endpoint ball of radius \(R\) are
   exactly identical across \(p\);
3. endpoint survival probabilities lie within \(\delta\) of one common
   record for every \(t\in[-H,H]\);
4. endpoint return probability at \(T\) is exactly \(p\);
5. every \(p<1\) has a connected representative;
6. exact \(p=1\) forces a zero bond outside the common local ball.

The finite construction may grow dimension and bandwidth with
\((R,H/T,\delta)\). A separate exact lift now realizes every witness on a
countably infinite Hilbert space with a maximal self-adjoint unbounded
Hamiltonian, normalized states, and infinitely many distinct energy levels.
The lift preserves all matched moments and exact terminal probabilities and
cannot enlarge earlier return discrepancies. It is an exact infinite system,
not an interacting thermodynamic limit.

## Formal status — 2026-07-28

Core construction is closed in
`LocalHorizonQuantumReturnLaw.lean`.
`localHorizon_every_future_probability` proves one common dimension and
baseline work simultaneously for every \(p\in[0,1]\), with:

- exact equality of all local matrix entries whose shifted Krylov degree is
  at most \(2R+2\), hence every onsite through \(R\) and bond through
  \(R\leftrightarrow R+1\);
- self-adjoint nearest-neighbour Hamiltonians;
- exact unitary intertwining with one common diagonal Hamiltonian, hence
  isospectrality including multiplicity;
- one fixed endpoint state;
- \(\delta\)-close return probabilities throughout \([-H,H]\);
- exact terminal return \(p\);
- an explicit active-sector-plus-spectator construction at \(p=1\), without
  applying strict positivity at the rank-dropped endpoint.

The generic engine is stronger than the construction:
`canonicalKrylovCompression_local_eq_of_moments_cross_of_sizes` permits
different spectra and different ambient dimensions. Matching moments through
\(2R+2\) alone fixes the corresponding local canonical entry.

The genuine infinite extension is closed in:

- `MaximalRealDiagonalSelfAdjoint.lean`: maximal coordinate multiplication by
  every real energy function on \(\ell^2(I)\) is self-adjoint;
- `InfinitePhaseLadderLocalHorizonLaw.lean`: `exists_infiniteLocalHorizonWitness`
  gives every \(R,T,H,\delta,p\) an exact countably infinite witness whose
  Hamiltonian is self-adjoint, norm-unbounded, and has an injective infinite
  energy ladder over every finite spectral coordinate;
- `InfinitePhaseLadderMomentTransfer.lean`:
  `phaseLadderMoment_decomposition` expresses every lifted moment as a
  triangular combination of base moments, and
  `infiniteAngularInterpolated_moments_eq` proves exact preservation of every
  requested finite moment record.

The lift uses
\[
 E_{j,k}=E_j+\frac{2\pi k}{T},\qquad
 \gamma_k=2^{-(k+1)}.
\]
Its amplitude factorizes exactly:
\[
 A_p^\infty(t)=A_p(t)B_T(t),\qquad
 B_T(t)=\sum_{k\ge0}\gamma_k
   \exp\!\left(2\pi i k\,t/T\right).
\]
Here \(B_T(T)=1\) and \(|B_T(t)|\le1\), so terminal laws survive exactly while
earlier distinguishability can only decrease.

## Stronger apex target: locality--predictability law

The construction alone is not enough.  Pair it with a converse causal
bound for arbitrary finite nearest-neighbour chains.

Let \(J,K\) be self-adjoint path Hamiltonians with the same onsite
coefficients \(a_0,\ldots,a_R\) and the same bonds
\(b_0,\ldots,b_R\).  Then every endpoint closed walk of length at most
\(2R+2\) sees exactly the same matrix entries, hence
\[
 \langle e_0,J^m e_0\rangle=\langle e_0,K^m e_0\rangle
 \qquad(0\le m\le 2R+2).
\]
If \(\|J-c_JI\|,\|K-c_KI\|\le\Lambda\), after removing the irrelevant
global phases the exponential series gives the dimension-free bound
\[
 |A_J(t)-\mathrm e^{-\mathrm i(c_J-c_K)t}A_K(t)|
 \le
 2\sum_{m\ge 2R+3}\frac{(\Lambda |t|)^m}{m!}
 \le
 2\mathrm e^{\Lambda |t|}
   \frac{(\Lambda |t|)^{2R+3}}{(2R+3)!}.
\]
The probability discrepancy is at most twice this amplitude bound.

The parity construction supplies the converse order of scale.  At
\(n=2q+1\), moments agree through \(2q\), and the canonical path
coefficients agree for onsites and bonds with left index
\(0,\ldots,q-1\).  Thus choosing \(q\ge R+1\) hides the selecting
Hamiltonian beyond every prescribed local radius while retaining the
entire target interval.  The centered bandwidth is
\(\pi n/(2T)\), so the construction has
\[
 R=\Theta(\Lambda T).
\]
Consequently linear distance--bandwidth--time scaling cannot be improved
to a superlinear universal predictability horizon.  Constants and the
optimal norm model remain separate questions.

This theorem hierarchy would support the defensible headline:

> Locality protects the quantum past only up to a linear horizon; beyond
> it, the same local Hamiltonian and arbitrarily accurate return record
> can permit every future return probability.

It does not imply indeterminism, superluminal signaling, a cosmological
horizon, or a result about a particular material.

## Coverage expansion: spectral-memory classification

The final paper should not stop at finite closed paths.  Add a
dependency-closed classification with three exact regimes:

1. **Finite passive/open dynamics.**  Retain the already proved theorem
   for every finite-dimensional contraction and every finite convex
   mixture: the peripheral projection mass is the exact late-return
   ceiling.  Seek the same attractor/transient statement in an
   operational trace norm for every finite quantum channel, rather than
   claiming Hilbert--Schmidt contractivity for all channels.
2. **Arbitrary pure-point spectrum.**  Retain the proved countable
   summable phase-energy recurrence and observer zero law.  This removes
   finite dimension without taking a formal thermodynamic limit.
3. **Continuous spectral mass.**  Closed in
   `SpectralMeasureExactReturnClassification.lean`: for every probability
   spectral measure and every nonzero time, unit survival is equivalent to
   almost-everywhere phase locking.  The phase fibre is countable, so exact
   return forces a countable full-mass carrier.  More strongly, every
   atomless submeasure of an exactly returning spectrum is zero.  Therefore
   any nonzero continuous component forbids exact return.  Add the Wiener
   time-average law only if its complete measure theorem is formalized.

This yields a single total boundary: discrete lossless modes carry
recurrent memory; strictly contractive modes lose it; continuous spectral
mass cannot return exactly; remote local structure can still hide which
finite-system future occurs before the locality horizon.

The cofinal thermodynamic statement is now closed:
`exists_cofinalLocalHorizonSequence` selects finite models with exact common
radius \(R\), strict-window discrepancy tending to zero, and terminal gap
exactly \(p\) at every stage. This is not convergence to two distinct
globally identical infinite Hamiltonians.
`infiniteBoundedOperator_eq_of_all_matrixEntries_eq` proves the sharp
boundary: two fixed bounded operators on \(\ell^2(\mathbb N)\) with every
canonical matrix entry equal are identical, hence all iterates agree.

The relational-clock bridge is closed in
`RelationalClockLocalHorizonLaw.lean`: the same law is realized by stationary
clock--system histories obeying exact clock covariance. This removes external
coordinate time from the formulation. It does not turn the theorem into a
gravitational field equation or derive cosmological initial conditions; those
would be different scientific claims requiring corresponding models.

## Mathematical engine

Use the parity-conditioned binomial measures at odd depth
\[
 n=2q+1,\qquad
 q_j=2^{-n}{n\choose j},\qquad
 w_{p,j}=(1-\sqrt p)q_j+\sqrt p\,q_j[1+(-1)^{n-j}]
\]
on energies \(E_j=\pi j/T\).

All measures have identical moments through degree \(n-1=2q\). The
normalized Krylov/Lanczos representation of a positive spectral measure is
a Jacobi matrix. Its onsite coefficient at site \(a\) depends only on
moments through degree \(2a+1\), and its bond from \(a\) to \(a+1\) only on
moments through degree \(2a+2\). Therefore the family has a common
observer-side Jacobi prefix of linearly growing depth.

At \(p=1\), the active odd-energy measure has \(q+1\) support points. Its
Jacobi block terminates after \(q+1\) sites and unused even eigenvalues form
a spectator block. Existing endpoint rigidity proves that every
tridiagonal fixed-protocol realization must have a zero bond. For \(p<1\),
all spectral weights are positive and existing Krylov rigidity proves every
bond in the canonical representative is nonzero.

The exact amplitude law remains
\[
 |A_p(t)-A_0(t)|
 =\sqrt p\,\left|\sin\frac{\pi t}{2T}\right|^n ,
\qquad P_p(T)=p.
\]

Index audit: at \(n=2q+1\), onsite \(a_j\) uses moments through
\(2j+1\), and bond \(b_j\) uses moments through \(2j+2\).  Therefore
\(a_j,b_j\) are common for every \(j\le q-1\).  At \(p=1\), the active
block has \(q+1\) sites and the forced fracture is bond \(b_q\), strictly
outside this common prefix.  Numerical pre-certification at
\(n=3,5,7\) confirms these indices; it is not evidence for the theorem.

## Open core

Moment-prefix transfer, cross-dimension endpoint transfer, the closed
\([0,1]\) capstone, the relational-clock form, and the exact unbounded
infinite-system lift are complete. Remaining mathematical strengthening:

1. common path terms imply endpoint power moments through exact round-trip
   order \(2R+2\);
2. dimension-free operator-exponential tail bound;
3. integrate existing connectedness below \(p=1\) and forced remote fracture
   at \(p=1\) into one public capstone if paper uses those clauses.

Remaining publication work:

4. establish the exact novelty boundary against inverse Jacobi, truncated
   moment, Hamiltonian-learning, and quantum-forecasting literature;
5. state experimental falsifiers and resource scaling without claiming device
   feasibility not established by a theorem or study;
6. run hostile Nature editorial and specialist-referee reviews.

## Formal dependencies already closed

- `ParityConditionedForecastingInstability.lean`
  - `parity_energyMoment_eq_full`
  - `interpolated_energyMoment_eq_full`
  - `one_record_compatible_with_every_future_probability`
- `KrylovNearestNeighborRealization.lean`
  - `finiteKrylovVector_linearIndependent`
  - `finiteKrylovBasis_nearestNeighbor`
  - `fixedProtocolHamiltonian_krylov_nearestNeighbor`
- `EndpointKrylovNearestNeighborRealization.lean`
  - `endpointActiveWeight_pos`
  - `endpointBlockBasis_active_matrix`
  - `fixedProtocolHamiltonian_endpoint_nearestNeighbor`
- `PerfectReturnPathRigidity.lean`
  - `finiteKrylovBasis_forward_entry_ne_zero`
  - `endpoint_paritySupport_forces_path_disconnection`
- `QuantumRecurrenceUniversality.lean`
  - dependency-closed prior capstone
- `KrylovGramPrefixTransfer.lean`
  - `canonicalCompressionEntry_eq_of_gram_eq_of_rectangle`
  - `canonicalKrylovCompression_local_eq_of_moments_cross_of_sizes`
  - `canonicalKrylovPathHamiltonian_local_eq_of_moments_of_size`
  - `canonicalKrylovPathHamiltonian_nearestNeighbor`
- `LocalHorizonQuantumReturnLaw.lean`
  - `endpointCanonicalPathHamiltonian_local_eq_full`
  - `localHorizon_every_strict_future_probability`
  - `localHorizon_every_future_probability`
  - `exists_cofinalLocalHorizonSequence`
  - `infiniteBoundedOperator_eq_of_all_matrixEntries_eq`
- `SpectralMeasureExactReturnClassification.lean`
  - `norm_charFun_eq_one_iff_phase_locked`
  - `exact_return_has_countable_spectral_carrier`
  - `exact_return_has_no_atomless_submeasure`
- `MaximalRealDiagonalSelfAdjoint.lean`
  - `maximalRealDiagonal_isSelfAdjoint`
- `InfinitePhaseLadderLocalHorizonLaw.lean`
  - `phaseLadderReturnAmplitude_factor`
  - `phaseLadderHamiltonian_isNormUnbounded`
  - `exists_infiniteLocalHorizonWitness`
- `InfinitePhaseLadderMomentTransfer.lean`
  - `phaseLadderMoment_decomposition`
  - `phaseLadderMoment_eq_of_base_moments_eq`
  - `infiniteAngularInterpolated_moments_eq`
- `RelationalClockLocalHorizonLaw.lean`
  - `isClockCovariant_iff_stationary`
  - `universalRelationalLocalHorizon_every_future_probability`

## Novelty boundary

Classical:

- truncated moments determine a Lanczos/Jacobi prefix;
- binomial finite-difference cancellation;
- Krylov tridiagonalization;
- endpoint cyclicity for irreducible Jacobi matrices.

Closest direct collision:

- Manos--Weilenmann--Navascués, *Timed demolition measurements*
  (arXiv:2507.06912 v2), already proves generic quantum extrapolation
  instability, fog banks, continua of future distributions, and
  binomial/power hard instances.

Candidate new conjunction:

- one fixed endpoint preparation and projector;
- one exact complete spectrum;
- one exactly common physical nearest-neighbour Hamiltonian ball of
  arbitrary radius;
- one common continuous finite-window return record;
- every exact future return probability;
- connected representatives below one;
- forced remote path fracture at perfect return.
- an exact infinite-dimensional lift with maximal self-adjoint unbounded
  Hamiltonian, infinitely many distinct populated levels, and normalized
  states;
- exact preservation of every finite matched moment block under that lift;
- a dimension-free converse causal bound for every self-adjoint path;
- matching linear locality--bandwidth--time order for complete future
  ambiguity.

No priority claim is permitted until direct searches of inverse Jacobi,
fractional-revival, isospectral-chain, Krylov-complexity, and quantum
forecasting literature find no collision.

## Nature gate

This theorem can address the prior manuscript's principal physical
objection: candidate Hamiltonians would no longer differ arbitrarily close
to the observer. It would give a local, falsifiable statement: any finite
Hamiltonian neighbourhood and any finite pre-target return record can
leave the complete return interval unresolved because the selecting
structure lies beyond that neighbourhood.

Still required:

- exact shared-prefix theorem;
- exact round-trip causal bound and sharp prefix length;
- proof that linear \(R=\Theta(\Lambda T)\) order is the strongest
  defensible resource claim;
- direct literature collision audit;
- experimentally readable spin/photonic-chain protocol and robustness
  envelope;
- hostile review showing conceptual separation from fog-bank work;
- final Lean axiom, lint, and umbrella-build audits.

## Status

- [x] candidate law isolated
- [x] prior formal dependencies identified
- [x] broad collision with generic forecasting impossibility acknowledged
- [x] paper proof and Lean formalization of generic moment-to-Jacobi-prefix transfer
- [x] arbitrary spectral-measure exact-return and continuous-component boundary
- [ ] paper proof of path-prefix-to-moment and exponential-tail bounds
- [ ] Lean formalization of transfer and parity capstone
- [ ] physical protocol and robustness law
- [ ] Nature hostile review passes

## 2026-07-28 universal open-system extension

Hilbert--Schmidt geometry is no longer the general open-system boundary.
Two dependency-closed modules now separate the maximally general operational
law from its finite spectral identification.

- `UniversalOperationalMemoryFloor.lean`
  - `OperationalTheory.Channel.distance_evolve_le`
  - `OperationalTheory.Channel.tendsto_distanceAt_memoryFloor`
  - `OperationalTheory.Channel.memoryFloor_eq_zero_iff`
  - `OperationalTheory.Channel.memoryFloor_pos_iff`
  - `OperationalTheory.Channel.informationLossAt_monotone`
  - `OperationalTheory.Channel.forgetting_or_persistent_memory`
- `FiniteContractionOperationalMemoryLaw.lean`
  - `norm_finiteContraction_pow_apply_peripheralProjection`
  - `tendsto_norm_finiteContraction_pow_apply_peripheralProjection`
  - `tendsto_norm_finiteContraction_pow_apply_sub`
  - `finiteContraction_pair_forgetting_iff`
  - `finiteContraction_pair_persistent_memory_iff`

The first theorem quantifies over every state type, every effect type, every
probability response, every channel closed under Heisenberg pullback, and
every pair of states. It uses no Hilbert space, dimension, spectrum, norm,
closedness, or reversibility. Operational distinguishability decreases to
one exact floor. Exactly one of two phases holds: complete forgetting, or a
strictly positive distinction surviving at every future time. The resulting
information-loss current is monotone. This is an operational arrow, not a
claim to derive the thermodynamic or cosmological arrow.

The second theorem identifies the floor for every finite-dimensional Hilbert
contraction: it is exactly the norm of the peripheral projection of the
initial state difference. This closes the finite spectral mechanism and
makes the survivor criterion algebraic. It does not reinstate a false
all-CPTP Hilbert--Schmidt claim.

Scientific placement: these are scope and interpretation theorems. Data
processing and peripheral channel asymptotics have extensive prior art, so
neither contributes to the novelty score. The candidate novelty remains the
local-horizon/cofinal future-indeterminacy theorem and its sharp all-radii
global boundary.

## 2026-07-28 normalized Kraus-channel closure

`FiniteQuantumOperationalMemoryLaw.lean` now proves the standard finite
quantum realization, not merely an abstract channel schema.

- density matrices and all quantum effects are constructed explicitly;
- effect probabilities are proved to lie in `[0,1]`;
- every normalized finite Kraus family preserves positivity and trace;
- its Heisenberg pullback preserves the full quantum-effect interval;
- trace cyclicity proves exact Born-probability duality;
- the universal exact floor, forgetting/persistence dichotomy, and monotone
  operational information loss follow for every such channel, including
  nonunital channels.

Principal capstones:

- `FiniteKrausChannel.tendsto_operationalDistance_memoryFloor`
- `FiniteKrausChannel.forgetting_or_persistent_memory`
- `FiniteKrausChannel.operationalInformationLoss_monotone`

This closes the old Hilbert--Schmidt-normalization objection by eliminating
an auxiliary operator probe norm: distinguishability is the supremum Born
probability gap over every physical quantum effect. It also closes the
nonunital finite-open-system exclusion. It does not claim a new data
processing theorem; this remains supporting scope, not novelty.
