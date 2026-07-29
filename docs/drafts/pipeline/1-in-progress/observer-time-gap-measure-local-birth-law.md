# Observer time is a gap measure with a connected birth filtration

- **ID:** observer-time-gap-birth
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), manuscript and novelty audit open
- **Source:** recurrence corpus synthesis after rejection of the earlier anatomy/collage framing
- **Statement:** Complete projective return history is equivalent to one
  observer-selected energy-gap measure; under arbitrary local control
  architectures, every finite experiment generates each visible gap through
  a canonical coordinate-invariant sum of connected interaction packets.

## Goal

Replace the multi-clause “recurrence anatomy” by one mathematical object and
one local-to-global law.

The global object is the observer-time gap measure
\[
  \nu_O=(E-E')_\#(\mu_O\otimes\mu_O).
\]
Its characteristic function is the complete projective return record:
\[
  \widehat{\nu_O}(t)=|\widehat{\mu_O}(t)|^2.
\]
Characteristic-function injectivity makes this factorization complete, not
an analogy: two observer spectra have the same fidelity at every time if and
only if they have the same \(\nu_O\).

For a locally controlled finite experiment, every moving atom
\(E_i(g)-E_j(g)\) of this measure has the exact germ decomposition
\[
 E_i(g_S)-E_j(g_S)-\bigl(E_i(0)-E_j(0)\bigr)
 =
 \sum_{\substack{P\subseteq S\\P\ne\varnothing\\P\ {\rm spatially\
 indecomposable}}}
 \Delta_P(E_i-E_j)(g).
\]
The packet projectors are pairwise orthogonal.  A packet of \(n\)
independently switchable channels is \(O(\|g\|^n)\); every disconnected
packet vanishes.  Relabelling channels and independently changing their
nonzero units preserve and reflect each packet's zero-germ status.

Scientific interpretation under test:

> Operational quantum time is not a property of a Hamiltonian alone.  It is
> the observer's projective gap measure.  Locality determines how that
> measure can be born: only connected interaction packets can move its
> visible atoms, one control order at a time.

## Gates

- [x] 0 → 1 in-progress: well-posed object, exact global completeness,
  exact local decomposition, explicit falsifiers
- [ ] 1 → 2 fully-proven on paper: sharp physical family and complete
  local-to-gap-measure bridge written without hidden assumptions
- [ ] 2 → 3 formalized: all manuscript claims mapped; capstone module;
  foreground checks; axiom audit
- [ ] 3 → 4 publication-ready: one-law manuscript, primary-source novelty
  audit, device protocol, hostile Nature review

## What earlier work missed

The earlier manuscript assigned separate objects to threshold, finite
deadline, observer graph, collision statistics and non-identifiability.  That
was a dependency chart, not a law.

The new invariant explains them:

1. Exact recurrence is cyclicity of the support-generated group of
   \(\nu_O\).
2. Temporal dimension is the rational rank of that same support.
3. Every long-time fidelity moment is a zero-sum collision mass of
   \(\nu_O^{*n}\).
4. Every continuous long-time fidelity statistic is determined by this
   collision hierarchy.
5. Rate--distortion bounds are finite-support covering laws on the character
   torus of the same support group.
6. Local and perturbative classifier no-go theorems fail precisely because
   their inputs do not determine the completed \(\nu_O\).
7. Locality supplies the missing birth mechanism: visible gap germs are
   reconstructed from connected Möbius sectors, with a hypergraph-Steiner
   onset obstruction.

## Formal status

### Global completeness, arbitrary finite or infinite spectra

`formal/GaloisForLFunctions/RHTower/ObserverTimeGapMeasureLaw.lean`

- `charFun_observerTimeGapMeasure`
- `observerTimeGapMeasure_eq_iff_projectiveReturnRecord_eq`
- `observerTimeGapMeasure_translate_invariant`
- `projectiveReturnRecord_eq_iff_collisionMeasures_eq`
- `exists_positive_projectiveReturnRecord_one_iff_cyclic`
- `spectralReturnMomentMeanReal_tendsto_observerTimeCollisions`

### Exact local connected birth

`formal/GaloisForLFunctions/HTGeometry/LocalSpectralObserverControlOrbitLaw.lean`

- exact reconstruction for every activated control subset
- exact connected reconstruction for every continuous linear spectral
  observer

`formal/GaloisForLFunctions/HTGeometry/LocalObserverTimeGapBirthLaw.lean`

- total energy gap = onsite gap + interaction response
- analyticity of every selected gap
- real energy-gap germs for Hermitian families and real controls
- connected packet reconstruction of every selected energy gap
- packet-cardinality onset bound

`formal/GaloisForLFunctions/HTGeometry/InteractionPacketCoordinateInvariance.lean`

- invariance under arbitrary channel relabelling
- invariance under independent nonzero changes of control units

`formal/GaloisForLFunctions/HTGeometry/ArbitraryControlArchitectureObserverTimeLaw.lean`

- every finite experiment inside an arbitrary, possibly infinite, control
  architecture obeys the same law

## Novelty boundary

Known parent theories:

- linked-cluster and Schrieffer--Wolff expansions already force connected
  clusters in effective Hamiltonians;
- Boolean Möbius inversion and functional interaction decompositions are
  general mathematics;
- characteristic functions already identify finite measures;
- quantum recurrence has long been expressed through spectral measures.

Therefore none of those facts is claimed as new.

Candidate novelty is their exact observer-specific local-to-global
factorization:

- complete projective return history is identified with one minimal
  observer gap measure;
- all continuous linear spectral observers receive a canonical orthogonal
  packet resolution;
- locality kills disconnected packet germs for every simple spectral branch,
  not only a ground-state energy or effective Hamiltonian truncation;
- every activated subset reconstructs from connected subpackets;
- a hypergraph-Steiner condition governs the first eligible observer-time
  layer;
- the construction is invariant under the control-coordinate changes that
  preserve independent switchability;
- the same object classifies exact return and every long-time collision
  statistic for arbitrary spectra.

Absence of an equivalent theorem in preliminary search is not proof of
priority.  External linked-cluster, spectral-analysis and quantum-recurrence
experts must audit this boundary.

## Hard falsifiers and rejection conditions

1. A prior theorem giving the same observer-gap-measure completeness plus
   connected local birth filtration kills the novelty claim.
2. If packet depth changes under channel relabelling or independent unit
   changes, it is bookkeeping rather than physics.  These invariances are
   now proved.
3. Arbitrary linear mixing is not a harmless coordinate change because it
   changes which controls can be switched off independently.  Claim no such
   invariance.
4. Calling rational gap rank “the dimension of physical time” without the
   operational return-record definition is an overclaim.
5. Connected-cluster support alone is not enough for Nature.  Explicit
   Hermitian two-control and closed three-edge-cycle packets are now proved
   nonzero, but exact generic graph-distance onset remains open.
6. No claim about quantum gravity, cosmological time, black-hole interiors,
   an arrow of time or thermodynamic-limit locality is allowed without a
   separate theorem.
7. A theory-only paper without a feasible small-device protocol remains a
   Nature editorial risk.

## Open core

1. Formalize generic exact pair-distance birth for Hermitian graph-local
   Hamiltonians, including the labelled-cycle coefficient
   \[
     [\lambda_1\cdots\lambda_d]E_{s_0}
       =\frac{2}{\prod_{j=1}^{d-1}(A_0-A_j)}.
   \]
2. Derive a small-device protocol using independently tunable couplers and
   multi-level spectroscopy; quantify required subset measurements and
   resolution.
3. Rewrite the master paper around the exact gap cocycle, its measure
   pushforward and connected birth filtration. Previous
   threshold/deadline/no-go results become corollaries or supplementary
   material, not coequal clauses.
4. Complete primary-source priority audit against excited-state linked
   cluster expansions, spectral phase retrieval and 2026 recurrence bounds.
5. Re-run hostile review. Current honest editorial verdict: not yet
   Nature-ready because generic graph-distance sharpness, priority
   confirmation and an empirical protocol are missing.

## Log

- 2026-07-29 — Rejected earlier “universal recurrence anatomy” as a collage.
- 2026-07-29 — Proved exact connected control-orbit reconstruction for every
  continuous linear spectral observer.
- 2026-07-29 — Proved Hermitian real-energy bridge.
- 2026-07-29 — Proved relabelling and independent-unit invariance.
- 2026-07-29 — Proved complete projective return-record/gap-measure
  equivalence for arbitrary probability spectra.
- 2026-07-29 — Extended local law to every finite experiment inside
  arbitrary infinite control architectures.
- 2026-07-29 — Proved energy gaps are exact pair cocycles, reconstruct
  energies uniquely up to a common origin, and commute with every Boolean
  control-packet projector.
- 2026-07-29 — Proved finite atomic bridge: observer-time measure is exactly
  weighted pushforward of pair states through controlled gap cocycle.
- 2026-07-29 — Proved explicit Hermitian sharpness at connected packet layer
  two, then removed parallel-control objection with linearly independent
  transverse and diagonal controls.
- 2026-07-29 — Identified closed-cycle spectral holonomy as the mechanism
  beneath irreducible control packets.  Proved a three-level Hermitian cycle
  with three linearly independent edge controls has a nonzero joint packet:
  every proper forest is edge-sign gauge invariant, while the full
  characteristic equation detects the product of all three edge signs.
- 2026-07-29 — Extended law from closed unitary dynamics to every finite
  contraction: return amplitude is persistent mass times one peripheral
  characteristic function plus a transient tending to zero; transient-
  stripped fidelity is exactly persistent mass squared times gap record.
