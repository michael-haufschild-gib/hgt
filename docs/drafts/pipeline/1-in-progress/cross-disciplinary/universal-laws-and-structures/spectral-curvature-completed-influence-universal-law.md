# Spectral-curvature completed-influence universal law

- **ID:** `spectral-curvature-completed-influence-universal-law`
- **Stage:** 1-in-progress
- **Type:** PAPER-PROVED BRIDGE / UNIVERSAL CLASSIFICATION
- **Labels:** `[PAPER-PROVED] [BRIDGE] [NOVELTY INSUFFICIENT ALONE]`
- **Parent:** `universal-quantum-recurrence-anatomy`
- **Date opened:** 2026-07-31

## Public sentence

> Interaction strength controls how long quantum influence is delayed, but
> spectral curvature decides whether maximal influence can ever occur.

## Theorem

Let \(\Omega\) be a finite configuration space, let
\(E:\Omega\to\mathbb R\), and let \(P,Q:\Omega\to\Omega\) be commuting
involutions. On \(\ell^2(\Omega)\), let \(U_t\) multiply the configuration
\(\omega\) by \(e^{-itE(\omega)}\), and let the same letters \(P,Q\) denote
the induced permutation unitaries. Define the mixed spectral curvature
\[
 \kappa_{P,Q}E(\omega)=
 E(PQ\omega)-E(P\omega)-E(Q\omega)+E(\omega).
\]
Then
\[
 \boxed{
 \sup_{t\in\mathbb R}\|[U_tPU_{-t},Q]\|_{\mathrm{op}}
 =
 \begin{cases}
 0,&\kappa_{P,Q}E\equiv0,\\
 2,&\kappa_{P,Q}E\not\equiv0.
 \end{cases}}
 \tag{SC}
\]

For a Boolean product configuration and coordinate flips \(X_x,X_y\),
\(\kappa_{x,y}E\equiv0\) exactly when every Walsh interaction coefficient
whose support contains both \(x\) and \(y\) vanishes. Hence the
completed-time influence graph is exactly the two-section of the nonzero
interaction hypergraph, independent of coefficient magnitudes.

The recurrence law and curvature law should admit one factorization:

- support incidence determines which pairs can ever influence one another;
- rational arithmetic of the same coefficient labels determines exact
  projective recurrence dimension;
- coefficient magnitude and spatial decay determine delay and fixed-time
  locality, not completed-time reach.

## Proof

Put
\[
 a_t(\omega)=
 \exp\!\bigl(it(E(P\omega)-E(\omega))\bigr).
\]
The evolved permutation has the exact action
\[
 (U_tPU_{-t}\psi)(\omega)=a_t(\omega)\psi(P\omega).
\]
Since \(P\) and \(Q\) commute,
\[
 [U_tPU_{-t},Q]\psi(\omega)=
 \bigl(a_t(\omega)-a_t(Q\omega)\bigr)\psi(PQ\omega).
\]
The right side is multiplication followed by a permutation unitary, so
\[
 \|[U_tPU_{-t},Q]\|_{\rm op}
 =
 \max_{\omega\in\Omega}
 \left|1-\exp\!\bigl(it\kappa_{P,Q}E(\omega)\bigr)\right|.
\]
If the curvature vanishes, this is zero for every time.  If
\(\kappa_{P,Q}E(\omega_0)\ne0\), the choice
\[
 t=\pi/|\kappa_{P,Q}E(\omega_0)|
\]
makes the corresponding phase antipodal and the norm equal to its universal
ceiling \(2\).

For a Boolean cube, Walsh expansion gives
\[
 \kappa_{x,y}E_J(\sigma)
 =
 4\sum_{S\ni x,y}J_S\chi_S(\sigma).
\]
Linear independence of the Walsh characters proves that this function
vanishes exactly when every coefficient crossing the pair vanishes.

## Anderson-locality merger

The theorem does not identify interacting l-bit dynamics with Anderson
localization.  It classifies the exact fracture between them:

- the Anderson/noninteracting endpoint has no cross-site interaction
  curvature and admits time-uniform confinement;
- an interacting diagonal localized model can remain transport-localized
  while any nonzero cross-site curvature makes the completed operator-norm
  influence equal to \(2\);
- exponential locality then constrains only the waiting time.  In the
  explicit infinite l-bit field already formalized, every pair saturates
  while
  \[
  2\le
  4K\,t_{xy}\,2^{-\operatorname{dist}(x,y)}.
  \]

There is a second, genuinely Anderson-facing projection already formalized.
For a local survival packet with exponentially localized spectral weights,
the recurrence error is the sum of a localization-tail term and a resolved
phase term, while the deadline exponent depends on the number of modes in
the localization volume rather than the ambient Hilbert-space dimension.
The same escape--return alternative holds for countably infinite
nonnegative summable pure-point packets.  Thus Anderson locality compresses
the recurrence problem seen by a local observer, whereas interactions
decide whether that spatial barrier survives completion in time.

## Why the combination matters

This changes the primitive from “localization length versus recurrence
rank” to a labelled spectral-curvature hypergraph. Anderson confinement,
l-bit logarithmic propagation, recurrence-rank explosion, finite-range
ceilings, symmetry-induced rank loss and the same-boundary quadratic budget
become distinct shadows of topology, arithmetic and metric on the same
hyperedges.

The exact scale-free \(0/2\) dichotomy `(SC)` shows that no intermediate
completed-time operator-norm influence exists for diagonal dynamics with
commuting involutive probes.  The observer-local recurrence theorem supplies
the complementary statement: the part of the future visible before
completion is controlled by localization volume.

## Internal frontier

- `[CORPUS]`
  `mixedCoordinateContrast` and its locality annihilation laws in
  `formal/GaloisForLFunctions/HTGeometry/SpectralCausality.lean`.
- `[CORPUS]`
  exact infinite l-bit commutator phase and fixed-time bound in
  `InfiniteLBitRecurrenceLocalitySeparationLaw.lean`.
- `[CORPUS]`
  exact saturation for one positive all-support field in
  `InfiniteLBitAllPairsInfluenceSaturationLaw.lean`.
- `[CORPUS]`
  recurrence dimension equals rational coefficient rank in
  `LBitTemporalDimensionLaw.lean`.
- `[CORPUS]`
  same-boundary rank doubling and mass budget in
  `LBitBoundaryTemporalDimensionBudgetLaw.lean`.
- `[CORPUS]`
  arbitrary finite-noise certification fails without normalization or a
  margin in `OperationalHorizonNoiseNoGo.lean`.

## External frontier

- `[LITERATURE]` Friesdorf--Werner--Goihl--Eisert--Brown, *New J. Phys.*
  **17**, 113054 (2015), prove arbitrary-distance information propagation
  from local constants of motion and a generic spectrum, without an exact
  pairwise \(0/2\) curvature classification.
- `[LITERATURE]` Exact l-bit OTO phase formulas and logarithmic crossovers
  occur in Chen--Zhou--Huse--Fradkin, *Ann. Phys. (Berlin)* **529**,
  1600332 (2017).
- `[LITERATURE]` Time-uniform zero-velocity Lieb--Robinson bounds for an
  Anderson-localized random XY chain occur in Hamza--Sims--Stolz,
  *Commun. Math. Phys.* **315**, 215--239 (2012).

## Shadow map

| Existing result | Proposed shadow |
|---|---|
| Anderson all-time confinement | vanishing distant spectral curvature |
| MBL logarithmic light cone | exponentially small but nonzero curvature; delay is metric |
| eventual all-pairs saturation | nonzero curvature on every pair |
| free Fock recurrence rank \(\le N\) | only singleton hyperedges |
| interacting rank up to \(2^N-1\) | rationally independent labelled hyperedges |
| finite-range rank ceiling | finite hyperedge support geometry |
| symmetry/collision rank loss | arithmetic label degeneracy without topology loss |
| boundary \(2\delta D^2\le K\) law | metric cost of resolving one topological boundary packet |
| finite-noise rescaling no-go | magnitude is not a scale-free completed-time invariant |

## Falsifiers

1. A nonzero curvature witness for which the all-time commutator norm never
   reaches \(2\).
2. Zero curvature with a nonzero commutator.
3. Failure of the Walsh support classification through cancellation of
   distinct characters.
4. A primary source already stating the exact general finite
   commuting-involution operator-norm dichotomy and labelled-hypergraph
   interpretation.
5. Failure of the claimed recurrence/curvature factorization because the
   two laws require unrelated coefficient packets.

## Hostile verdict

The scalar identity
\[
 \sup_t|1-e^{it\kappa}|=2\quad(\kappa\ne0)
\]
is elementary.  Exact l-bit OTO phases, logarithmic propagation and
interaction-induced dephasing are established literature.  The operator
identity and support classification are therefore a rigorous bridge, not a
Nature-level novelty claim by themselves.  The combined paper still needs
a new theorem that turns localization volume, recurrence completion and
finite-time operational distinguishability into one sharp invariant.

## Open core

`[OPEN CORE]` Define a stable observer-visible recurrence complexity whose
finite-time value is bounded by Anderson localization and whose completion
is classified by the relation lattice.  Prove a matching lower bound and a
transfer stable under quasi-local dressing or a named microscopic Anderson
ensemble.  The completed-curvature theorem may be formalized as supporting
infrastructure, but it cannot carry the novelty claim.
