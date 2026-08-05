# Universal static Choi complexity plateau

- **ID:** universal-static-choi-complexity-plateau
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[PROVED HERE]` `[FORMALIZED]`; equations (1)-(5) and the fixed-`q` Pauli
  Gaussian almost-sure plateau are closed in Lean with no spectral premise, umbrella builds
  green, axioms audited
- **Role:** closes the geometric and completed-time parts of O3 in
  `../1-in-progress/static-local-complexity-law.md`

## Result

Let `H` be a Hermitian operator on a complex Hilbert space of dimension
`D >= 2`, with orthonormal eigenbasis `(e_j)` and eigenvalues `(E_j)`.  Write

\[
  \Phi_H(t)=D^{-1/2}\sum_{j=1}^D e^{-itE_j}
       e_j\otimes\overline{e_j}.
\]

This is the Choi state of `e^{-itH}`.  More generally, for
`z in T^D`, set

\[
  \Phi(z)=D^{-1/2}\sum_{j=1}^D z_j
       e_j\otimes\overline{e_j}.
\]

Let `Delta` be pure-state trace distance.  Fix `0 < delta < 1/2` and put

\[
  \eta_\delta=1-\sqrt{1-4\delta^2},\qquad
  B_D(\delta)=D e^{D/2}
      \left({\pi\eta_\delta\over2}\right)^{(D-1)/2}.
\]

Then, for every normalized target state `psi`, independently of the
eigenbasis,

\[
  \mu_{\mathbb T^D}\{z:\Delta(\Phi(z),\psi)\leq\delta\}
  \leq B_D(\delta).                                      \tag{1}
\]

Consequently, for every finite target dictionary `A`,

\[
  \mu_{\mathbb T^D}\{z:\exists\psi\in A,\
       \Delta(\Phi(z),\psi)\leq\delta\}
  \leq |A|B_D(\delta).                                   \tag{2}
\]

Let a discrete local gate alphabet offer at most `M >= 2` labelled gate
choices at every circuit step.  Circuits of length at most `s` produce at
most `M^(s+1)` target states, so

\[
  \mu_{\mathbb T^D}\{z:C_\delta(\Phi(z))\leq s\}
  \leq M^{s+1}B_D(\delta).                                \tag{3}
\]

For every fixed `delta` satisfying

\[
  \kappa_\delta:=-{1\over2}
      -{1\over2}\log\!\left({\pi\eta_\delta\over2}\right)>0,
\]

the right-hand side of (3) is exponentially small in `D` whenever
`s <= c_delta D / log M`, apart from the explicit lower-order `log D` term.
For local gates on `2n` qubits, `log M=O(log n)`, hence completed-time
complexity is `Omega(2^n/log n)` for all but `exp(-Omega(2^n))` of phase
time.

If the projective gaps of `H` are rationally independent, the phase flow is
uniquely ergodic on the projective torus.  Since the finite-circuit target in
(3) is closed, Portmanteau gives

\[
  \limsup_{T\to\infty}{1\over2T}
   \operatorname{Leb}\{t\in[-T,T]:C_\delta(\Phi_H(t))\leq s\}
  \leq M^{s+1}B_D(\delta).                                \tag{4}
\]

For the full-density fixed-`q` Pauli Gaussian ensemble with `q >= 2`, the
projective-gap premise holds almost surely by
`generic-two-local-spectral-monodromy.md`.  Equation (4) is therefore an
unconditional almost-sure static-local plateau law once that spectral theorem
is formally closed.

There is also an infinite-time topological strengthening.  Whenever the
right-hand side of (3) is strictly below one, there exists a finite
target-dependent `L` such that

\[
  \forall a\in\mathbb R\quad\exists t\in[a,a+L]\quad
  C_\delta(\Phi_H(t))>s.                                \tag{5}
\]

Thus hard endpoints are syndetic: no interval longer than `L` can consist
entirely of low-complexity endpoints.  Equation (5) holds for every maximally
projective spectrum, for all time, without a mixing-rate or randomness
premise.  It does not quantify `L`.

## Proof

### 1. A target ball is contained in one translated coherence target

If the left-hand target of (1) is empty there is nothing to prove.  Otherwise
choose `y` in it.  For any other `z` in the target, the triangle inequality
for pure-state trace distance gives

\[
  \Delta(\Phi(z),\Phi(y))\leq 2\delta.
\]

For pure states,

\[
  \Delta(\Phi(z),\Phi(y))^2
   =1-|\langle\Phi(z),\Phi(y)\rangle|^2,
\]

and orthonormality gives

\[
  \langle\Phi(z),\Phi(y)\rangle
    ={1\over D}\sum_j z_j\overline{y_j}.
\]

Hence every `z` in the ball satisfies

\[
  1-\eta_\delta=\sqrt{1-4\delta^2}
  \leq\left|{1\over D}\sum_jz_j\overline{y_j}\right|.
\]

Coordinatewise multiplication by `conj(y)` preserves product Haar measure.
Thus the target ball has no more Haar mass than the equal-weight coherence
target at defect `eta_delta`.

### 2. Exact torus entropy bound

`UniversalPhaseCoherenceTargetMeasure.lean` proves for every finite index
type of cardinality `D` and every `eta > 0` that the equal-weight target has
Haar mass at most

\[
  D e^{D/2}\left({\pi\eta\over2}\right)^{(D-1)/2}.
\]

Applying it at `eta=eta_delta` proves (1).  Finite subadditivity proves (2).

### 3. Circuit union

A length-`ell` circuit is one word of length `ell` in at most `M` labelled
gate choices.  The number of words of length at most `s` is at most
`M^(s+1)` for `M >= 2`.  Apply (2) to the output states of those words to get
(3).  Taking logarithms gives the exact exponent

\[
  (s+1)\log M+\log D-\kappa_\delta(D-1)+{1\over2}.
\]

This has no hidden dimension-linear remainder.

### 4. Static completed time

Projective rational independence makes the deterministic phase flow converge
weakly to normalized Haar measure on the projective torus.  Fidelity and
circuit balls are global-phase invariant, so their projective Haar mass equals
their full-torus Haar mass.  A finite union of closed trace-distance balls is
closed.  The closed-set half of Portmanteau therefore turns (3) into (4).

### 5. Syndetic hard endpoints

If the bound in (3) is below one, the closed low-circuit target cannot fill
the projective torus, so its complement is nonempty and open.  Projective
rational independence makes the physical one-parameter phase subgroup dense.
The translates of any nonempty open target by a dense subgroup cover the
compact torus; compactness selects finitely many translates.  The diameter of
their time parameters supplies one finite inclusion length `L`, proving (5).

This is stronger than an average-frequency argument.  A set may have positive
or even near-unit asymptotic density while retaining arbitrarily long gaps;
compact minimal rotation forbids those gaps for every nonempty open target.

## What this closes and what it does not

This theorem closes a robust maximal-complexity **occupation plateau** for the
static Choi/thermofield-double trajectory.  It needs no Haar-random eigenbasis,
unitary design, ETH, mixing, stochastic drive, or complexity-class separation.
It is compatible with an efficient all-time non-Haar locality witness.

It does **not** prove pointwise linear growth from time zero, an exponentially
late first cut, or a doubly exponential first low-complexity recurrence.
Equation (5) gives a finite first hard time and bounded gaps, but no useful
upper bound on `L`; `L` can depend on fine Diophantine properties of the
spectrum.  Quantitative first hitting remains O4/O5 of the master card.

## Initial collision audit

- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove saturation and recurrence
  for random circuits and stochastic local Hamiltonians using approximate
  equidistribution on the ambient state/unitary spaces.  They explicitly state
  that a concrete time-independent Hamiltonian remains out of reach.
- Kotowski--Oszmaniec--Horodecki treat static random-matrix Hamiltonians; their
  ensemble is nonlocal and its eigenbasis randomness is load-bearing.
- Guo--Sasieta--Swingle already occupy the slogan that complexity need not be
  randomness.  Novelty here is the eigenbasis-free spectral-torus bound and
  its deterministic static-local completed-time consequence, not that slogan.

Exact-title and mechanism searches found no theorem giving (1)--(5) for every
eigenbasis and static Hamiltonian with full projective spectral rank.  This is
an initial clean audit, not the final citation-graph/expert audit.

## Formalization status

Completed and compiled in the foreground:

1. `StaticChoiPhaseDensity.lean` defines the equal-weight phase density,
   proves its exact Hilbert--Schmidt/fidelity identity, and proves that a
   Hilbert--Schmidt displacement bound forces membership in a translated
   coherence cap.
2. `StaticChoiPhaseTargetEntropy.lean` proves translation invariance,
   arbitrary metric-ball domination, controlled-target entropy, finite-union
   entropy, and the exact padded circuit-word factor `|gate|^(s+1)`.
3. `StaticChoiComplexityPlateau.lean` combines those layers into explicit
   finite-dictionary and padded-circuit Choi plateau bounds; its error defect
   is exactly `2 * delta^2` for Hilbert--Schmidt radius `delta`.  Its theorem
   `completedTime_iUnion_uniformPhaseDensity_paddedCircuitTargets` now also
   applies the closed-target Portmanteau law and returns both the completed-time
   occupation bound and the explicit Haar-volume bound.
4. `FiniteSpectralRecurrenceFrequencyLaw.lean` supplies the generic
   closed-target Portmanteau upper-frequency theorem used by that capstone.
5. `StaticChoiProjectiveComplexityPlateau.lean` removes the otherwise fatal
   full-frequency assumption.  It splits normalized Haar measure exactly into
   global and zero-anchored projective phase, proves Choi density invariant on
   the global factor, transfers the entire finite circuit union without losing
   overlaps, and derives physical relative-frequency independence from maximal
   projective rank.  Its completed-time theorem therefore applies to traceless
   Hamiltonians.
6. `SyndeticDenseOrbitLaw.lean` proves that every dense real subgroup of every
   compact topological group hits every nonempty open target in all intervals
   of one finite length.  `StaticChoiSyndeticComplexityLaw.lean` combines that
   result with the explicit circuit entropy bound and maximal projective rank
   to prove (5).  Its headline theorem and the operator-norm cone theorems have
   been audited with `#print axioms`; they use only `propext`,
   `Classical.choice`, and `Quot.sound`.
7. `StaticChoiFullStateProjectionLaw.lean` removes the spectral-subspace target
   surrogate.  It proves that diagonal--diagonal restriction from the actual
   `D^2`-dimensional Choi density space is Hilbert--Schmidt contractive and
   that the evolved full density restricts exactly to `uniformPhaseDensity`.
   Its headline theorem therefore establishes (5) against arbitrary full
   circuit-target density matrices, with no dimension or radius loss.
8. `StaticChoiTraceDistanceLaw.lean` proves directly from finite coordinates
   that Hilbert--Schmidt distance between normalized pure-state densities is
   exactly `sqrt 2` times operational pure-state trace distance.  It identifies
   `fullUniformPhaseChoiDensity` with the density of a normalized physical Choi
   vector and transfers the syndetic theorem to normalized pure circuit
   targets with the exact radius conversion and no dimension loss.
9. `SyndeticDenseOrbitLaw.lean` now proves the ordered two-regime alternation
   theorem: every dense real flow on every compact group passes from either
   nonempty open regime to a disjoint second regime and back, with one finite
   upper bound on every leg after every starting time.
   `StaticChoiComplexityAlternationLaw.lean` specializes it to an ordered
   operational recurrence--circuit-hardness--recurrence cycle in trace
   distance.  All three times are strictly ordered and the cycle repeats
   forever.
10. `FiniteAndersonChoiComplexityAlternationLaw.lean` transfers the ordered
    law to the standard finite Anderson family.  Combined with the existing
    `finiteAndersonProjectiveMaximalSet_dense_residual_fullMeasure`, it applies
    to a dense, residual, full-Lebesgue-measure set of onsite potentials for
    every fixed finite Hermitian hopping matrix.  The headline theorem was
    audited with `#print axioms`; it uses only `propext`,
    `Classical.choice`, and `Quot.sound`.

11. `PiMeasureAbsoluteContinuity.lean` proves that a coordinatewise absolutely
    continuous family of sigma-finite measures has absolutely continuous finite
    product, and specializes it to a nondegenerate product Gaussian on a finite
    real coordinate space.
12. `PauliTracelessChoiComplexityPlateauLaw.lean` closes the card's own
    ensemble.  It relabels the eigenvalue family of a real combination of
    nonidentity Pauli strings of weight at most `q` from computational
    configurations to `Fin (2^n)`, imports the maximal projective rank already
    proved for that ensemble in `generic-two-local-spectral-monodromy.md`, and
    instantiates the completed-time occupation bound (4), the syndetic
    trace-distance hardness law (5) and the ordered alternation law.  Both a
    generic-set form and an almost-sure form for every full-density coefficient
    law are proved, and the almost-sure form is then instantiated at a
    nondegenerate product Gaussian.  Equation (4) is therefore now an
    unconditional almost-sure static-local plateau law for the fixed-`q` Pauli
    Gaussian ensemble with `q >= 2`, with no remaining spectral premise.  All
    headline theorems were audited with `#print axioms`; they use only
    `propext`, `Classical.choice`, and `Quot.sound`.

Remaining before stage 4:

1. Any quantitative claim about the common alternation gap `L`, first hard
   time, linear cut time, or first low-complexity recurrence remains outside
   this theorem.  Those require new Diophantine/no-shortcut input.
2. A fixed-`q` many-body nearest-neighbour qudit chain is a different ensemble
   from the fixed-weight Pauli ensemble proved here; it is not claimed by this
   card and its genericity proof is not manuscript-authorized.

## Lean formalization map

| Paper item | Lean declaration | Module |
|---|---|---|
| torus entropy bound (1) | `UniversalPhaseCoherenceTargetMeasure` | `HTGeometry` |
| translated coherence cap | `StaticChoiPhaseDensity` | `RHTower` |
| finite dictionary (2), circuit union (3) | `StaticChoiPhaseTargetEntropy`, `StaticChoiComplexityPlateau` | `RHTower` |
| completed time (4) | `completedTime_zeroAnchoredPaddedCircuitTargets` | `RHTower.StaticChoiProjectiveComplexityPlateau` |
| syndetic hard endpoints (5) | `maximallyProjective_paddedCircuitHardTimes_syndetic`, `maximallyProjective_pureChoiTraceHardTimes_syndetic` | `RHTower.StaticChoiSyndeticComplexityLaw`, `RHTower.StaticChoiTraceDistanceLaw` |
| ordered alternation | `maximallyProjective_pureChoiComplexity_alternates_syndetically` | `RHTower.StaticChoiComplexityAlternationLaw` |
| finite Anderson family | `finiteAnderson_pureChoiComplexity_alternates_syndetically` | `RHTower.FiniteAndersonChoiComplexityAlternationLaw` |
| fixed-`q` Pauli register relabelling | `pauliRegisterEquiv`, `pauliTracelessChoiEnergy`, `maximallyProjective_pauliTracelessChoiEnergy` | `RHTower.PauliTracelessChoiComplexityPlateauLaw` |
| (4) for the Pauli ensemble | `pauliTraceless_completedTime_paddedCircuitTargets`, `pauliTraceless_completedTime_paddedCircuitTargets_ae` | `RHTower.PauliTracelessChoiComplexityPlateauLaw` |
| (5) for the Pauli ensemble | `pauliTraceless_pureChoiTraceHardTimes_syndetic` | `RHTower.PauliTracelessChoiComplexityPlateauLaw` |
| alternation for the Pauli ensemble | `pauliTraceless_pureChoiComplexity_alternates_syndetically`, `pauliTraceless_pureChoiComplexity_alternates_syndetically_ae` | `RHTower.PauliTracelessChoiComplexityPlateauLaw` |
| Gaussian ensemble instance | `pauliTracelessGaussian_pureChoiComplexity_alternates_syndetically_ae`, `pauliTracelessGaussian_completedTime_paddedCircuitTargets_ae` | `RHTower.PauliTracelessChoiComplexityPlateauLaw` |
| product absolute continuity | `pi_absolutelyContinuous_pi`, `productGaussian_absolutelyContinuous` | `HTGeometry.PiMeasureAbsoluteContinuity` |
