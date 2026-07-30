# The predictive-relation spectrum

- **ID:** `predictive-relation-spectrum-universal-law`
- **Stage:** 1-in-progress
- **Type:** ABDUCTIVE MASTER CONJECTURE / DYNAMICAL SYSTEMS / QUANTUM
  MANY-BODY THEORY / OBSERVABILITY / RECURRENCE
- **Scientific status:** `[CONJECTURE] [CORPUS-SYNTHESIS]`
  `[CLASSICAL PARENTS IDENTIFIED] [NOVEL PHYSICAL THEOREM OPEN]`
- **Freeze date:** 2026-07-30

Novelty is judged only against external literature. Internal results are
evidence and constraints, never priority evidence.

## Strongest present hunch

The corpus keeps treating time, recurrence, memory, observer dependence,
hypertranscendence, causal horizons and failed geometric gluing as separate
objects. The recurring primitive is more general:

> **Physical temporal structure is the minimal intervention-stable predictive
> closure of the distinctions an observer can make.**

Equivalently:

> **Dynamics changes the exact relations among observable futures.
> Interaction removes relations; restriction and dissipation add them;
> locality limits how quickly the change can become observable.**

The candidate invariant is not one dimension. It is the complete
**predictive-relation spectrum**: exact relations, their depth of failure, their
finite-resolution persistence, and the comparison maps induced by changing
observer or intervention set.

This is a conjectural interpretation. It is not yet a manuscript claim.

## Exact operational starting point

Let `Hist` be a set of operational histories. For a history \(h\), a future
intervention script \(a\) and horizon \(T\), let
\[
  P_h^{a,T}
\]
be the resulting future-output probability law. Choose an operational
distance \(d\) on output laws and define the horizon-\(T\) predictive
pseudometric
\[
 d_T(h,h')
 =
 \sup_{a\in\mathcal I_{\leq T}}
 d(P_h^{a,T},P_{h'}^{a,T}).                         \tag{1}
\]
The exact future-equivalence relation is
\[
 h\sim_\infty h'
 \quad\Longleftrightarrow\quad
 d_T(h,h')=0\ \text{for every finite }T.             \tag{2}
\]
The quotient
\[
 \mathcal X_{\rm pred}=\operatorname{Hist}/{\sim_\infty}   \tag{3}
\]
is the candidate exact predictive state object.

For \(\varepsilon>0\), the relation \(d_T\leq\varepsilon\) need not be
transitive. The robust object is therefore not an approximate quotient but
the covering profile
\[
 \mathcal C(\varepsilon,T)
 =
 \log N_\varepsilon(\operatorname{Hist},d_T),         \tag{4}
\]
or its source-restricted analogue. The pair
\[
 \mathfrak P
 =
 \bigl(
 \mathcal X_{\rm pred},
 \mathcal C(\varepsilon,T),
 \text{observer/intervention comparison maps}
 \bigr)                                               \tag{5}
\]
is the predictive-relation spectrum.

Equations `(1)`--`(5)` are definitions, not discoveries. Causal states,
Nerode equivalence, minimal realization, predictive rate--distortion,
Koopman closure and Mori--Zwanzig reduction occupy major parts of this
territory.

## Why exact dimension alone was insufficient

Several corpus results force two different boundaries to be retained.

1. Exact relations are singular. An arbitrarily small generic interaction
   can remove an integer spectral relation and change an exact temporal rank
   discontinuously.
2. Every fixed finite-horizon record varies continuously under a small
   Hamiltonian perturbation.
3. Exact local moments or arbitrarily many perturbative coefficients can fail
   to determine completed recurrence.
4. A common bounded-generator prefix controls every response inside an
   energy--time causal horizon.
5. Hypertranscendence can force infinite algebraic closure while a positive
   norm suppresses higher grades enough to keep finite operational capacity.

Thus exact rank and operational complexity are different boundary values of
one scale-dependent object. A physically meaningful law must retain
\(\varepsilon\), \(T\), coupling strength, system size and observer scope
before taking limits.

## The central noncommutation

Let \(Q\) be observer restriction and
\(\operatorname{Cl}_D\) the least closure under dynamics and allowed
interventions. There are two operations:

\[
 \operatorname{Cl}_{QD}(Q\mathcal O)
 \qquad\text{and}\qquad
 Q\operatorname{Cl}_D(\mathcal O).                    \tag{6}
\]

Their comparison is the **predictive descent map**. Its failure to be an
isomorphism is the **predictive closure defect**.

In elementary linear form, if \(Q:X\to Y\) is an observation quotient and
\(D:X\to X\) is dynamics, an autonomous quotient dynamics exists exactly when
\[
 D(\ker Q)\subseteq\ker Q.                            \tag{7}
\]
The sequence
\[
 QD^k|_{\ker Q},\qquad k=1,2,\ldots                   \tag{8}
\]
records the depths at which currently invisible distinctions re-enter the
future. This is the simplest shadow of the proposed defect.

Condition `(7)` and related minimal-realization constructions are known.
Novelty requires a theorem identifying the same defect, with one compatible
composition law, across the recurrence and interaction results below.

## What the corpus is pointing toward

| Corpus phenomenon | Predictive-relation reading |
|---|---|
| observer coherence graph | exact quotient of visible phase relations |
| rational spectral rank | dimension of reversible predictive closure |
| recurrence | simultaneous rephasing of surviving independent relations |
| replica collision hierarchy | all-order statistics of the completed visible gap law |
| contraction peripheral sector | maximal asymptotically lossless predictive quotient |
| transient sector | distinctions erased by dissipation |
| local common moments | finite-depth predictive agreement |
| bounded-generator causal horizon | speed limit for operational relation breaking |
| generic local spectral maximality | interaction removes every non-trace projective relation |
| weak-coupling singularity | exact completion and zero-coupling limit do not commute |
| hypertranscendence | failure of finite differential closure, not automatically large metric capacity |
| relational clock twirl | observer restriction adds exact relations by quotienting a clock action |
| dynamics underdetermination | passive histories do not choose an interventional law |
| fixed-carrier flatness | globally supplied comparison coordinates trivialize holonomy |

The repeated message is:

```text
present observations define relations
        ↓ dynamics and interventions test them
minimal predictive closure retains only consequential distinctions
        ↓ observer restriction / dissipation / locality
relation spectrum determines memory, recurrence and operational time
```

## Conjecture P1 — interaction-induced predictive incompressibility

For every finite local alphabet and every connected bounded-degree
interaction graph, almost every unrestricted one- and edge-local Hermitian
Hamiltonian has maximal projective spectral relation rank. For every
observer coherence graph \(G\), the same Hamiltonian simultaneously gives
the maximal reversible predictive dimension allowed by \(G\).

For an uncoupled \(n\)-site \(q\)-level system this exact dimension is at most
\[
 n(q-1),
\]
whereas generic local interaction gives
\[
 q^n-1
\]
globally. Along a suitable one-knob line leaving any uncoupled point, the
maximal value holds outside a countable exceptional coupling set, including
arbitrarily weak nonzero couplings.

**Public consequence if proved:**

> **Any generic local interaction, however weak, destroys exact compression
> of the complete quantum future.**

**Falsifiers:** a connected graph and local alphabet with a forced non-trace
rational spectral relation; failure of the physical local witness; an
external theorem already proving the same or a stronger result.

## Conjecture P2 — causal activation of the singular exact future

The discontinuity in P1 is invisible at fixed finite horizon. There is a
source-normalized operational complexity profile
\(\mathcal C_{H,g}(\varepsilon,T)\) such that:

1. for fixed \(\varepsilon,T\),
   \(\mathcal C_{H,g}(\varepsilon,T)\) is stable as \(g\to0\);
2. for every generic nonzero \(g\), its exact completed boundary has maximal
   dimension;
3. locality bounds the growth of
   \(\mathcal C_{H,g}(\varepsilon,T)\) by the observer's causal volume;
4. a matching local family attains the causal-volume order.

The exact and operational limits therefore fail to commute:
\[
 \text{zero coupling}
 \quad\text{and}\quad
 \text{infinite precision/infinite horizon}.          \tag{9}
\]

This would convert the exact rank jump into a physical scale-separation law
rather than metaphysical rhetoric.

**Falsifiers:** no source-independent operational metric with stability and
composition; a locality-respecting family whose complexity activates outside
every causal-volume bound; absence of a matching lower family.

## Conjecture P3 — infinite-volume temporal inexhaustibility

For generic finite-range interactions on an infinite connected lattice, a
separating net of finite-region reporters has no finite exact predictive
closure. Its finite-volume reversible ranks grow maximally, while at fixed
resolution the operational complexity grows only through the causal region
reached by the reporter.

This is the honest infinite extension of P1. It does not say that coordinate
time has infinitely many axes. It says no fixed finite autonomous phase
machine reproduces every exact future distinction exposed by the observer
net.

**Falsifiers:** generic symmetries or quasi-local reductions that uniformly
bound the exact reporter closure; failure of compatible finite-volume
restriction maps; dependence on a nonphysical completion.

## Conjecture P4 — arrow as predictive nonreciprocity

Let \(\mathfrak P^+\) and \(\mathfrak P^-\) be the future-predictive and
past-retrodictive relation spectra for the same intervention class. The
operational arrow is not spectral nonreturn. It is the failure of these two
spectra to be isomorphic under reversal:
\[
 \mathfrak A
 =
 \mathfrak P^+\ominus\mathfrak P^-.                  \tag{10}
\]
For reversible closed dynamics with reversal-compatible interventions,
\(\mathfrak A=0\). For irreversible record-forming dynamics, a suitable
finite-resolution density of \(\mathfrak A\) equals or bounds entropy
production.

Forward/reverse causal states and causal irreversibility are close parents.
Novelty requires an exact quantum/interventional theorem joined to the same
relation spectrum, not a new name.

**Falsifiers:** irreversible entropy production with isomorphic spectra under
the physically fixed intervention metric; reversible dynamics with a
nonzero invariant after representation gauge is removed.

## Conjecture P5 — horizon as exterior predictive-descent defect

For a global theory and exterior observer net, compare global predictive
closure restricted to the exterior with predictive closure formed entirely
from exterior interventions. A horizon carries a nontrivial defect when these
objects do not agree.

The wild quantitative conjecture is that a gravitationally normalized
finite-resolution fiber-growth rate of this defect equals generalized
entropy:
\[
 S_{\rm gen}
 =
 \lim_{\varepsilon\downarrow\varepsilon_{\rm grav}}
 \log N_\varepsilon(
   \text{global predictive fibers over exterior histories}
 ).                                                    \tag{11}
\]

Pure-point versus continuous spectrum cannot characterize horizons; the
corpus already found counterexamples in both directions. Equation `(11)`
replaces spectral type by failure of faithful predictive descent.

**Falsifiers:** horizonless systems with the same defect after locality,
gauge and intervention structure are fixed; black-hole models with faithful
descent and nonzero generalized entropy; regulator or representation
dependence of the proposed fiber growth.

`P5` has no proof route and is not part of the finite recurrence paper.

## Conjecture P6 — spacetime as gluing geometry of predictive closure

Let local observer/intervention domains carry their minimal predictive
closures and comparison maps on overlaps. The boldest corpus-driven
conjecture is:

> **Spacetime geometry is the gluing geometry of locally minimal predictive
> laws; gravitational curvature is the obstruction to trivializing their
> comparison maps in one global predictive carrier.**

The fixed-carrier flatness results are negative evidence of the right kind:
global wall coordinates, one fixed projection carrier and arbitrary typed
diamonds either become exact coboundaries, path-flat, or universal carriers
that select no physics. Nonzero physical curvature must therefore use
source-calibrated local closures and comparison maps not supplied by one
global trivialization.

This resembles sheaf descent, contextuality and gauge theory. Those
frameworks are occupied. A discovery requires a source-derived comparison
law that uniquely recovers a known gravitational response and predicts a new
one.

**Falsifiers:** a faithful fixed global predictive carrier reproducing the
same proposed curvature invariant; dependence on presentation; inability to
derive one empirical gravitational response without assuming the geometry.

`P6` is a research programme, not a result.

## External occupied territory

The following are parents, not discoveries:

- causal states and minimal predictive sufficient statistics;
- future/Nerode equivalence and canonical automata;
- predictive and causal rate--distortion;
- observability rank and minimal state-space realization;
- Koopman-invariant observable closure;
- Mori--Zwanzig projection and memory kernels;
- maximal equicontinuous/Kronecker factors and Pontryagin duality;
- process tensors and instrument-specific quantum Markov order;
- sheaf/cohomological obstruction to global sections;
- quantum prethermalization and noncommuting long-time/weak-coupling limits;
- black-hole late-time spectral discreteness and nonperturbative plateaux.

Searches found no checked source joining these parents to the exact
local-interaction projective-rank transition, its all-observer recurrence
consequences and a causal finite-resolution activation law. Search absence is
not priority proof.

## Research judgement

The best present answer to “what has been missed?” is not yet a discovery:

> The scientifically missing object may be the full scale-dependent spectrum
> of relations among observable futures, rather than state, entropy,
> recurrence time, clock count or spectral type separately.

The strongest tractable new theorem is P1 plus P2. P3 is its infinite
extension. P4--P6 are increasingly wild physical conjectures and must not be
smuggled into a manuscript as interpretations of finite spectral theorems.

## Immediate theorem programme

1. Close the physical endpoint-local witness and prove P1 for path graphs.
2. Prove the one-knob arbitrarily weak interaction theorem.
3. Formalize the pure-point minimal carrier only as classical infrastructure.
4. Define one operational pseudometric from specified quantum interventions.
5. Prove an upper causal-volume activation law and construct a matching lower
   family.
6. Extend the finite relation groups to an inverse system for infinite
   lattices.
7. Audit P1--P3 theorem by theorem against external literature.
8. Let a hostile general-journal review decide whether the joined theorem is
   a universal physical law or a new mathematical many-body theorem.

