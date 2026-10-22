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

### Proved lower boundary of P2

The finite-horizon continuity mechanism is now unconditional in every
unital \(C^*\)-algebra.  For self-adjoint \(H,K\), arbitrary bounded
observable \(O\), and real \(t\),
\[
 \|e^{-itH}Oe^{itH}-e^{-itK}Oe^{itK}\|
 \leq 2|t|\|H-K\|\|O\|.                              \tag{P2.1}
\]
Hence resolving a difference \(\varepsilon\) requires
\[
 |t|\geq
 \frac{\varepsilon}{2\|H-K\|\|O\|}.                 \tag{P2.2}
\]
The result is dimension-free and operator-normalized.  It proves fixed-time
stability and the inverse-coupling lower activation scale, but not the
causal-volume upper/lower laws or maximal completed dimension.

Formal source:
`formal/GaloisForLFunctions/HTGeometry/FiniteHorizonCStarPerturbationLaw.lean`.

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

Closest checked quantum-recurrence parents:

- Riddell--Pagliaroli--Alhambra,
  `arXiv:2206.07541`, derive concentration and doubly exponential recurrence
  lower bounds under a generic-spectrum condition. Their genericity argument
  is for the full Hermitian matrix space; it does not prove that a
  geometrically local interaction family contains a witness, nor the
  one-knob weak-coupling singularity.
- Riddell--Bertini, `arXiv:2404.12100`, construct rationally independent
  *single-particle* spectra with local free-fermion hopping. Their many-body
  additive structure remains detectable in higher spectral-form-factor
  moments. This is a close integrable boundary, not P1's maximal
  \(q^n-1\) interacting many-body projective rank.
- Huang--Tong--Fang--Su, `arXiv:2210.03030`, achieve and lower-bound
  \(O(\varepsilon^{-1})\) total evolution time for active many-body
  Hamiltonian learning. This is operationally adjacent to `(P2.2)`, but it
  neither identifies completed recurrence geometry nor proves its
  discontinuous activation at nonzero coupling.

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
4. Extend the proved C⋆ operator metric to one intervention-complete
   operational pseudometric.
5. Prove an upper causal-volume activation law and construct a matching lower
   family.
6. Extend the finite relation groups to an inverse system for infinite
   lattices.
7. Audit P1--P3 theorem by theorem against external literature.
8. Let a hostile general-journal review decide whether the joined theorem is
   a universal physical law or a new mathematical many-body theorem.

## Novelty-finder reset: seek the law whose results are shadows

The search must not promote the strongest theorem currently within reach.
Theorems, observations and no-gos are data.  Default move:

1. conjecture a reinterpretation with a more universal primitive;
2. require an exact recovery map from that primitive to every claimed shadow;
3. attack the reinterpretation against the strongest external parent;
4. retain it only if one recovery theorem is genuinely new and
   parameter-reducing.

This reverses the earlier workflow.  P1 and `(P2.1)`--`(P2.2)` are evidence
for a law, not the law itself.

## Jump J1 — relation--metric recurrence duality

The current best mathematical jump replaces “recurrence rank” and
“rate--distortion entropy” by one exact object.

Let \(K\) be the minimal compact observable return group, let \(d\) be its
translation-invariant observer metric after quotienting the zero-distance
subgroup, let \(m\) be Haar probability and put
\[
 B_\varepsilon=\{k\in K:d(k,0)<\varepsilon\}.
\]
For \(\alpha\in K\), define the first observer return
\[
 \tau_\varepsilon(\alpha)
 =\min\{n\geq1:d(n\alpha,0)<\varepsilon\}.
\]
Write \(N_\delta(K,d)\) for the least number of open
\(\delta\)-balls covering \(K\).

### Universal metric-return theorem target

For every compact metrizable group with invariant metric,
\[
 \tau_\varepsilon(\alpha)
 \leq N_{\varepsilon/2}(K,d)                         \tag{J1.1}
\]
for every \(\alpha\).  Indeed, two of
\(0,\alpha,\ldots,N_{\varepsilon/2}\alpha\) lie in one
\(\varepsilon/2\)-ball, and invariance translates their collision to a
return to zero.

For every nontrivial compact connected metrizable abelian group, define the
worst dense-orbit return
\[
 \tau_\varepsilon^\star
 =\sup_{\overline{\mathbb Z\alpha}=K}
 \tau_\varepsilon(\alpha).
\]
The proposed sharp scale-shift law is
\[
 \boxed{
 \left\lceil\frac1{m(B_\varepsilon)}\right\rceil
 \leq \tau_\varepsilon^\star
 \leq N_{\varepsilon/2}(K,d)
 \leq \frac1{m(B_{\varepsilon/4})}.}                  \tag{J1.2}
\]
The left inequality follows by choosing a Haar-generic dense generator
outside the finitely many inverse images
\(\{\alpha:n\alpha\in B_\varepsilon\}\); connectedness makes multiplication
by every positive integer Haar-preserving.  The final inequality follows
from a maximal \(\varepsilon/2\)-separated set whose
\(\varepsilon/4\)-balls are disjoint.

The complete chain is paper-proved.  The covering deadline `(J1.1)` and the
general conull Haar-budget lower mechanism are Lean-proved in
`CompactGroupMetricReturnLaw.lean`.  The connected-group
full-measure-dense-generator corollary and the final covering-volume
inequality are not yet Lean-proved, so the boxed chain `(J1.2)` is not yet a
manuscript theorem.

Its important feature is exactness at neighboring resolutions.  It does not
replace a dimension-linear error by a hidden dimension-dependent constant:
\[
 \text{worst return}
 \quad\leftrightarrow\quad
 \text{inverse target volume}
 \quad\leftrightarrow\quad
 \text{covering complexity}
\]
with only the explicit scale change
\(\varepsilon\mapsto\varepsilon/4\).

### Existing laws recovered as shadows

| Shadow | Recovery from \((K,d,m)\) |
|---|---|
| exact periodicity | the orbit generator is torsion |
| quasiperiodic recurrence | a dense rotation on \(K\) |
| rational spectral rank | Lie dimension when \(K\) is a finite torus |
| observer coherence rank | dimension of the quotient by the metric kernel |
| reverse-water entropy | finite weighted-torus estimate of \(-\log m(B_\varepsilon)\) |
| worst-spectrum minimax exponent | `(J1.2)` plus finite-torus ball asymptotics |
| countable pure-point recurrence | compact metrizability of the dual of the countable visible-frequency group |
| solenoidal return | finite-rank non-finitely-generated frequency groups give non-toral \(K\) |
| infinite temporal dimension | an infinite-rank dual inverse limit; every fixed-resolution cover remains finite |
| finite contraction ceiling | apply the return group to the reversible peripheral factor; stable mass fixes the ceiling |
| observer restriction | quotient \(K\) by a closed zero-distance subgroup |
| local-moment no-go | a finite observable prefix does not determine the completed metric group |

The table is a derivation obligation.  A row enters the paper only after its
recovery theorem is proved and formalized.

## Jump J2 — interaction changes the return object, not merely the spectrum

For a \(D\)-level Hamiltonian let \(R_H\) be the balanced integer relation
lattice of its energies and let
\[
 \Gamma_H=\mathbb Z^D/(\mathbb Z{\bf1}+R_H),\qquad
 K_H=\widehat{\Gamma_H}.
\]
The uncoupled tensor law gives
\(\operatorname{rank}\Gamma_H\leq n(q-1)\).  The target local-interaction
theorem gives
\(\Gamma_H\cong\mathbb Z^{q^n-1}\) for almost every nearest-neighbour
Hamiltonian.

The reinterpretation is stronger than “generic gaps are independent”:

> **Interaction changes the minimal space in which the complete observable
> future can return.  Observation chooses a metric quotient of that space;
> dissipation chooses its surviving factor; target volume sets the minimax
> waiting time.**

Along a one-knob perturbation \(H_g=H_0+gV\), the exact return object can jump
for every nonzero \(g\) outside a countable exceptional set, while
`(P2.1)` gives
\[
 \sup_{|t|\leq T}
 \|O_{H_g}(t)-O_{H_0}(t)\|
 \leq 2T|g|\|V\|\|O\|.                               \tag{J2.1}
\]
Thus exact completion and zero coupling do not commute, but finite-time
physics remains continuous.  If the local maximality theorem closes, this
gives a new joined consequence:
\[
 \boxed{
 \text{arbitrarily weak local interaction changes exact return complexity
 from linear to exponential, while detecting the change requires time
 at least of order }|g|^{-1}.}                         \tag{J2.2}
\]

The inverse-coupling bound alone is a standard perturbative speed limit.
The rank jump alone is an algebraic genericity statement.  Candidate novelty
is their recovery from one return object and their simultaneous realization
inside a physical bounded-degree local family.

## Hostile parent attack on J1--J2

J1 uses classical compactness, Haar measure, Pontryagin duality and Kronecker
rotation.  Quantitative recurrence versus local dimension, Bohr return sets,
metric entropy and Kac-type inverse-volume laws are established subjects.
Therefore `(J1.1)`--`(J1.2)` alone cannot carry a Nature claim even if the
exact scale-shift formulation is absent from searches.

Weak integrability breaking and prethermal plateaux already establish that a
small perturbation can have a late dynamical effect, often on
\(g^{-2}\) or longer scales.  J2 must not be advertised as discovery of
noncommuting weak-coupling and long-time limits.  It survives only if the
following exact conjunction is externally new:

1. every finite and countable pure-point reporter is represented by the same
   minimal compact return object;
2. exact target volume and covering geometry give the two-resolution
   minimax law `(J1.2)`;
3. observer restriction and open-system survival are canonical
   quotient/factor operations on that object;
4. almost every bounded-degree local interacting Hamiltonian has maximal
   projective return group;
5. an arbitrarily weak one-knob local interaction realizes the full
   linear-to-exponential jump; and
6. operator-norm observations cannot detect that completed jump before the
   inverse-coupling scale.

Current verdict:

- **reinterpretive coherence:** pass;
- **infinite pure-point universality:** plausible and exact;
- **worst-spectrum minimax framing:** materially stronger;
- **dimension-linear remainder:** removed at the universal level by the
  neighboring-resolution law;
- **arbitrary continuous spectrum:** not covered;
- **arbitrary open dynamics:** not covered;
- **physical local maximality:** open;
- **external priority:** open;
- **Nature gate:** closed.

J1--J2 is therefore the next theorem programme, not yet the paper headline.

## 2026-07-30 reinterpretation-first novelty gate

Novelty search now uses one hard rule: seek a primitive law under which several
established theorems, observations, and no-go results become necessary shadows.
A renamed conjunction does not qualify. The current candidate primitive is the
**relation--observation duality**:

1. exact integer relations determine the compact return object and its metric
   recurrence complexity;
2. observer restriction quotients that relation object;
3. interaction changes the exact relation object discontinuously;
4. finite-time operator observations change continuously, with detection time
   bounded below by inverse coupling;
5. open evolution retains only the nondecaying observable factor.

This is still a research conjecture, not a manuscript claim. Its key physical
local-interaction bridge advanced today: the exact diagonal-probe transition
law and one-sided nonvanishing corollary are now Lean-proved in
`AffineEigenbranchDiagonalProbeLaw.lean`. They show, without phase assumptions,
how an arbitrarily weak local interaction creates endpoint-observable
cross-block transitions. Qubit same-layer transition creation remains the
single explicit endpoint-geometry gap before the all-path local maximal-rank
theorem can be promoted.

## 2026-07-30 hostile external parent collision

Two checked parents materially narrow novelty:

- L. Campos Venuti, *The recurrence time in quantum mechanics* (2015),
  arXiv:1509.04352, already states that any nonzero generic
  nonintegrable perturbation restores rational independence with probability
  one, changes recurrence from exponential to double exponential, and makes
  recurrence time discontinuous at the integrable point (paper lines 94--113).
  Therefore “arbitrarily weak interaction changes recurrence discontinuously”
  is occupied and cannot be the headline.
- M. J. W. Hall, *Almost-periodic time observables for bound quantum systems*
  (2008), arXiv:0803.3721, already constructs time observables for arbitrary
  discrete spectra using almost-periodic measures and energy-gap Fourier
  modes. Therefore “discrete quantum histories are almost periodic” and
  “almost-periodicity defines a time observable” are occupied.

Survivor requiring a stricter novelty audit: an observer-indexed **minimal
compact clock theorem**. Proposed invariant is the Pontryagin dual of the
frequency group visible to the observer's entire history algebra; its rank is
the least number of independent phase coordinates through which all those
histories factor. Required genuinely new consequences are exact quotient/data-
processing laws under observer restriction and a proved exponential local-
interaction amplification theorem. Classical almost-periodic hull and
Pontryagin-duality results must be presented only as parents, not novelty.
