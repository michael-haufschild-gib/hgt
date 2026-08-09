# The temporal-codimension law of quantum recurrence

- **ID:** `temporal-codimension-interaction-law`
- **Stage:** 1-in-progress
- **Type:** FROZEN MASTER CONJECTURE / UNIVERSAL RECURRENCE LAW /
  OBSERVER--INTERACTION TEMPORAL GEOMETRY
- **Frozen:** `2026-07-29`
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOVELTY UNVERIFIED]`
- **Master-paper role:** proposed replacement for
  `universal-quantum-recurrence-anatomy`
- **Component candidate:** `local-interaction-recurrence-rank-explosion-law`

> **Supersession note (2026-07-29).** This remains a component theorem, but
> is no longer the strongest master organization. The higher candidate is
> `universal-replica-collision-law-of-quantum-return.md`: temporal dimension
> becomes a derived upper-tail invariant of the complete replica-collision
> return law, while local interaction is characterized by simultaneous
> minimization of every return moment.

## Public discovery

> **Time has an observer-dependent dimension, and interaction creates it.**

This does not change the coordinate dimension of spacetime. A stationary law
may be written with one real parameter \(t\), but a physical reporter compares
many relative spectral phases. Their compact orbit is the reporter's
**temporal hull**. Its dimension is the number of rationally independent
relative clocks visible to that reporter.

The proposed law is:

> **A quantum history returns according to the codimension of its
> observer-visible temporal hull. Generic local interaction makes that
> codimension exponentially large.**

The first sentence supplies the universal classification. The second supplies
the new many-body prediction: an arbitrarily weak generic interaction changes
the asymptotic recurrence clock from local scale to Hilbert-space scale.

## Corpus closure discovered after freeze

The universal observer/spectrum foundation is already unconditionally
formalized in the current corpus. In particular:

- `ObserverTemporalDimensionLaw.lean` defines cardinal-valued temporal
  dimension for arbitrary finite or infinite visible frequency families,
  proves observer monotonicity, the exact cyclic-versus-dense return
  dichotomy, finite graph-capacity laws, atomless continuum dimension and
  zero-density positive-threshold return;
- `ObserverTemporalUniversalityLaw.lean` proves invariance under the common
  energy origin, one fixed finite Hamiltonian saturating every observer graph,
  and one fixed stationary spectrum with observer choices realizing temporal
  dimension zero and continuum;
- `ObserverRecurrenceDistributionLaw.lean` proves that every long-time
  fidelity moment is an additive gap-collision probability and that every
  continuous fidelity statistic has a long-time mean for every probability
  spectrum, finite or infinite.

These results close the kinematic “one object” foundation. They do not make
the paper novel: their formal status is an internal correctness control, and
the manuscript will neither mention formalization nor count it as scientific
significance. The candidate new discovery remains the physical generator
theorem: bounded-degree local interaction creates the maximal exponential
temporal dimension.

## Why this is not the earlier collage

Earlier manuscripts list several recurrence facts:

```text
peripheral mass -> weights -> observer graph -> collision hierarchy
```

The present conjecture asserts that these are not successive independent
layers. They are different operations on one object:

\[
  \text{observer-visible persistent temporal hull }K_{\mathcal O}.
\]

```text
common phase / clock origin       -> quotient of K_O
observer coarse graining          -> quotient of K_O
observer joining                  -> join of temporal modules
dissipation                       -> deletion of transient directions
interaction                       -> creation of independent directions
finite resolution                 -> neighbourhood of the return locus
recurrence density                -> Haar volume of that neighbourhood
waiting time                      -> transverse shrinking-target exponent
continuous spectrum               -> loss of positive-density compact return
```

Every old recurrence theorem must appear as a specialization of this one
geometry. No clause may survive merely because it can be placed beside the
others.

## Finite stationary setting

Let
\[
  H=\sum_{j=1}^{D} E_j P_j
\]
be a finite-dimensional self-adjoint Hamiltonian. Let
\(\mathcal O=\{(B_a,\lambda_a)\}_{a=1}^{N}\) be any finite nonzero family of
Hilbert--Schmidt reporters with \(\lambda_a>0\). Define
\[
  W_{ij}=\sum_a\lambda_a\|P_iB_aP_j\|_{\mathrm{HS}}^2
\]
and the exact displacement
\[
  Q_{\mathcal O}(t)
  =
  \sum_{i,j}W_{ij}
  \left|e^{-it(E_i-E_j)}-1\right|^2.                 \tag{1}
\]

Let \(M_{\mathcal O}\subset\mathbb R\) be the rational vector space generated
by all gaps \(E_i-E_j\) with \(W_{ij}>0\), and put
\[
  d_{\mathcal O}=\dim_{\mathbb Q}M_{\mathcal O}.      \tag{2}
\]
Let \(K_{\mathcal O}\) be the closure of the relative-phase orbit generated
by those gaps. It is the minimal compact connected abelian group through
which every reporter in \(\mathcal O\) factors. The common energy origin has
already been quotiented.

The displacement descends to a continuous nonnegative function
\(\mathcal Q_{\mathcal O}:K_{\mathcal O}\to\mathbb R_{\geq0}\). Define the
static return information
\[
  \mathcal I_{\mathcal O}(\varepsilon)
  =
  -\log m_{K_{\mathcal O}}
    \{z:\mathcal Q_{\mathcal O}(z)<\varepsilon\},     \tag{3}
\]
where \(m_{K_{\mathcal O}}\) is normalized Haar measure.

## Frozen master conjecture `[CONJECTURE]`

### I. Exact temporal-codimension law

For every finite stationary system and reporter family above, every target
whose boundary has Haar measure zero has exact asymptotic time density
\[
 \boxed{
 \operatorname{dens}
 \{t:Q_{\mathcal O}(t)<\varepsilon\}
 =
 e^{-\mathcal I_{\mathcal O}(\varepsilon)}.
 }                                                    \tag{4}
\]

If \(d_{\mathcal O}<\infty\), then the return locus is isolated in the
minimal hull and its Hessian is positive definite. Consequently
\[
 \boxed{
 \mathcal I_{\mathcal O}(\varepsilon)
 =
 \frac{d_{\mathcal O}}2\log\frac1\varepsilon
 +c_{\mathcal O}+o(1)
 \qquad(\varepsilon\downarrow0).
 }                                                    \tag{5}
\]
The leading constant \(e^{-c_{\mathcal O}}\) is the curvature-weighted Haar
volume determined by the reporter weights and the character lattice.

Thus temporal dimension is operationally recoverable from the high-return
density:
\[
 \boxed{
 d_{\mathcal O}
 =
 2\lim_{\varepsilon\downarrow0}
 \frac{-\log\operatorname{dens}
   \{t:Q_{\mathcal O}(t)<\varepsilon\}}
      {\log(1/\varepsilon)}.
 }                                                    \tag{6}
\]

For Lebesgue-almost every admissible frequency vector, the first continuous
post-exit encounter and the first stroboscopic encounter obey
\[
 \boxed{
 \lim_{\varepsilon\downarrow0}
 \frac{\log\tau^{\mathrm{cont}}_{\mathcal O}(\varepsilon)}
      {\log(1/\varepsilon)}
 =\frac{d_{\mathcal O}-1}{2},
 \qquad
 \lim_{\varepsilon\downarrow0}
 \frac{\log\tau^{\mathrm{disc}}_{\mathcal O}(\varepsilon)}
      {\log(1/\varepsilon)}
 =\frac{d_{\mathcal O}}2.
 }                                                    \tag{7}
\]
The subtraction of one in continuous time is geometric: the orbit itself
uses one temporal direction, so only the transverse codimension controls
successive encounters.

### II. Temporal information is the finite-resolution law

For a finite pure spectral packet, the existing projective reverse-water
functional is the finite-resolution approximation to `(3)`. It controls both
the static target information and the logarithm of the least
spectrum-uniform return deadline within explicit constants.

The active water coordinates are therefore not an analogy to information
theory. They are the resolution-dependent temporal directions that must be
synchronized. The asymptotic rank in `(5)` is the zero-resolution limit of
this effective dimension.

The master paper must either prove a dimension-free comparison between exact
\(\mathcal I_{\mathcal O}\) and reverse-water information or state the sharp
unavoidable remainder. A support-linear error cannot be hidden as a
lower-order term when the information itself is only \(O(d_{\mathcal O})\).

### III. Observer composition and temporal rank balance

Reporter refinement acts by inclusion of visible gap modules and cannot
decrease temporal dimension. For two reporter families, define their join by
union and their common temporal content by
\[
 M_{\mathcal O\wedge\mathcal P}
 =M_{\mathcal O}\cap M_{\mathcal P}.
\]
Whenever the ranks are finite,
\[
 \boxed{
 d_{\mathcal O\vee\mathcal P}
 +d_{\mathcal O\wedge\mathcal P}
 =
 d_{\mathcal O}+d_{\mathcal P}.
 }                                                    \tag{8}
\]

For independent product systems, the temporal module is the sum of the two
factor modules. Their recurrence dimensions add exactly when they share no
nonzero rational frequency direction; shared clocks give precisely the
intersection correction in `(8)`.

This is the observer law: different reporters do not change external
parameter \(t\). They take different quotients of one relative temporal
geometry.

### IV. Interaction creates temporal dimension

Let \(G=(V,E)\) be every finite connected interaction graph,
\(|V|=n\geq2\), with local dimension \(q\geq2\) and \(D=q^n\). In the full
real vector space of one-site and edge-supported Hermitian Hamiltonians,
Lebesgue-almost every Hamiltonian has simple spectrum and maximal projective
gap rank
\[
 \boxed{d_{\mathrm{global}}=D-1=q^n-1.}              \tag{9}
\]
It therefore saturates every finite observer's graph-theoretic temporal
capacity.

By contrast, if
\[
 H=\sum_{a=1}^{m}K_a,\qquad [K_a,K_b]=0,
\]
with every \(K_a\) supported on at most \(k\) sites, then
\[
 \boxed{d_{\mathrm{global}}\leq m(q^k-1).}            \tag{10}
\]
For bounded-range bounded-degree systems this is \(O(n)\).

The maximal-rank set in `(9)` is dense and full measure. Hence every
neighbourhood of every commuting local Hamiltonian contains noncommuting
local Hamiltonians whose temporal dimension is \(q^n-1\). Eigenvalues move
continuously, but recurrence dimension and the asymptotic waiting exponent
jump discontinuously:
\[
 \boxed{
 O(n)\longrightarrow q^n-1.
 }                                                    \tag{11}
\]

This is the new physical mechanism behind doubly exponential generic
many-body recurrence. Hilbert dimension makes many phases available;
interaction makes them arithmetically independent.

The path case of `(9)` is now paper-proved for every \(q\geq2\), and the
same theorem follows for every interaction graph containing a spanning path.
See
`../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md`.
Only connected graphs without a spanning path remain in open core 1.

### V. Dissipation, infinite spectra and the arrow boundary

Every finite power-bounded recurrence record decomposes into a persistent
peripheral record and a transient remainder. The transient remainder tends
to zero; the persistent temporal hull obeys `(3)`--`(8)`. Persistent mass is
the exact late-return ceiling, while temporal codimension fixes the rarity
below that ceiling.

For every normalized stationary positive-definite record with arbitrary
spectral type, the atomic visible-gap measure generates a compact temporal
hull and the continuous remainder vanishes in time density. Its complete
long-time record distribution is the Haar pushforward from the atomic hull.
The total atomic mass is the exact positive-density return threshold.

If the visible gap measure is atomless, every fixed positive-return set has
zero time density. If its atomic temporal module has infinite rational rank,
its return information grows faster than
\(N\log(1/\varepsilon)\) for every fixed \(N\), subject to the target seeing
every chosen independent direction. Thus finite, countably infinite,
singular-continuous and absolutely continuous systems occupy different
limits of the same temporal-codimension law.

Microscopic reversibility alone therefore does not force a macroscopic
repeatable history. A continuous observer spectrum can remove
positive-density recurrence without nonunitarity.

### VI. Global completion is necessary and sufficient

Complete polynomial local dynamics, complete local Krylov geometry and even
complete all-orders perturbative data do not determine
\(K_{\mathcal O}\), \(d_{\mathcal O}\) or
\(\mathcal I_{\mathcal O}\). Opposite recurrence phases can share all those
local data.

The completed visible gap measure is sufficient: its atomic hull determines
all long-time continuous recurrence statistics, and its additive collision
hierarchy gives every long-time fidelity moment.

The local/global no-go theorem is therefore not a separate negative result.
It identifies the exact information boundary of the temporal-codimension
law.

## What the law would explain

### Quantum many-body physics

It answers why integrable or commuting models can recur on exponentially
shorter scales than generic interacting models even when both act on the same
Hilbert space. The difference is not dimension of state space but dimension
of the relative temporal orbit actually generated.

It also answers the explicit two-body question whether locality forces hidden
energy resonances. It does not: even a static nearest-neighbour chain of
\(q\)-level systems generically has the maximal \(q^n-1\) projective clocks.
The combined law then turns that spectral fact into exact density and
first-return exponents. Every interaction graph containing a spanning path
inherits the same generic theorem, including rings and standard finite grids
with such a path.

At arbitrary local dimension, maximal projective rank also proves every
finite-order no-resonance condition simultaneously. Equal sums of the same
number of energy levels are forced to be the same multiset. Higher-moment
dephasing assumptions therefore become generic theorems inside a static
bounded-degree local coupling space, while near-resonance scales remain
nonuniform.

Writing the chain's maximum entropy as
\(S_{\max}=\log(q^n)\), the exact fixed-fidelity recurrence density becomes
\[
 -\log\operatorname{dens}\{\Delta_H<\varepsilon\}
 =
 (e^{S_{\max}}-1)
 \log\!\left(\frac{\pi}{2\arcsin(\varepsilon/2)}\right).
\]
Thus interaction turns an additive many-body system into one whose
high-fidelity returns occupy a doubly exponentially small fraction of time
as a function of maximum entropy. This is an exact finite-chain density
identity, not an assumption of randomness and not a first-hitting-time
identity.

### Black-hole recurrence estimates

A finite-entropy black-hole model with effective Hilbert dimension
\(D\sim e^S\) has a doubly exponential high-fidelity recurrence scale only
if its observer-visible persistent gap module has rank comparable to \(D\).
Entropy alone does not establish that premise. A local maximal-rank theorem
would supply it for genuine finite local models; a gravitational model still
requires a separate bridge identifying its Hamiltonian and reporter class.

The law therefore changes the question from

```text
How many states does the black hole have?
```

to

```text
How many independent relative spectral clocks survive and remain visible?
```

No claim that an actual black hole has finite \(D\), maximal rank or a
particular recurrence time is permitted without proving those physical
premises.

### Problem of time

The unobservable common energy phase is the quantum form of the common
clock-origin quotient. Recurrence depends only on relations among internal
clocks. The law does not create an external time or solve quantum gravity;
it states what temporal structure remains operational after the external
origin is removed.

## Existing results subsumed

- `projective-quantum-recurrence-rate-distortion`: finite-resolution target
  information and minimax deadline inside one finite temporal hull.
- `local-quantum-clock-recurrence`: finite records do not determine the
  completed hull or a later point on it.
- `multiple-elliptic-gamma-rational-rank-dichotomy`: complete polynomial and
  perturbative local data do not select the global hull; gap collisions do.
- `universal-quantum-recurrence-anatomy`: persistent mass, weights, observer
  graph and spectral completion become operations on the same hull.
- `observer-time-recurrence-distribution-law`: arbitrary-spectrum Haar
  distribution and atomic-mass threshold become the infinite-sector form.
- `relational-history-external-time-ambiguity-classification`: quotient by
  common origin explains why only relative phases enter.
- `dissipative-quantum-return-information-transition`: the peripheral hull is
  what survives loss.
- `local-interaction-recurrence-rank-explosion-law`: interaction clause
  `(9)`--`(11)` supplies the proposed nonclassical Nature anchor.

## Exact falsifiers

Retire the frozen conjecture if any of the following occurs.

1. A finite stationary reporter whose return density differs from Haar
   target volume.
2. A finite visible-gap hull whose high-return exponent differs from half
   the rank because the return Hessian is degenerate in a genuinely visible
   direction.
3. Failure of either metric shrinking-target exponent in `(7)` on a
   positive-measure symmetry-free local spectral family.
4. A connected interaction graph for which every local Hamiltonian satisfies
   a nontrivial rational projective spectral relation.
5. An open set of symmetry-free local Hamiltonians with nonmaximal projective
   rank.
6. A commuting \(k\)-local Hamiltonian violating `(10)`.
7. A prior theorem equivalent to the joined codimension, information,
   observer-composition, interaction-rank and all-spectrum transition law.
8. An honest physics audit showing that maximal global recurrence has no
   consequence independent of classical torus equidistribution.
9. A Nature editor can delete `(9)`--`(11)` and reduce the paper to known
   Kronecker--Wiener--Bohr machinery without losing its central conclusion.

Failure of one clause does not license silently weakening it. Record the
counterexample, extract the strongest positive survivor and freeze a new
conjecture.

## Remaining gates

1. Exact-object priority audit for the local generator theorem. Abstract
   generic non-resonance is known in continuum Schrödinger control theory;
   novelty must rest on full \(q^n-1\) rank inside the static
   polynomial-parameter bounded-degree tensor-local family.
2. Independent specialist audit of the qudit endpoint-extension proof and
   the metric-Diophantine transfer.
3. Unconditional formalization of the local qudit-chain generator theorem,
   its all-order no-resonance corollary and exact recurrence-density law.
4. An experimentally definable finite-spin protocol measuring the temporal
   rank slope without waiting for the astronomical global return.
5. Optional strengthening from spanning-path graphs to every connected
   graph. This would widen the generator theorem but is not required for the
   universal observer/spectrum law, since a one-dimensional degree-two path
   is already the minimal locality anchor.
6. Either prove the sharp reverse-water comparison or omit it from the
   master paper. It cannot remain as an independent decorative layer.

## Nature gate

```text
One canonical object rather than collage:                 YES
Recognized major question:                                YES
New mathematical theorem beyond parent machinery:         PAPER-PROVED; AUDIT OPEN
New physical mechanism:                                   PAPER-PROVED; PRIORITY OPEN
Arbitrary finite/infinite stationary scope:               FORMALIZED
Local physical Hamiltonian anchor:                         PAPER-PROVED FOR ALL QUDIT PATHS
Experimental consequence:                                 OPEN
Black-hole relevance without overclaim:                    DELIMITED
Exact-object priority:                                     OPEN
Unconditional formal trace:                                FOUNDATION YES; GENERATOR NO
Hostile specialist review:                                 OPEN
Hostile Nature editorial review:                           OPEN
```

## Log

- 2026-07-29: Corpus audit found unconditional arbitrary-spectrum
  observer-temporal universality and complete recurrence-distribution modules.
  This closes the master law's kinematic foundation and narrows all novelty
  scoring to the local interaction generator and its physical consequences.
  Formalization remains internal and will not be mentioned in the manuscript.

- 2026-07-29: Closed the paper-level first-return gap for generic static
  nearest-neighbour qubit chains. Analytic branch independence makes the local
  spectral map a nondegenerate Diophantine manifold outside an algebraic null
  set. Kleinbock--Margulis extremality plus an elementary first-hit lemma gives
  exact phase-radius exponents \(2^n-1\) for stroboscopic return and
  \(2^n-2\) for continuous return; quadratic reporter deficits divide both
  exponents by two. See
  `../2-fully-proven/local-chain-metric-recurrence-exponents.md`.
- 2026-07-29: Primary-source audit currently finds no theorem colliding with
  generic maximal projective rank in a static nearest-neighbour chain.
  Existing sources assume pair-gap nondegeneracy, study finite-order
  no-resonance statistically, engineer only \(O(n)\) free frequencies, or use
  unrestricted random Hamiltonians. Priority remains open pending spectral
  Galois and sparse-matrix literature.
- 2026-07-29: Upgraded bounded-degree maximality from qubits to every finite
  local dimension \(q\geq2\). The endpoint-extension equality graph is the
  categorical product of the old non-bipartite transition graph with
  \(K_q\), hence connected. A separate endpoint-observability induction
  supplies the required open witness set. Every qudit interaction graph
  containing a spanning path inherits rank \(q^n-1\).

- 2026-07-29 — user rejected a universal-law title assembled from sharpened
  known results and requested one reinterpretation subsuming prior work.
- 2026-07-29 — froze the temporal-codimension interaction law before using
  the available Kronecker, Haar, graph-rank, water-filling and local spectral
  proof routes.
- 2026-07-29 — hostile review rejected an instantaneous physical reading of
  exact rational-rank discontinuity. The finite-horizon operational repair is
  paper-proved in
  `../2-fully-proven/finite-horizon-observer-temporal-profile-stability.md`:
  reporter-orbit covering profiles are perturbation stable, converge in the
  ordered long-time/high-resolution limit to visible gap rank, and cannot
  change at resolution \(\varepsilon\) before time
  \(\varepsilon/(4\|H-K\|\mathcal B_{\mathcal O})\).
- 2026-07-29 — bounded-degree local maximality is paper-proved for every open
  nearest-neighbour qubit chain in
  `../3-formalized/nearest-neighbor-chain-projective-spectral-maximality.md`.
  Almost every static chain has projective rank \(2^n-1\); commuting local
  chains have rank \(O(n)\). Arbitrary connected graphs and local
  \(q>2\) remain open.
