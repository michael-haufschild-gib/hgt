# Locality does not shorten quantum recurrence

- **ID:** `locality-does-not-shorten-quantum-recurrence`
- **Stage:** 1-in-progress
- **Type:** MASTER PAPER REWRITE / LOCAL MANY-BODY RECURRENCE / THEOREM SYNTHESIS
- **Date:** 2026-08-23
- **Replaces as publication spine:**
  `../4-publication-ready/universal-quantum-recurrence-anatomy/`
- **Statement:** The projective spectral-relation lattice is the single invariant governing
  first-return exponents and all-order return collisions; almost every static onsite-plus-nearest-
  neighbour qudit path has trivial projective relation lattice and therefore attains the maximal
  recurrence codimension allowed by its Hilbert space.

## Goal

Answer one current many-body recurrence question rather than catalogue recurrence phenomena:

> Does one-dimensional bounded-degree locality force hidden spectral relations that shorten
> recurrence?

Proposed answer: no. For an open path of `n >= 2` `q`-level sites, almost every Hamiltonian in the
exact real coefficient space of arbitrary onsite and nearest-neighbour two-site Hermitian terms
has `D = q^n` simple levels and maximal projective spectral rank `D - 1`. The same relation-free
condition gives the sharp metric first-return exponents and the fixed-weight floor of every
long-time survival-return moment.

This is a rewrite, not an additive expansion. Loss, general open-system recovery, finite-record
forecasting, l-bit infinite-volume dynamics, and circuit complexity do not share this theorem's
load-bearing invariant and must remain separate papers.

## One invariant and one causal chain

For a finite labelled spectrum `E = (E_j)`, use the balanced projective relation lattice

\[
 L_E^{\rm proj}
 =\{k\in\mathbb Z^D:\sum_j k_j=0,\ \sum_jk_jE_j=0\}.
\]

The paper is organized by the single chain

```text
projective relation lattice
        |
        +-- annihilator phase hull -> temporal rank -> return density
        |                                      -> first-return exponent
        +-- relation height filtration -> replica collisions -> all return moments
        +-- local interaction -> deletion of relations -> simultaneous extremality
```

No section survives unless it is an explicit arrow in this diagram.

## Proposed theorem package

### Law I — constraint/dimension conservation

For every `D`-level spectrum, anchored-gap rank plus balanced-relation rank is `D - 1`.
The completed phase ensemble is equivalent to the relation lattice, and replica order `m` detects
exactly those relations whose positive coefficient mass is at most `m`.

This is universal infrastructure. Classical Kronecker--Weyl and Pontryagin-duality ingredients
receive no novelty credit.

### Law II — transverse first-return law

For almost every frequency packet in every admissible analytic simple-spectrum chart, phase-radius
first hits have exponent equal to phase-hull dimension in stroboscopic time and one less in
continuous time. For a quadratic fidelity/operator-return deficit, the exponents are divided by
two.

For a generic local qudit path this becomes

\[
 \alpha_{\rm disc}=q^n-1,
 \qquad
 \alpha_{\rm cont}=q^n-2
\]

for phase radius, and `(q^n-1)/2`, `(q^n-2)/2` for quadratic deficit.

The subtraction of one is the paper's geometric explanation: continuous flow consumes one hull
direction; recurrence is controlled by transverse codimension.

### Law III — all-order collision extremality

Every long-time `m`th survival-fidelity moment equals the probability that two `m`-replica energy
sums coincide. At fixed positive spectral weights, unavoidable permutation matchings give a
universal floor. Equality at every order is equivalent to `L_E^{proj} = {0}`.

Thus the same condition that maximizes first-return codimension minimizes every long-time return
moment. First hitting and completed return statistics are two consequences of one arithmetic
invariant, not separate laws.

### Law IV — static local saturation

For almost every Hamiltonian in the exact onsite-plus-nearest-neighbour Hermitian coefficient
space of an open `n`-site `q`-level path:

1. spectrum is simple;
2. `L_E^{proj} = {0}` and projective rank is `q^n - 1`;
3. sharp local-chain first-return exponents of Law II hold;
4. every positive-weight survival-return moment attains Law III's floor at every replica order;
5. completed strict global-return density has the exact finite-size product law and vanishes
   doubly exponentially in `n` at fixed tolerance after taking the long-time completion first.

This is the novelty anchor. It upgrades ambient/random-Hamiltonian recurrence results to one
static, one-dimensional, degree-two, finite-range many-body family.

## Thermodynamic statement permitted

Include only the proved ordered limit:

```text
finite n -> completed long-time return density -> n to infinity
```

At fixed strict projective tolerance, density tends to zero; its negative logarithm divided by
`q^n - 1` has an exact limit, and its site-normalized double logarithm tends to `log q`.

Do not call this an infinite-volume global recurrence theorem. Standard infinite-volume l-bit
dynamics is a different theorem and would turn the paper into a collage.

## Strong optional corollary — weak interaction activation

The publishable strengthening is:

> For almost every onsite background `A` and pure nearest-neighbour interaction profile `V`, all
> coupling strengths outside a countable exceptional set containing zero have maximal projective
> rank, while `rho(A) <= n(q-1)`; fixed-horizon histories remain `O(T |g| ||V||)` close.

This gives a sharp noncommuting weak-coupling/long-time limit and makes the paper substantially
more arresting. Current corpus contains every abstract component, but not one unconditional local-
path capstone discharging the canonical onsite/interaction coordinate split. Until that capstone
exists, the manuscript may state only the unconditional almost-every-affine-line theorem in the
full local space, which does not establish the onsite-to-interacting rank jump.

## Required formal capstone before manuscript rewrite

Construct one theorem on one canonical uniform qudit path coefficient space that simultaneously
returns:

1. path architecture and Hilbert dimension `q^n`;
2. canonical onsite/pure-edge coordinate split;
3. full-measure maximal-projective locus;
4. full-measure discrete and winding first-return exponents on each simple-spectrum chart;
5. all-order collision floor for every positive weight vector;
6. exact projective return-density/thermodynamic consequences;
7. for almost every `(A,V)` in the canonical split, a countable exceptional coupling set containing
   zero and maximal projective rank for every nonexceptional `g`;
8. finite-horizon reporter Hausdorff bound for the same `A,V,g`.

This is largely a same-object composition theorem. It is still load-bearing: existing declarations
prove these claims in separately packaged path systems or in abstract affine families, so the
public paper must not silently identify their witnesses.

## Current proof inventory

| Claim | Current declaration/module | Status for paper |
|---|---|---|
| constraint/rank conservation | `projectiveTemporalRank_add_relationRank`; `relationPhaseEnsemble_temporalDimension_add_relationRank` | closed |
| completed ensemble iff relation lattice | `spectralRelationLattice_eq_iff_phaseEnsemble_eq` | closed |
| exact replica-height filtration | `resolvedReplicaDetects_iff_relation_and_height_le`; `relationLattice_eq_iff_all_resolvedReplicaDetectors_eq` | closed |
| generic local path maximality | `exists_uniformQuditPathLocalHamiltonianMaximalSet_dense_residual_fullMeasure` | closed |
| local discrete exponent `q^n-1` | `exists_quditPathChain_discreteRecurrenceExponent` | closed |
| local physical survival-fidelity first-return exponent `(q^n-2)/2` for every cyclic state | `universalQuditPathPhysicalRecurrenceCollisionLaw` | closed, same Hamiltonian as rank/collision laws |
| local continuous/winding exponent `q^n-2` | `exists_quditPathChain_windingRecurrenceExponent` plus `WindingReturnEquivalence` | closed |
| universal collision floor/equality | `fidelityReplicaCollisionMass_floor_le`; `all_fidelityReplicaCollisionMass_eq_floor_iff` | closed |
| generic local all-order floor | `exists_quditPath_generic_collisionFloor`; `exists_quditPath_generic_survivalFidelityFloor` | closed |
| thermodynamic completed-density law | `ThermodynamicProjectiveRecurrenceExtinctionLaw` capstones | closed, ordered limit only |
| arbitrary local-space affine-line activation | `exists_uniformQuditPath_countable_exceptional_coupling` | closed but insufficient for onsite jump |
| abstract onsite-background activation | `countable_exceptional_blockLine_onsite` | conditional physical premises remain to be discharged in one path capstone |
| finite-horizon stability | `hausdorffDist_coupledReporterOrbit_le` | closed |

All listed closed declarations have prior targeted verification and axiom audits reporting only
`propext`, `Classical.choice`, and `Quot.sound`. Publication audit must recheck only the final
capstone dependency closure; no full umbrella rebuild.

## External frontier and novelty boundary

Closest checked results:

1. Kotowski--Oszmaniec (2026): deterministic packing upper bounds and generic saturation for random
   Hamiltonians, not static bounded-degree local coefficient spaces.
2. Gupta--Short (2026): simultaneous all-state recurrence bounds from Diophantine approximation,
   not generic exact local exponents.
3. Huang (2021): almost-everywhere nondegenerate gaps for geometrically local Hamiltonians, a
   finite/order-two condition weaker than maximal projective rank.
4. Riddell--Bertini (2024): rationally independent single-particle free-fermion examples with local
   hopping; many-body additive relations remain.
5. Campos Venuti--Odavic--Hamma (2026): exact independent-spectrum SFF moments and limiting laws
   under rational-independence premises; abstract moment formula is prior art.
6. Riddell--Pagliaroli--Alhambra (2023): concentration and recurrence lower bounds under generic
   spectral assumptions; local models are numerical examples, not premise discharge.

Novelty claim permitted after exact priority audit:

> Maximal projective rank and sharp first-return/collision extremality hold almost everywhere in
> the full static one-dimensional nearest-neighbour qudit Hamiltonian family.

Do not claim novelty for torus equidistribution, replica convolution identities, independent-phase
random walks, exponential SFF limits, or Hilbert-space-size recurrence estimates.

## Manuscript architecture

1. Question: does locality force shorter recurrence?
2. One invariant: projective relation lattice and phase hull.
3. Universal transverse-return and replica-collision consequences.
4. Main theorem: generic static nearest-neighbour qudit paths saturate both.
5. Weak-coupling singularity, only after physical onsite/interaction capstone.
6. Ordered thermodynamic consequence.
7. Scope and comparison with random, free, and generic-gap literature.
8. Proofs and appendices.

Suggested title:

> **Locality does not shorten quantum recurrence**  
> *Sharp first-return exponents and all-order collision extremality in static one-dimensional
> many-body systems*

More conservative title if priority audit weakens “does not shorten”:

> **Maximal quantum recurrence codimension in static local many-body systems**

## Explicit exclusions

- Markovian loss and recovery;
- black holes or gravitational extrapolation;
- finite-record forecasting/no-go results;
- observer-graph catalogues beyond one short visible-rank corollary;
- l-bit infinite-volume dynamics;
- circuit complexity ramps, plateaux, or returns;
- Anderson localization;
- general countable-spectrum metric entropy except a brief outlook.

Each is valid research but requires an additional mechanism. Including them would recreate the
rejected “anatomy” collage.

## Gates

- [x] 0 → 1: central question, single invariant, corpus closure and primary frontier mapped
- [x] same-object path capstone: rank, sharp clocks, physical first return, collisions and exact-return rigidity
- [ ] 1 → 2: physical onsite/interaction weak-coupling instantiation
- [x] targeted physical-first-return capstone build and axiom audit
- [ ] 3 → 4: standalone rewrite, claim trace, reference audit and hostile specialist review

## Approach

1. Prove same-object local capstone without new mathematics.
2. Prove or reject canonical onsite/pure-edge activation capstone.
3. Re-run exact-object literature search for local maximal projective rank and local shrinking-target
   exponents.
4. Rewrite `universal-quantum-recurrence-anatomy` around Laws I--IV; remove excluded sections.
5. Audit every displayed mathematical claim against the final capstone dependency graph.

## Log

- 2026-08-23 — wide corpus search and 2026 literature comparison select local recurrence
  codimension as stronger paper spine; old four-law anatomy rejected as omnibus organization.
- 2026-08-23 — identified exact formal gap: abstract onsite one-knob theorem lacks one unconditional
  canonical local-path instantiation, and separate local recurrence results lack one public
  same-object capstone.
- 2026-08-28 — closed same-object local capstone and upgraded winding surrogate to actual orbit
  survival-fidelity first return for every cyclic state.  Exact exponent is `(q^n-2)/2` in fidelity
  deficit.  Targeted module build passed; axiom audit reports only standard quotient/classical
  principles.  Remaining gap on this card is weak-coupling onsite/pure-edge activation, not local
  first return.
