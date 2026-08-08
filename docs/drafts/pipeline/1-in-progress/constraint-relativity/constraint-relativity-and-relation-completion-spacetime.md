# Constraint relativity and relation--completion spacetime

- **ID:** `constraint-relativity-relation-completion-spacetime`
- **Stage:** 1-in-progress
- **Type:** NEW MATHEMATICAL FIELD / FOUNDATIONAL RESEARCH PROGRAM
- **Short name:** `CR`
- **Scientific status:** `[BOLD CONJECTURAL FIELD] [PARTIAL MODEL THEOREMS EXIST]`
  `[EXTERNAL PRIORITY OPEN] [NOT RH] [NO LEAN AUTHORIZED]`
- **Statement:** Relations do not merely cut subsets from a fixed background. An observer's
  relation system generates the topology, dimension, causal order, completion, and complexity
  geometry in which its realizations exist; noncommutation of relation transport with completion
  is curvature.

## Goal

Create the analogue of general relativity for heterogeneous mathematical constraints.

```text
fixed-background mechanics:
  choose arithmetic/spectral/geometric ambient space -> impose equations

constraint relativity:
  source relations + observer language + allowed transformations
  -> completed realization geometry -> time, dimension, metric, horizons, curvature
```

The primitive object is not a zeta function, zero set, Hilbert space, divisor, phase torus, or
spacetime manifold. It is a covariant system of relations and their completed realization spaces
as the language of observation changes.

> **Constraint equivalence principle.** No arithmetic, spectral, geometric, or operational frame
> is preferred. Finite observers may flatten their own relations. Intrinsic content is what
> survives transport around the observer-language atlas and through cofinal completion.

## 0. Why prior grand geometries are still one level too low

Existing corpus programs already supply local charts:

- Interfinity geometry: stable-exactness cuts, terminal cohomology, synchronized nerves, phases;
- noncommuting exactification geometry: observer/completion curvature;
- polarized exchange horizons: arithmetic--spectral--geometric comparison;
- completed-time relativity: time from completed distinguishable histories;
- quantum recurrence: relation lattice and its completed future annihilator.

But Interfinity Theorem XIX proves a fatal universality statement: a free source can manufacture
arbitrary finite residue, Gram, and phase data. Geometry is not predictive until source relations
constrain it.

Each predecessor holds the relation system fixed and studies what it produces. `CR` makes the
relation system a field variable:

```text
Newtonian constraint mechanics: geometry fixed; relations live inside it.
Constraint relativity: relations source geometry; geometry controls admissible relations.
```

## 1. Observer-language relation atlas

Let `Lambda` be a category of observer languages and resource scales. Languages may consist of
polynomial words, differential words, prime-depth characters, Fourier reporters, Hodge tests,
finite-time experiments, or bounded-depth circuits.

For source `x` and `lambda in Lambda`, a **relation chart** contains:

1. a potential-law object `P_lambda(x)` of admissible formal questions;
2. a relation subobject

   \[
   R_\lambda(x)\hookrightarrow P_\lambda(x),
   \tag{CR.1}
   \]

   consisting of questions that vanish, become identities, or are operationally
   indistinguishable on `x`;
3. the exposed freedom object

   \[
   F_\lambda(x)=P_\lambda(x)/R_\lambda(x);
   \tag{CR.2}
   \]

4. a completion or realization spectrum

   \[
   X_\lambda(x)=\operatorname{Real}_\lambda(F_\lambda(x));
   \tag{CR.3}
   \]

5. elementary costs on transformations of `X_lambda(x)`.

Linear charts use subspaces or modules; algebraic charts use ideals and spectra; quantum charts
use operator relations and state spaces; differential charts use differential ideals and
differential-Galois realizations. No common carrier is assumed.

A language change `u:lambda->mu` is **constraint-flat at x** when

\[
 u_*R_\lambda(x)=R_\mu(x)\cap u_*P_\lambda(x)
 \tag{CR.4}
\]

and completion commutes with transport. Otherwise relation mismatch is curvature data.

## 2. Relation--completion spacetime

The **constraint spacetime** of `x` is the total atlas

\[
 \mathfrak X(x)=\int_{\lambda\in\Lambda}X_\lambda(x),
 \tag{CR.5}
\]

with relation transport, completion comparison, and costs. `(CR.5)` names the research object; an
ordinary Grothendieck construction is not assumed sufficient.

### Relation topology

At fixed language, finite-resolution neighborhoods agree on finitely many declared relations up
to declared tolerances. Cofinal completion adds stable relation profiles. Across languages,
neighborhoods preserve source provenance and transport compatibility.

Topology is **endogenous**: changing relation profile changes which Cauchy filters, boundary
points, and dimensions exist. A state can change the geometry of its own realization space.

### Causal order and time

For profiles on a common potential-law object, declare

\[
 R_y\preceq R_x\quad\Longleftrightarrow\quad R_y\subseteq R_x.
 \tag{CR.6}
\]

Moving toward fewer accessible relations exposes more freedom, but inclusion alone is not time:
an observer can forget tests arbitrarily. A **provenant event** is a source operation together with
a language comparison which induces `(CR.6)`, transports declared nonzero witnesses, and remains
nontrivial after common observer refinement. Pure observer restriction is vertical gauge.

Causal order is generated only by provenant events. A directed chain of non-gauge events is a
candidate future direction; its order/completion is intrinsic time. Incomparable provenant
relation changes are candidate spatial directions. Physical spacetime reconstruction remains an
open realization problem.

### Complexity metric

Choose elementary allowed changes of relation profile or realization. Path cost is the action of
elementary costs; distance is minimal path cost. Complexity is metric length on constraint
spacetime, not an unrelated scalar.

### Completion horizons

A **horizon** occurs when a family is indistinguishable at every bounded resource while its
completed relation profile or realization changes discontinuously:

\[
 \operatorname{Comp}\lim_{a\to a_0}\ne
 \lim_{a\to a_0}\operatorname{Comp}.
 \tag{CR.7}
\]

This includes weak-coupling/infinite-time recurrence boundaries, finite-jet/HT tails, singular
source completion, and observer exactness cuts.

### Mathematical wormholes

Given boundary charts `X_A,X_B`, a **relation bridge** is a joint completion `W` with surjections

\[
 W\longrightarrow X_A,
 \qquad W\longrightarrow X_B,
 \tag{CR.8}
\]

whose relation profile does not split as a product. Hidden cross-fibre is kernel of boundary
comparison. “Wormhole” is justified only if this fibre has an intrinsic complexity/time metric
and changes boundary return laws. No astrophysical identification is assumed.

## 3. Relation curvature

For invertible transport `h:P->P` and relation object `R subset P`, put `I_h=R\cap hR` and define
the ordered loss/gain pair

\[
 \mathcal K_R(h)=
 \left(
   \mathcal K_R^-(h),\mathcal K_R^+(h)
 \right)
 =\left(
   \frac{R}{I_h},\frac{hR}{I_h}
 \right).
 \tag{CR.9}
\]

It is retained as the directed cospan

\[
 R\longleftarrow I_h\longrightarrow hR,
 \tag{CR.10}
\]

with the direction `R -> hR`. Reversing the loop swaps loss and gain. A scalar rank or positive
energy sees only their common size or sum and forgets direction. The tempting `K_0` difference of
the two quotients is identically zero for invertible `h`, so it is explicitly rejected as a
curvature invariant.

For a heterogeneous loop, compose declared correspondences back to the starting potential-law
object, then apply `(CR.9)`--`(CR.10)`. For partial maps, use an ordered comparison relation or
cone.

This differs from curvature on one carrier: it measures which equations cease to be equations
after a complete trip through arithmetic, spectral, geometric, or operational languages.

**Selection curvature** is finer. Pairwise transported profiles may be compatible while no common
source-provenant profile realizes the loop. Its first model is a horn in the relation atlas, not
another pairwise commutator.

## 4. Constraint--freedom conservation

In additive finite charts,

\[
 [P_\lambda]=[R_\lambda]+[F_\lambda]
 \tag{CR.11}
\]

and every additive dimension theory gives

\[
 \operatorname{capacity}
 =\operatorname{relation\ rank}+\operatorname{freedom\ dimension}.
 \tag{CR.12}
\]

Rank--nullity is not novelty. Research claim: `(CR.12)` is the local flat law of a larger
geometry. Under language change,

\[
 \Delta\operatorname{freedom}
 =-\Delta\operatorname{relation}+\operatorname{transport\ anomaly}.
 \tag{CR.13}
\]

Main index problem: define `(CR.13)` across heterogeneous charts so its anomaly is a directed
index of `(CR.10)`, rather than its vanishing ordinary `K_0` difference, and is invariant under
source-preserving Morita equivalence.

## 5. Four governing principles

1. **Finite flattening.** A tail obstruction is intrinsic only if it survives every compatible
   finite-resource flattening.
2. **No cofinal curvature without singular transport.** Exact edge limits plus equicontinuous
   transports force cyclic holonomy to vanish. Nonzero tail curvature requires unboundedness,
   nonattainment, nonclosed range, or relation-valued transport.
3. **Orientation precedes metric.** Relation creation/loss is signed; positive energy is a
   quadratic shadow which can erase its side and provenance.
4. **Source--geometry reciprocity.** Relations determine completion geometry; only relations
   continuous and provenant in that geometry count as laws.

## 6. Quantum recurrence, Brown--Susskind, and horizons

Quantum recurrence supplies the first exact flat model. For finite projective carrier `P`,

\[
 0\longrightarrow L\longrightarrow P\longrightarrow T\longrightarrow0,
 \qquad \dim T+\operatorname{rank}L=\operatorname{rank}P.
 \tag{CR.14}
\]

For countable pure-point dynamics, annihilator of the balanced relation lattice is the compact
completed future. Weak interaction can delete exact relations while remaining invisible on every
fixed bounded horizon. Thus relation loss changes completed time and realizes `(CR.7)`.

Brown--Susskind suggests the metric layer:

```text
relation lattice                 topology/dimension of completed phase future
local gate set / Hamiltonian     elementary directions and complexity metric
unitary orbit                    path through completed future
complexity growth                distance growth from low-complexity relation locus
plateau                          maximal-distance / minimal-short-relation region
recurrence                       rare return near low-complexity locus
uncomplexity                     remaining directed path capacity
```

This becomes physics only if a gravitational model realizes the same invariant as wormhole volume
or Wheeler--DeWitt action.

For factor dimensions `D_A,D_B`, joint capacity decomposes as

\[
 D_AD_B-1=(D_A-1)+(D_B-1)+(D_A-1)(D_B-1).
 \tag{CR.15}
\]

Last term is invisible to separate boundary clocks. It is the candidate interaction cross-fibre
in `(CR.8)`. Corpus proves weak generic interaction can expose this sector. Wormhole
interpretation requires showing it also controls interior complexity.

## 7. Hypertranscendental realization

Let `P_r(f)` be differential words of order at most `r`, and `R_r(f)` their relation ideal.
Finite-jet results show differential-algebraic and hypertranscendental germs are mutually dense in
finite-jet topology. HT geometry therefore belongs to the inverse system

\[
 \{R_r(f)\subset P_r(f)\}_{r\ge0},
 \tag{CR.16}
\]

not one finite chart. Hypertranscendence is failure of relation charts to stabilize under
prolongation. Differential Galois groups, wild kernels, Stokes data, and arithmetic source
relations are realization frames of this tail.

## 8. RH realization without circularity

Current RH atlas has many faithful carriers; one source-isogeny class of horizontal defect;
substantial provenance, completion, and positive geometry; obstruction rank one; proved
source-vanishing rank zero.

In `CR`, many frames expose one freedom class but no independent arithmetic relation kills it.
Adding an equivalent detector cannot change `(CR.12)`.

Missing RH theorem must be a **relation-creation law** on pre-divisor source. It must:

1. exist before zero specialization;
2. increase transversal source-relation rank by one;
3. preserve ordinary-prime provenance and multiplicity;
4. transport through a singular chart;
5. kill horizontal freedom rather than measure its norm.

This is a prediction, not proof. Any proposal changing carrier, positivity, target dimension, or
Kummer depth without changing transversal relation rank is route theatre.

## 9. What corpus shadows become

| Corpus pattern | Constraint-relativistic shadow |
|---|---|
| many routes, one radical | repeated coordinates on one freedom direction |
| source isogenies | gauge equivalence of relation charts |
| finite jets miss HT | local flattening of tail curvature |
| positive forms lose orientation | metric square of signed relation change |
| compact synthesis loses source mass | bounded chart fails at horizon |
| singular readers survive | horizon crossing requires relation-valued transport |
| depth adds roots, no new radical | refinement without transversal rank change |
| weak interaction changes infinite future | relation loss changes completion before bounded history |
| temporal dimension multiplies | joint completion has cross-fibre `(CR.15)` |
| long complexity plateau and recurrence | compact freedom revisits low-cost locus |
| source producer missing | curvature exists but source field equation does not |

## 10. Fields-Medal questions

1. Which relation atlases admit a universal completion spacetime? What replaces `Spec`,
   Pontryagin duality, and Tannaka duality across heterogeneous languages?
2. What covariance identifies presentation changes but rejects fitted gauges?
3. Is there a cohomology whose `H1` records stable relation loss, `H2` selection curvature, and
   index gives `(CR.13)`?
4. Can finite-capacity constraint spacetimes be uniformized into flat charts and singular horizons?
5. Does nonzero cofinal holonomy force unbounded transport or infinite observer distance?
6. When do arithmetic relations determine spectral completion and geometric metric uniquely?
7. Can relation-spectrum invariants determine complexity growth, plateau measure, and recurrence?
8. Is interaction cross-fibre `(CR.15)` the universal local model for new completed time?
9. Is differential transcendence degree an entropy/dimension of pro-relation spacetime?
10. What arithmetic law creates relations instead of detecting their absence?
11. Can boundary relation data determine bulk completion and Brown--Susskind geometry?
12. What new non-zeta theorem does `CR` predict without being fitted to its proof?

## 11. Bold conjectures

- **CR-I — heterogeneous rank--curvature index.** A source-Morita-invariant directed index extends
  `(CR.12)` and detects the ordered defect `(CR.10)` despite its zero ordinary `K_0` class.
- **CR-II — singular holonomy theorem.** Exact finite edges plus equicontinuity force cofinal
  selection curvature zero.
- **CR-III — relation/complexity second law.** Low-cost observer relations disappear in measure
  under generic local quantum evolution; circuit complexity is geodesic distance generated by
  that filtration; recurrence is controlled by metric entropy of completed freedom.
- **CR-IV — holographic constraint duality.** Complete boundary relation data determine bulk
  completion up to constraint covariance; non-product relation bridges are wormhole objects.
- **CR-V — HT tail curvature.** Hypertranscendence equals absence of finite flat terminal chart;
  generator growth equals intrinsic dimension growth of `(CR.16)`.
- **CR-VI — arithmetic source equation.** Euler--Gamma incidence defines a pre-divisor relation
  current whose spectral shadow is horizontal Green defect and geometric shadow is signed
  premetric orientation. This is not assumed to vanish.

## 12. Conjecture loop ledger

1. **New carrier geometry — failed.** Free-source universality realizes arbitrary phase geometry.
   Survivor: source relations are predictive content.
2. **Pairwise noncommutation — failed.** Existing faces coexist and anomalies are source-isogenous.
   Survivor: transversal relation rank and full-cycle selection curvature.
3. **Derived torsion selects wall — failed.** Nonzero derived fibre is already wall membership.
   Survivor: horizon kinematics; dynamics must act before quotient.
4. **Relation loss creates freedom — succeeds in quantum flat model.** `(CR.14)` and `(CR.15)` are
   exact. Generalization open.
5. **Relations gravitate — live.** Relation profile and completion mutually determine topology,
   time, complexity, and horizons.

## 13. Fatal tests

Retire `CR` as a claimed new field if:

1. `(CR.5)` is a standard institution/stack with no new invariant or theorem;
2. relation curvature predicts nothing beyond ordinary diagram noncommutativity;
3. all theorems reduce to rank--nullity, Stone/Pontryagin duality, or Nielsen geometry;
4. no nonlinear dimension theory supports `(CR.13)`;
5. causal order cannot distinguish evolution from observer forgetting;
6. black-hole language supplies no theorem-level dictionary;
7. RH realization only renames “find a source identity”;
8. no non-zeta prediction is proved;
9. relation systems remain external rather than covariant fields;
10. theory cannot separate independent relation loss from isogenous detectors.

## Gates

- [x] 0 -> 1: ontology, corpus evidence, exact model, fatal tests
- [ ] prove singular triangular-holonomy theorem
- [ ] prove one nonlinear relation--completion index theorem
- [ ] prove a non-zeta prediction not used to define theory
- [ ] define source-covariant relation dynamics
- [ ] audit institutions, categorical logic, dualities, information/complexity geometry,
  contextuality, and holography
- [ ] connect Brown--Susskind only through gravitational realization
- [ ] no RH inference before independent pre-divisor relation current

## Log

- 2026-08-08 — created after route-local DSG rejection. Central jump: relations source completion
  geometry; earlier exactness/observer/phase geometries become local charts. Added recurrence and
  Brown--Susskind as a second realization, not metaphor.
