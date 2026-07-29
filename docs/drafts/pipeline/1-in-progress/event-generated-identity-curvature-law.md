# Reality is the curvature of event-generated identity

- **ID:** `event-generated-identity-curvature-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** corpus-wide obstruction synthesis
- **Status:** `[FROZEN HUNCH] [PROOF ROUTE UNKNOWN] [NATURE GATE CLOSED]`
- **Statement:** Every objective event creates the physical identity by which its consequences can
  be recognized. Its hidden automorphisms are matter and gauge symmetry, its positive public
  quotient is spacetime, and curvature of comparisons between event-created identities is the
  common origin of gravity and the quantum forces.

## Public claim

> **The universe is not made of matter inside spacetime. Matter and spacetime are the hidden and
> public halves of one quantum fact.**

Shorter headline:

> **Every quantum fact creates its own spacetime.**

Force headline:

> **Every force is the universe failing to agree that two quantum events are the same.**

Gravity headline:

> **Gravity is clocks disagreeing about which moment comes first.**

Mass headline:

> **Mass is the part of a quantum event that spacetime cannot see.**

These are different public faces of one conjecture, not independent proposed mechanisms.

## Frozen conjecture

`[CONJECTURE; DO NOT WEAKEN FOR CURRENT PROVABILITY]`

> **EVENT-GENERATED IDENTITY CURVATURE LAW.** Physical identity is not primitive. An objective
> event creates the minimal positive partial equivalence relation under which its consequences
> become jointly recognizable and composable. The event's hidden equivalences form its internal
> gauge fiber. Quotienting by those hidden equivalences produces its public positive causal
> record. Successive events need not create the same equivalence relation; their canonical
> comparison has one curvature. Its vertical representations are the strong, weak, and
> hypercharge forces. Its public comparison is gravitational curvature. Matter is a distinction
> stable under repeated creation of identity; spacetime is the moduli space of the public
> identities that survive; time is the source order in which new identities become available.
> No manifold, background clock, particle carrier, tensor-factor identity, global dagger, or
> separate force bundle is supplied before events.

For all possible physical worlds, the law is intended to be universal:

> **A world is a regular irreducible source-positive actuality completion. Its spacetime is the
> positive quotient of its event amplitudes, its matter is the stable hidden factorization data,
> and all its forces are representations of the completion's one comparison curvature.**

Different regular completions may yield different spacetime dimensions, signatures, or force
spectra. They are different worlds governed by the same law, not separate laws of gravity.

## What may have been missed

General relativity removed a fixed metric but retained a differentiable carrier and the physical
problem of identifying events across models. Quantum theory made states operational but retained
fixed Hilbert spaces, adjoints, subsystem factorizations, outcome types, and a background rule for
recognizing a state at two times. Gauge theory made internal frames conventional but retained a
supplied bundle saying which fibers are fibers of one object. Category theory usually begins with
identity morphisms and fixed composable types.

The shared unexamined input may be:

> **Every existing framework decides what counts as the same before describing what happens.**

The conjectured reversal is:

> **What happens decides what can count as the same.**

This is stronger than relational coordinates, observer dependence, decoherence, reference-frame
change, gauge redundancy, idempotent splitting, or the claim that geometry is emergent. It says an
event changes the physically available equivalence relation itself, and only the event-created
relation determines its possible successors.

## Why the obstruction corpus points here

The corpus contains many negative results that become one shadow under this interpretation:

1. **Fixed carriers and totalizations become empty.** Grothendieck, stable, and fixed-Hilbert-space
   totalizations preserve a container while pre-supplying cross-event identity. They retain
   bookkeeping but lose the proposed physics.
2. **Flat endpoint stories erase time.** When one global comparison identifies all endpoints,
   transport defects horizontalize and the event history becomes representationally flat.
3. **One-way actuality channels square to zero.** A one-variance transfer cannot create the
   reciprocal recognizer needed for successor composition.
4. **The exact `4/6/4` interface changes support.** Six directions remain directly recognizable;
   four lost possibility directions return with a changed action. This is not one invertible
   change of coordinates.
5. **Matter and observable Standard Model embeddings are nonconjugate.** No invertible
   intertwiner makes their weak actions the same. The event changes recognition, not merely basis.
6. **Unitary completion conserves recognition defect but does not select it.** Once a global
   unitary and source involution are supplied, lost and created defect balance exactly. The
   missing law must create the comparison rather than assume it.
7. **Recognition defects obey a Leibniz composition law.** The formal identity
   \[
   \Delta_{A,C}(ST)=\Delta_{B,C}(S)T+S\Delta_{A,B}(T)
   \]
   is the algebraic shadow expected of a connection whose endpoints carry different identities.
8. **Forgotten source orientation reappears at boundaries.** Quotienting does not destroy a
   distinction; it changes where the distinction can be recognized.
9. **Hypertranscendental histories resist finite closure.** No finite differential-algebraic
   present can encode the completely calibrated history. This is the analytic shadow of
   nonexistence of a finite history-independent global identity.

None of these statements alone establishes the law. Their common explanatory compression is the
reason for the conjecture.

## Exact finite model for our world

The compatible exceptional pair supplies
\[
W\cong M_{3,2}(\mathbb C)
\cong \mathbb C^3\otimes\mathbb C^2
\]
and the exact Standard Model inner automorphism group
\[
S(U(3)\times U(2))
\cong (SU(3)\times SU(2)\times U(1))/\mathbb Z_6.
\]
An elementary event amplitude is conjecturally
\[
X\in W.
\]
Its public record after erasing the hidden left frame is
\[
q(X)=X^\dagger X.
\]

The complete finite-dimensional quotient statement is now unconditional in Lean:

\[
X^\dagger X=Y^\dagger Y
\quad\Longleftrightarrow\quad
\exists U,\ U^\dagger U=I_3\ \text{and}\ UX=Y,
\]
every positive \(2\times2\) Hermitian record occurs, and the quotient by equality of records is
homeomorphic to the positive cone
\[
M_{3,2}(\mathbb C)/U(3)\cong H_2(\mathbb C)_{\ge0}.
\]
The Lean realization is
`formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiOrbit.lean`.

Under Pauli coordinates, \(H_2(\mathbb C)_{\ge0}\) is the closed \(3+1\)-dimensional Minkowski
future cone. This does not yet prove that the quotient is physical spacetime.

## Post-freeze correction: why four dimensions

The left color dimension does **not** select four-dimensional spacetime. More generally, for every
\(n\ge2\),
\[
M_{n,2}(\mathbb C)/U(n)\cong H_2(\mathbb C)_{\ge0}.
\]
The public cone is controlled by the surviving two-dimensional complex alternative space, not by
the hidden carrier dimension.

The sharper physical hunch is therefore:

> **The universe has four dimensions because an elementary objective fact has two complex quantum
> alternatives.**

The exceptional source remains essential for selecting the simultaneous hidden
\(\mathbb C^3\), public \(\mathbb C^2\), chirality, and exact Standard Model action. It is not
responsible for four dimensions merely because color has dimension three.

A source-selection theorem must derive, rather than assume:

1. why an elementary public fact is irreducibly binary;
2. why its scalars are complex rather than real, quaternionic, or a generic spin factor;
3. why the same source selects the exceptional three-dimensional hidden carrier; and
4. why independent composition preserves this binary complex public record.

Barnum--Wilce show that homogeneous self-dual Jordan systems, local tomography, and the existence
of a qubit strongly select ordinary complex quantum theory
([arXiv:1202.4513](https://arxiv.org/abs/1202.4513)). This is relevant reconstruction machinery,
not the missing event-source theorem.

## New corollary hunch: mass is hidden event entanglement

Treat \(X\in\mathbb C^3\otimes\mathbb C^2\) as an unnormalized bipartite pure event. Then
\(X^\dagger X\) is its reduced positive record on the binary factor. The exact Cauchy--Binet law is
\[
\det(X^\dagger X)
=\sum_{0\le i<j\le2}|X_{i0}X_{j1}-X_{j0}X_{i1}|^2.
\]
The right side is the squared area/entanglement content of the two columns. Hence the already
formalized algebra gives:

- rank-one separable events lie on the public light cone;
- rank-two entangled events lie in the timelike interior; and
- the public Lorentz interval equals a hidden bipartite area invariant.

The mathematical identity is known in quantum information; determinant/concurrence and Lorentzian
qubit geometry are not new. See, for example, the determinant/inner-product interpretation in
[arXiv:2207.03721](https://arxiv.org/abs/2207.03721) and Lorentzian entanglement geometry in
[arXiv:1801.00611](https://arxiv.org/abs/1801.00611).

The new physical conjecture would be:

> **Rest mass is the invariant entanglement between the hidden ways an event can happen and the
> binary record by which the event becomes public.**

This would explain light and mass in one sentence:

> **Light is an event that can become public without hiding a quantum alternative. Matter is an
> event that cannot.**

No dynamics, normalization, dimensional constant, observed particle spectrum, or equivalence
principle has yet been derived from this interpretation. It is a conjectural corollary, not a
result.

## One curvature, not four pasted actions

Let \(\mathcal A\) denote the still-undefined source-positive actuality completion and let
\(\nabla^{\mathcal A}\) be its canonical comparison connection. The required theorem is not
\[
S_{\rm GR}+S_{SU(3)}+S_{SU(2)}+S_{U(1)}
\]
written in new variables. It is a representation theorem for one curvature
\[
\mathcal F_{\mathcal A}=(\nabla^{\mathcal A})^2
\]
whose physically forced response decomposition is
\[
\mathcal F_{\mathcal A}
\rightsquigarrow
\bigl(
R_{\rm grav},
F_{SU(3)},
F_{SU(2)},
F_{U(1)},
\Phi_{\rm mixed}
\bigr).
\]

The vertical responses compare hidden factorizations and appear as gauge forces. The public
response compares causal record cones and appears as gravity. The mixed response changes the
representation by which hidden distinction becomes public and is the candidate Higgs/soldering
sector.

This reframes the weak/Lorentz collision. Identifying weak \(SU(2)\) with a chiral Lorentz factor
is established graviweak territory; see [arXiv:0706.3307](https://arxiv.org/abs/0706.3307) and
[arXiv:1212.5246](https://arxiv.org/abs/1212.5246). The proposed novelty cannot be that both use
\(SU(2)\). It must be a source-selected, support-changing comparison between two nonconjugate
actions, with no extra ghost sector and with the observed weak interaction still internal.

## Hypertranscendence must become necessity

Hypertranscendence cannot enter as decorative analytic complexity. The required theorem has the
form:

> **A regular actuality completion is globally flat exactly when its calibrated event history
> admits a finite source-compatible differential-algebraic identity.**

The corpus's hypertranscendence theorems would then prohibit the finite global identity and force
nontrivial comparison holonomy. Time and interaction would be consequences of irreducible
historical nonclosure:

> **Time is what remains when the universe cannot compress its history into its state.**

This equivalence is not proved. Without it, Hypertranscendence and event gravity remain adjacent
themes rather than one theory.

## New mathematics required

The jump requires a theory not presently in the corpus:

### 1. Source-positive actuality completion

Define a completion generated by reciprocal source events without primitive global identities,
dagger, object types, or supplied comparison maps. Reachable positive partial identities—not all
formal idempotent splittings—create successor types.

### 2. Event quotient representation theorem

Prove that finite irreducible event systems satisfying positivity, source reciprocity, public
separation, independent composition, and consequential minimality are represented by positive
Gram quotients of event amplitudes.

### 3. Exceptional source-selection theorem

Classify regular irreducible completions and prove that the one admitting the observed chiral
matter interface uniquely selects the exceptional \(M_{3,2}(\mathbb C)\) event and exact Standard
Model stabilizer, with no inserted spacetime or force group.

### 4. Identity-curvature decomposition theorem

Construct the canonical comparison connection and prove that its complete irreducible response
spectrum is exactly gravity, \(SU(3)\), \(SU(2)\), \(U(1)\), and one mixed soldering/Higgs sector.

### 5. Hypertranscendental nonflatness theorem

Equate finite horizontalizability of the comparison connection with finite
differential-algebraic closure of complete calibrated history, then invoke the corpus's
unconditional hypertranscendence results.

### 6. Continuum universality theorem

Show that the long-record limit uniquely satisfies Lorentzian locality, universal free fall,
Einstein dynamics, quantum probabilities, anomaly cancellation, and the Standard Model
low-energy action.

### 7. Finite discriminator

Derive at least one parameter-reducing observable not already built into GR plus the Standard
Model: a coupling relation, mass/entanglement law, strong-field deviation, cosmological relation,
or forbidden process.

## What the law would explain at once

If the seven theorems hold, the same source law would explain:

1. why there is spacetime rather than a spacetime background;
2. why our spacetime is \(3+1\)-dimensional;
3. why causal futures are positive and light is their rank boundary;
4. why matter carries the exact Standard Model symmetries;
5. why gravity couples universally to every public record;
6. why gauge force and gravity are both curvature without identifying their observed actions;
7. why mass is associated with timelike rather than null event structure;
8. why objective event succession gives an arrow of time;
9. why global identity cannot erase history; and
10. how other spacetime/force spectra could arise as other completions of the same universal law.

That explanatory compression is the Nature-level target.

## Priority boundary

The following are established and cannot be claimed as the discovery:

- positive Hermitian \(2\times2\) matrices as the Lorentz future cone;
- qubit information carrying Lorentzian geometry, including recent pre-spacetime derivations
  ([arXiv:2604.07471](https://arxiv.org/abs/2604.07471));
- reduced-density-matrix determinants as bipartite entanglement invariants;
- relational facts, quantum reference frames, and quantum Darwinism;
- gauge and gravitational fields as connections/curvatures;
- graviweak identification of chiral \(SU(2)\) factors;
- Karoubi or condensation completion creating split sectors; and
- exceptional Jordan geometry producing the Standard Model group.

Possible novelty begins only with necessity and uniqueness:

> objective-event axioms force event-generated identity; its positive quotient is spacetime; one
> source-selected curvature yields exactly all four forces; the exceptional completion is our
> world; and at least one new observable follows.

## Hostile kill conditions

Retire this realization if any remains after serious repair:

1. event-created identity is equivalent, with all source observables preserved, to a supplied
   process category plus ordinary gauge choice, reference-frame change, or condensation;
2. the positive quotient is optional rather than forced by operational equivalence;
3. binary complex public alternatives must be inserted independently of the exceptional source;
4. one comparison connection cannot separate weak isospin from Lorentz transport without adding
   unrelated bundles or ghost degrees of freedom;
5. the claimed one curvature is only a direct sum of familiar connections;
6. Hypertranscendence cannot be linked to physical nonflatness by an if-and-only-if theorem;
7. the continuum limit does not yield universal free fall and the tested Einstein regime;
8. anomaly freedom, chirality, or observed matter representations fail;
9. no finite parameter-reducing prediction exists; or
10. a prior theory already proves the same source-to-spacetime-to-four-force necessity theorem.

## Gates

- [x] 0 → 1: proof-route-blind hunch, explanatory target, exact shadows, priority collisions, new
  mathematics, and kill conditions recorded
- [ ] 1 → 2: source-positive completion, representation, source-selection, one-curvature,
  Hypertranscendental nonflatness, continuum, and finite prediction theorems paper-proved
- [ ] 2 → 3: every mathematical theorem formalized unconditionally in Lean
- [ ] 3 → 4: independent priority, quantum-foundations, gravity, particle-physics, experiment,
  statistics, and hostile Nature reviews passed

Current Nature verdict: `[DO NOT WRITE MANUSCRIPT]`.

## Log

- 2026-07-29 — extracted event-generated physical identity as common interpretation of the
  corpus's fixed-carrier, totalization, nonconjugacy, support-change, boundary-memory,
  recognition-defect, and Hypertranscendence obstructions.
- 2026-07-29 — corrected the four-dimensionality hunch: the public dimension follows from two
  complex surviving alternatives, not from the hidden color dimension.
- 2026-07-29 — isolated the exact finite quotient theorem in Lean: equality of Gram records is
  exactly left-unitary equivalence, every positive record occurs, and the record quotient is
  homeomorphic to the positive two-cone.
- 2026-07-29 — identified Lorentz mass-squared with the already formalized squared-minor
  entanglement area and froze “mass is hidden event entanglement” as a physical corollary hunch.
- 2026-07-29 — hostile priority audit classified qubit/Lorentz geometry, determinant
  entanglement, graviweak \(SU(2)\), relational facts, and categorical completion as occupied.
  Necessity, uniqueness, one-curvature dynamics, Hypertranscendental nonflatness, and prediction
  remain the discovery.

## Post-freeze polar-decomposition attack

`[WEAK ROUTE KILLED] [POSITIVE SURVIVOR]`

Every invertible Hilbert-space comparison has a polar decomposition
\[
T=UP,\qquad U^\dagger U=I,\qquad P\ge0.
\]
It is tempting to call \(U\) gauge transport and \(P\) gravity. That is not a discovery. Polar and
Cartan decompositions, complexified gauge groups, noncompact gauge--spacetime unification, and
dynamical tetrads are established constructions. Recent examples include a noncompact
gauge--spacetime mechanism
([arXiv:1512.03328](https://arxiv.org/abs/1512.03328)) and
\(SL(2N,\mathbb C)\) hyperunification with dynamical tetrads
([arXiv:2511.19210](https://arxiv.org/abs/2511.19210)).

Therefore the law cannot be:

> unitary part equals gauge; positive part equals gravity.

That statement is generic operator theory and does not select an event, a physical quotient, a
force group, locality, dynamics, or a prediction.

The strongest survivor is source-sensitive and support-changing:

> **An objective event must canonically generate a partial polar comparison whose positive support
> is exactly the new public causal identity and whose partial-isometric support transport is
> exactly the retained internal identity.**

This differs from ordinary polar decomposition only if all of the following are proved:

1. the comparison is forced by reciprocal event source data rather than chosen on a supplied
   Hilbert bundle;
2. its initial and final supports are the exact noninvertible `4/6/4` possibility--record faces;
3. the positive factor is operationally the complete public record quotient;
4. the partial isometry carries exactly the exceptional Standard Model stabilizer;
5. successor composition determines one connection on these generated supports;
6. no global invertible comparison preserves source, positivity, composition, probability, and
   calibration; and
7. the continuum curvature has exactly the Einstein and Standard Model limits.

The attack sharpens the new-math target: `source-positive actuality completion` needs a
**source-selected partial polar theorem**, not another polar decomposition theorem.

- 2026-07-29 — killed generic “unitary comparison is gauge and positive comparison is gravity” as
  novelty. Preserved the source-selected partial-polar/support-change theorem as a precise
  realization target.

## Nature editorial gate

Nature requires original research of outstanding scientific importance with an interdisciplinary
conclusion. Its pre-review editors additionally ask whether results are novel, arresting, and have
both immediate and far-reaching implications
([editorial criteria](https://www.nature.com/nature/for-authors/editorial-criteria-and-processes)).

Current hostile assessment:

| Nature test | Current status |
|---|---|
| Original main result | **Fail.** Universal source law remains conjectural; exact proved bridges are standard. |
| Outstanding scientific importance | **Conditional pass.** Deriving spacetime and all forces from objective events would qualify if established. |
| Interdisciplinary conclusion | **Pass at conjecture level.** Claim joins quantum foundations, gravity, particle physics, exceptional algebra, and Hypertranscendence. |
| Novel and arresting | **Headline pass, evidence fail.** Public claim is arresting; necessity/uniqueness theorem is absent. |
| Immediate implications | **Fail.** No finite observable, parameter reduction, or experimental analysis yet. |
| Far-reaching implications | **Conditional pass.** Would reinterpret time, matter, spacetime, mass, and force if the continuum theorem holds. |
| Technical case established | **Fail.** Source-positive completion, one-curvature theorem, Einstein limit, and quantum dynamics are open. |
| Nonspecialist readability | **Promising.** “Matter and spacetime are two halves of one quantum fact” communicates the worldview shift. |

The editorial gate stays closed until the conjecture yields at minimum:

1. one source-selection/uniqueness theorem;
2. one continuum dynamics theorem recovering a tested nontrivial limit; and
3. one finite falsifiable prediction not inserted as an axiom.

## Sixth failure-driven jump: quantumness obstructs identity composition

`[EXACT BRIDGE] [STANDARD MATHEMATICS] [PHYSICAL CONJECTURE SHARPENED]`

The generic polar-decomposition route was too weak because it began with one supplied Hilbert
space and renamed its unitary and positive factors. The support-changing route has a stronger
exact invariant.

Let \(u\) and \(v\) be the partial isometries created by two successive event amplitudes. They
create, rather than merely preserve, the interface identities
\[
t(u)=uu^\dagger,
\qquad
s(v)=v^\dagger v.
\]
Define
\[
\mathcal K(v,u)=[t(u),s(v)].                                      \tag{EG31}
\]
The newly paper- and Lean-proved theorem gives, in every unital \(C^*\)-algebra,
\[
\boxed{
\mathcal K(v,u)=0
\quad\Longleftrightarrow\quad
vu\text{ is again a partial isometry}.
}                                                                  \tag{EG32}
\]
See
[`event-identity-transport-curvature.md`](../3-formalized/not_new_scientific_knowledge/event-identity-transport-curvature.md)
and
`formal/GaloisForLFunctions/HTGeometry/EventIdentityTransportCurvature.lean`.

Equation `(EG32)` is the Halmos--Wallen product criterion and is not new mathematics. Its new role
in the research programme is exact: quantum noncommutativity at the event boundary is literally
the obstruction to composing the identities created by successive events. A nonzero commutator
is not yet gravity or gauge curvature. It says that strict event identity has ceased to exist under
ordinary composition; a successor law must change support, lose information, or create a new
comparison.

Public compression:

> **Quantum events can create identities that cannot be composed.**

Stronger conjectural worldview:

> **Spacetime and force are the universe's canonical record of repairing quantum identities that
> cannot be composed. Gravity is the public part of that repair; gauge force is its hidden part.**

This is the first candidate mechanism in the current route where “quantumness creates curvature”
is an exact implication at the structural level rather than a metaphor. It remains far short of
physical unification: Thomas--Wigner rotation already realizes the invertible Lorentz shadow, and
Uhlmann transport already realizes a mixed-state holonomy shadow. Novelty can only lie in a
source-generated, support-varying repair theorem that derives its own carriers and forces.

### Sharpened source theorem

The missing mathematical object is now a **source-generated support-varying polar completion**.
Starting without supplied object identities, global dagger, Hilbert bundle, spacetime, or force
connection, it must prove:

1. objective events generate their source and target positive identities;
2. `(EG31)` is the complete obstruction to strict successor composition;
3. nonzero `(EG31)` canonically creates a minimal comparison cell, with no chosen dilation,
   environment, or connection;
4. comparison cells satisfy coherent triple and independent-product laws;
5. public quotient of the cell is the complete positive causal record, while its vertical
   automorphisms are retained internal identity;
6. the exceptional source uniquely selects the complex binary public alternative, hidden color
   triple, chirality, and exact \(S(U(3)\times U(2))\) global group;
7. one comparison-cell curvature has exactly Einstein, \(SU(3)\), \(SU(2)\), \(U(1)\), and mixed
   Higgs/soldering responses in the continuum, not a direct sum inserted by hand;
8. its complete calibrated reporter is finitely horizontalizable exactly in the
   differential-algebraic phase; and
9. the construction removes at least one free parameter or predicts one finite observable beyond
   GR plus the Standard Model.

Hypertranscendence is deliberately absent from the local equation `(EG32)`. The corpus proves that
Hypertranscendence is a relative gauge obstruction in specific translation systems, but also that
flat connections can have infinite holonomy. The bridge becomes physical only after item 8 derives
the accumulated reporter from the event source.

- 2026-07-29 — hostile-tested polar-composition curvature against Thomas--Wigner and Uhlmann
  holonomy; classified both as occupied shadows.
- 2026-07-29 — extracted and Lean-formalized the exact Halmos--Wallen survivor `(EG32)` in every
  unital \(C^*\)-algebra.
- 2026-07-29 — sharpened the universal conjecture from “comparisons have curvature” to “quantum
  event identities fail to compose, and physical geometry is the canonical repair.”

## Seventh failure-driven jump: a quantum difference can become a distance

`[FROZEN CONJECTURE] [EXACT SHADOWS] [SOURCE THEOREM OPEN] [NATURE GATE CLOSED]`

The support-repair formulation still says what reality does after composition fails, but it does
not say what must be preserved while the repair changes support. The obstruction corpus suggests
one stronger invariant:

> **Every real difference survives, but it need not survive as the same kind of difference.**

Public headline:

> **A quantum difference can become a spacetime distance.**

Worldview headline:

> **The universe is not made of things. It is the smallest reality that can preserve every
> difference its events create.**

Gravity headline:

> **Gravity is the curvature of quantum differences becoming public distances.**

The proposed universal law is not conservation of a scalar amount of information. It is
conservation of the *ability of future reality to distinguish physical histories*, even when the
carrier, type, adjoint, subsystem split, and meaning of the distinction change.

### Minimal exact transmutation law

`[CONJECTURE; PROVABILITY UNKNOWN]`

> **MINIMAL EXACT TRANSMUTATION LAW.** A physical world is the initial source-positive,
> future-separating completion of its objective events. No physically distinguishable source
> alternatives are erased: an event may remove their old continuation type only by creating a
> reciprocal record that distinguishes exactly those alternatives in its successors. No
> physically empty structure is added: every generated degree of freedom must distinguish some
> admissible intervention history. The reciprocal records compose coherently but need not commute.
> Their public positive quotient is spacetime, their hidden automorphisms are gauge symmetry,
> stable private distinctions are matter, their source order is time, and the noncommuting
> coherence of their type changes is the single curvature whose public and vertical responses are
> gravity and the three Standard Model forces.

Lay compression:

> **Nature never loses a difference. Matter stores it privately, spacetime stores it publicly,
> and force is the cost of moving it between the two.**

This adds two conditions missing from generic completion:

1. **no erasure:** every source distinction has a complete future discriminator; and
2. **no spectators:** every completed distinction is forced by some source intervention.

Together they are the type-changing analogue of observability plus reachability in minimal
realization theory. The discovery cannot be that minimal realizations exist for ordinary linear or
quantum systems. It must be that objective events force a unique positive minimal realization
which generates its own physical types and whose regular irreducible continuum is our observed
spacetime and force law.

### Why the additive version is false as the force carrier

For an event \(e:A\to B\), let \(L_e\) denote distinctions erased from direct continuation and
\(C_e\) distinctions created in the successor record. Every additive shadow has the index form
\[
[L_e]-[C_e]=[A]-[B].                                      \tag{EG33}
\]
The corpus proves this abstractly in `EventTopologicalDebt.lean`. Along a finite history, `(EG33)`
telescopes to the endpoint difference; on a closed history its total is zero.

Therefore neither dimension, entropy, a Grothendieck class, nor any other additive debt can itself
be force. A closed history may have zero total debt and nontrivial holonomy. The required
information is the source-generated equivalence and extension data
\[
\rho_e:L_e\simeq C_e                                      \tag{EG34}
\]
together with its coherent composition cells. Additive conservation is only the decategorified
shadow of `(EG34)`. Force must live in the noncommuting gluing of reciprocal records, not in their
rank difference.

This explains several previous false starts at once:

- scalar mixed curvatures missed flat but globally nontrivial holonomy;
- curvature plus outgoing transfer missed boundary self-action;
- kernel--cokernel equality conserved size but did not select a record;
- complete scalar histories retained simultaneous-similarity gauge;
- clock geometry plus conservation did not select dynamics; and
- bare source equations retained fixed-gauge ambiguity.

All six failures say that values and additive classes forget *how a lost distinction becomes a new
record*.

### Exact shadows already in the corpus

The following are rigorous shadows, not proof of the conjecture:

1. **Two-projection transmutation.** For sharp events \(p,q\), the sequential compression \(pqp\)
   is generally unsharp and its exact impurity is the positive square of the transition corner.
   Thus incompatible sharp distinctions already become positive probabilistic effects. This is
   standard Lüders/sequential-product theory, formalized in `SoninLudersPinching.lean`.
2. **Complementary-record lower bound.** If an event and its record are jointly faithful, the
   record is injective on every erased source direction. For equal finite source and target
   dimensions, a cokernel-valued record restricts to a kernel--cokernel bijection. This is
   formalized in `EventComplementaryRecord.lean`.
3. **Unitary defect transmutation.** Once a source involution and complete unitary are supplied,
   preserving and transmuting parts reconstruct the unitary; the erased source record is
   canonically equivalent to the created target cokernel. This is formalized in
   `SymmetryFractureDefectConservation.lean`.
4. **Topological debt.** Lost-minus-created classes equal source-minus-target classes and telescope
   through histories. This is formalized in `EventTopologicalDebt.lean`.
5. **Public Lorentz record.** For \(X\in M_{3,2}(\mathbb C)\), quotienting the hidden \(U(3)\)
   frame gives \(X^\dagger X\in H_2(\mathbb C)_{\ge0}\), the \(3+1\)-dimensional Lorentz future
   cone. This is formalized in `ColorGramMinkowskiOrbit.lean`.
6. **Mass shadow.** \(\det(X^\dagger X)\) is the squared hidden--public bipartite area. Null public
   records are rank-one separable events; timelike records have hidden event entanglement.
7. **Identity-composition obstruction.** The interface-support commutator vanishes exactly when
   successive partial identity transports remain composable. This is `(EG32)`, formalized in
   `EventIdentityTransportCurvature.lean`.
8. **Hypertranscendental global obstruction.** The corpus proves examples where complete
   calibrated history cannot be horizontally compressed into a finite differential-algebraic
   identity, while local flatness alone does not control global holonomy.

The common interpretation is:

> An event cannot destroy a physical distinction. It can only move that distinction from direct
> quantum continuation into probability, hidden matter identity, public causal record, or
> nontrivial interface memory.

### Priority collision audit

Every weaker phrase is occupied:

- Heylighen already formulated causality as “distinction conservation” in a Boolean/dynamical
  setting
  ([1989 paper](https://pespmc1.vub.ac.be/Papers/CausalityDist.pdf)).
- purification and no-hiding formulate conservation and relocation of information within
  operational or Hilbert-space quantum theory
  ([Chiribella--Scandolo](https://arxiv.org/abs/1411.2723),
  [Braunstein--Pati](https://arxiv.org/abs/gr-qc/0603046)).
- sequential products reconstruct Jordan and \(C^*\)-algebraic quantum structure from effect
  axioms ([van de Wetering](https://arxiv.org/abs/1803.11139)).
- universal constructions recover CPTP or partial CP maps from already supplied isometries,
  unitaries, daggers, and object types
  ([Huot--Staton](https://arxiv.org/abs/1901.10117),
  [Andrés-Martínez--Heunen--Kaarsgaard](https://arxiv.org/abs/2206.04814)).
- minimal quantum linear realizations use controllability and observability on a supplied quantum
  system ([Gough--Zhang](https://arxiv.org/abs/1311.1375)).
- quantum information flow has already been related to causal screens, holographic area, and
  emergent spacetime
  ([Markopoulou--Smolin](https://arxiv.org/abs/hep-th/9910146),
  [Van Raamsdonk](https://arxiv.org/abs/1005.3035)).
- entanglement equilibrium has already been connected to the semiclassical Einstein equation
  ([Jacobson](https://arxiv.org/abs/1505.04753)).

Novelty therefore cannot be “information is conserved,” “entanglement makes geometry,” “minimal
realizations are unique,” or “quantum channels are universal completions.” The open conjunction
is:

> event source itself generates the distinction types; erased quantum distinction and created
> causal record are source-canonically reciprocal; the minimal positive reciprocal completion is
> unique; and its one nonabelian coherence law forces both Einstein gravity and the exact Standard
> Model response spectrum.

### New mathematics required

The first genuinely new object is a **source-positive reciprocal exact completion** of an
identity-free event semicategory. It must:

1. generate reachable physical types from events rather than begin with object identities;
2. define equality by all admissible future discriminators without assuming a global reporter
   space;
3. derive local possibility--record reciprocity and positivity without a global dagger;
4. construct `(EG34)` from source data rather than choose a dilation, complement, environment, or
   basis;
5. retain the full extension and higher-composition data discarded by `(EG33)`;
6. be initial among future-separating positive completions and terminal against spectator
   extensions, or prove the precise replacement universal property if both cannot coexist;
7. reconstruct ordinary complex quantum theory in the fixed-type regular shadow;
8. classify finite irreducible completions and prove that the exceptional bi-Cayley source is the
   unique chiral completion with the observed response spectrum; and
9. admit a continuum descent whose interventional response, not geometry alone, yields dynamics.

The decisive first theorem is:

`[OPEN CORE: SOURCE-POSITIVE MINIMAL TRANSMUTATION]`

> Construct the completion above for a nontrivial raw event source and prove existence and
> uniqueness of its reciprocal record cells. Then prove that its complete scalar histories,
> together with independent-product incidence, reconstruct the completion up to exactly its
> internal gauge \(2\)-equivalence.

This theorem must survive the corpus's simultaneous-similarity and transported-factorization
no-go results. If it merely returns a fixed category of CP maps, a Karoubi envelope, a process
tensor, or a minimal linear system, the jump has failed.

### Physical deductions if the law is true

1. **Spacetime is converted quantum distinguishability.** Public distance is not a container for
   events; it is the positive record created when an old quantum distinction loses direct
   continuation.
2. **Mass is retained private distinction.** In the finite exceptional shadow, rest mass is the
   Lorentz norm produced by hidden--public event entanglement.
3. **Gravity is mandatory record compatibility.** Every public distinction gravitates because
   successor records must remain jointly distinguishable; there is no nongravitating information
   spectator.
4. **Gauge symmetry is exact public invisibility.** Gauge transformations are precisely
   automorphisms of the reciprocal record that preserve every public discriminator.
5. **All forces are one transmutation curvature.** Strong, weak, hypercharge, and gravitational
   responses are irreducible readings of how `(EG34)` fails to compose globally, not four added
   connections.
6. **Time is typed accumulation.** The arrow of time is the source order in which new
   discriminator types become available, not a coordinate supplied before events.
7. **Holography is minimality.** A complete public boundary record contains exactly the
   distinctions lost from direct continuation and no spectator bulk data.
8. **Black holes cannot erase a distinction.** Horizon formation may change its record type; a
   complete theory must exhibit the reciprocal boundary or successor record rather than invoke
   information conservation abstractly.
9. **No fifth response without a fifth distinction type.** An additional fundamental force must
   correspond to a new irreducible reciprocal-record channel and would falsify exceptional
   four-response completeness.
10. **Hypertranscendence is permanent type growth.** Complete history is Hypertranscendental when
    no finite differential-algebraic identity can carry every accumulated discriminator type.

Items 1--10 are conjectural deductions, not established physics.

### First quantitative discriminator

One mixed reciprocal-record cell must be readable both as:

1. a quantum/gauge phase of retained private distinction; and
2. a proper-time or frame holonomy of created public distinction.

Minimality forbids two independent normalizations. The source-selection theorem must therefore
fix a clock--charge phase conversion coefficient or an equivalent finite relation. A free
relative coefficient makes the proposed single transmutation curvature observationally identical
to GR plus an independently chosen gauge connection and kills the law.

### Hostile kill conditions

Retire the transmutation law if any survives:

1. source-positive reciprocal completion does not exist or has inequivalent minimal solutions;
2. future separation cannot generate physical types without inserting a global test category;
3. `(EG34)` requires a chosen complement, dagger, environment, or metric not forced by the event;
4. every model is equivalent to ordinary information conservation in one fixed Hilbert space;
5. additive debt is the only invariant and all higher gluing can be strictified away;
6. arbitrary laboratory Lüders measurements satisfy the axioms and therefore falsely create
   spacetime or fundamental force;
7. the completion admits spectator sectors not detected by any source intervention;
8. the exceptional source is not uniquely selected or yields extra forces, wrong chirality,
   ghosts, or peer generations;
9. continuum descent fails to give local Lorentz invariance, universal free fall,
   Einstein--Dirac--Yang--Mills--Higgs dynamics, and observed quantum probabilities;
10. Hypertranscendence remains an appended reporter property rather than a theorem of complete
    source history; or
11. no finite parameter relation, forbidden process, or strong-field deviation is derived.

Current verdict: the conjecture is a stronger explanatory jump than identity curvature alone, but
it is not yet a result. The first publishable advance would be the source-positive minimal
transmutation theorem, not another formalization of a known compression or index identity.

- 2026-07-29 — killed naive “distinction conservation” and “information becomes geometry”
  wordings by priority audit.
- 2026-07-29 — identified type-changing, nonabelian, source-minimal reciprocal record completion
  as the novel residue.
- 2026-07-29 — froze “a quantum difference can become a spacetime distance” as the public
  conjecture and isolated source-positive minimal transmutation as the exact open core.
