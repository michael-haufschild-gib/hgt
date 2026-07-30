# The universe has one state; physics is how it witnesses itself

- **ID:** `closed-universe-self-witness-resolution-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL PHYSICS CONJECTURE / CLOSED-UNIVERSE QUANTUM GRAVITY /
  NEW-MATHEMATICS TARGET
- **Status:** `[CONJECTURE] [TRUE-JUMP CANDIDATE] [PRIORITY INCOMPLETE]`
  `[NO CONTINUUM PHYSICS PROVED] [NATURE: DO NOT WRITE]`
- **Root:** `no-outside-witness-self-unfolding-law.md`
- **Finite source shadow:**
  `../3-formalized/not_new_scientific_knowledge/complete-comparison-reciprocity-rigidity.md`
- **Lean shadows:**
  `formal/GaloisForLFunctions/HTGeometry/CompleteComparisonReciprocity.lean`,
  `formal/GaloisForLFunctions/HTGeometry/SimplexAugmentedContraction.lean`
- **Statement:** A closed universe's unique global fact is not physically empty: the universe
  internally generates a complete higher resolution of ways to witness that fact, and quantum
  theory, spacetime, matter, and force are jointly conservative shadows of its higher
  self-relations.

## Public law

> **The universe has no outside. Reality must witness itself.**

Closed-universe form:

> **The universe may have only one global state. Everything we call physics is how that state
> witnesses itself.**

Sharper worldview:

> **Particles are persistent self-relations, spacetime is their public compatibility, and forces
> are the ways those relations fail to flatten into one account.**

These are proof-independent conjectures, not established conclusions.

## Why this is a larger reinterpretation

Several current quantum-gravity programmes report a striking tension:

1. the nonperturbative physical Hilbert space of a closed universe may be one-dimensional in each
   superselection sector;
2. an internal observer nevertheless experiences a large effective quantum state space,
   noncommuting observables, probabilities, and time; and
3. existing resolutions obtain the larger structure by adding an observer, partial source,
   unconstrained Hilbert space, conditioning datum, or observer-relative algebra.

The no-outside law reverses the last step. The observer or partial source may not be an extra
ingredient. If the universe is physically closed, the unique global fact must generate the
internal cuts by which it becomes observable.

The proposed primitive is therefore neither a many-dimensional universal wavefunction nor a
one-dimensional state by itself. It is

```text
one global fact
  + the complete source-generated higher structure of its internal self-witnesses.
```

The global state count is a degree-zero decategorification. It can be one while the complete
self-witness structure retains nontrivial automorphisms, extensions, higher operations,
comparison defects, and observer-relative positive representations.

## Universal self-witness resolution conjecture

Let \(S\) be a finite raw source presentation of a closed physical history. It may contain
distinction, incidence, counterfactual compatibility, and source extension, but no Hilbert space,
scalar field, positivity, tensor product, observer, subsystem, spacetime, time parameter, force
label, or target process category.

Conjecture that \(S\) generates:

1. one terminal public fact \(\mathbf 1_S\);
2. a spectator-free higher witness object \(\mathfrak W(S)\) whose objects and higher cells are
   internally generated partial accounts of \(\mathbf 1_S\);
3. a source-generated positive involutive realization of the higher self-relation object
   \[
   \mathfrak A(S)
   :=
   \mathbb R\!\operatorname{End}_{\mathfrak W(S)}(\mathbf 1_S);
   \tag{CW1}
   \]
4. nonconservative coherent, causal, and compositional reporters of \(\mathfrak A(S)\) whose
   complete family is jointly conservative; and
5. source-changing witness correspondences under which every irreducible failure of a present
   resolution becomes one generator of the next resolution layer.

Notation `(CW1)` names a construction target. A derived category, enhancement, endomorphism
object, scalar field, positivity cone, or composition law may not be supplied in advance.

The load-bearing law is the role-changing transgression
\[
\boxed{
\mathsf{ResidualWitness}_h
\;\simeq\;
\mathsf{NewWitnessOperation}_{h+1}.
}
\tag{CW2}
\]

The two sides must be defined independently from source consequences. Defining the right side as
a renamed copy of the left makes `(CW2)` tautological and kills the conjecture.

## No-outside exactness

A finite physical account is allowed to have a residual obstruction. Complete reality is not.
The conjecture therefore asks for a nonterminating self-resolution:

```text
fact
  -> internal accounts
  -> comparisons
  -> residual disagreement
  -> new comparison operation
  -> higher accounts
  -> higher disagreement
  -> ...
```

At every finite stage, residual classes remain observable. At the next stage, each residual
changes role from passive failure to active operation. No source distinction disappears, and no
successor operation arrives from outside.

This is stronger than saying that every obstruction eventually vanishes. The obstruction is
conserved by type promotion. A complete tower has no unaccounted external residue, while
Hypertranscendence says no finite differential-algebraic truncation remains faithful to the whole
tower.

The proposed law can be summarized as

\[
\boxed{
\text{no outside}
\quad=\quad
\text{every residual is internally witnessed again}.
}
\tag{CW3}
\]

## Exact finite seed

The complete-comparison theorem already formalized in Lean gives the first source shadow.
If one connected fact has \(n\) internally generated accounts, every pair is compared, and the
comparison layer has exactly one irreducible disagreement, then

\[
n=3,\qquad
\#\text{comparisons}=3,\qquad
\operatorname{rank}(\text{reduced accounts})=2.
\tag{CW4}
\]

The empty triangle has the exact witness sequence

\[
0\longrightarrow F
\longrightarrow F^3
\longrightarrow F^3
\longrightarrow F
\longrightarrow0,
\tag{CW5}
\]

with the last \(F\) representing its unique loop disagreement. Adjoining the one missing
two-dimensional filler turns the triangle into the full simplex. The normalized augmented
full-simplex complex contracts to its augmentation point and is exact in every positive degree.

Thus the smallest current seed has a literal self-resolution reading:

```text
one fact
  -> three accounts
  -> three comparisons
  -> one disagreement
  -> one generated filler.
```

`CompleteComparisonReciprocity.lean` unconditionally proves `(CW4)` and the
\(2\to3\to1\) reduced ranks. `SimplexAugmentedContraction.lean` unconditionally proves the
all-degree normalized augmented-simplex contraction. These are standard finite topology and
homological algebra. Their physical interpretation and source purity are not proved.

## Closed-universe bridge

Current primary parents make the target unusually concrete:

- Harlow--Usatyuk--Zhao argue that a closed-universe quantum-gravity Hilbert space is
  one-dimensional and real while an observer has an approximate effective Hilbert space of
  dimension roughly \(e^{S_{\rm Ob}}\), with exponentially small errors:
  <https://arxiv.org/abs/2501.02359>.
- Chen formulates gravitational path integrals using sources and partial sources; partial sources
  can produce nontrivial sectors with noncommuting operators:
  <https://arxiv.org/abs/2505.15892>.
- Nomura--Ugajin derive predictions by partial observability and conditioning in a closed
  Lorentzian universe:
  <https://arxiv.org/abs/2505.20390>,
  <https://arxiv.org/abs/2602.13387>.
- Miyata--Horikoshi--Tajima--Ugajin exhibit one-dimensional closed-universe superselection sectors
  after a large gauge constraint in a symmetric-orbifold CFT, while the pre-constraint and
  observer-coupled structures remain much larger:
  <https://arxiv.org/abs/2606.04575>.
- De Vuyst--Eccles--Hoehn--Kirklin prove observer dependence of gravitational entropy and connect
  the relevant observers to quantum reference frames:
  <https://arxiv.org/abs/2405.00114>.

These works own the general conclusions that a closed universe can have one physical state and
that observer-relative or partial-source structure can recover nontrivial physics. They do not
establish `(CW2)`, generate the observer/witness object from the unique fact, or derive all
interactions from its higher self-relations.

## Derived-endomorphism collision

The phrase “physics is higher self-relations” also has strong mathematical and physical parents:

1. derived endomorphism algebras and Koszul duality recover an augmented algebra from the
   self-extensions of its distinguished object under double-duality hypotheses;
2. derived Morita theory reconstructs suitable stable categories from a compact generator and its
   derived endomorphism algebra;
3. open-string states between D-branes are represented by Ext groups; and
4. higher operations, Massey products, and obstruction towers are standard in
   \(A_\infty\), \(L_\infty\), deformation, and string-field theories.

Representative primary parents:

- Katz--Sharpe, *D-branes, open string vertex operators, and Ext groups*,
  <https://arxiv.org/abs/hep-th/0208104>;
- Kapustin--Li, *Open String BRST Cohomology for Generalized Complex Branes*,
  <https://arxiv.org/abs/hep-th/0501071>;
- Espic, *Koszul duality for categories with a fixed object set*,
  <https://arxiv.org/abs/2204.03389>;
- Lowen--Van den Bergh, *The \(B_\infty\)-structure on the derived endomorphism algebra of the
  unit in a monoidal category*, <https://arxiv.org/abs/1907.06026>; and
- Jasso--Muro, *Obstruction theory for \(A_\infty\) bimodules*,
  <https://arxiv.org/abs/2507.17568>.

Therefore neither derived endomorphisms, self-Ext, obstruction towers, nor a Morita
reconstruction theorem is candidate novelty.

Candidate novelty is restricted to the full conjunction:

1. a raw closed source generates its own witness category and distinguished fact;
2. no observer, partial source, scalar field, positivity, tensor product, or spacetime is supplied;
3. residual witness classes generate new operation types rather than only obstructing extensions;
4. the source-generated positive higher self-relation object uniquely reconstructs quantum
   probability, causal spacetime, matter, and interaction;
5. one regular phase forces \(3+1\) Lorentzian gravity and exactly
   \(U(1)\), \(SU(2)\), and \(SU(3)\), including observed representations and relative
   normalizations; and
6. the reconstruction yields a parameter-free prediction.

Without items 1--3 the proposal is known derived/observer architecture. Without items 4--6 it is
not a theory of everything or a Nature result.

## One-law physical dictionary

Every row is conjectural.

| Physical shadow | Self-witness reading |
|---|---|
| unique closed-universe state | one terminal public fact |
| quantum superposition | inequivalent coherent resolutions of that fact |
| Born probability | positive comparison law among coherent resolutions |
| observer | internally generated partial resolution, not an external system |
| time | order of role-changing witness transgressions `(CW2)` |
| spacetime | public compatibility geometry of internal witness resolutions |
| gauge symmetry | automorphism freedom inside one resolution |
| gauge force | vertical holonomy of internal resolution comparisons |
| gravity | obstruction to identifying public witness geometry across histories |
| matter | persistent mixed self-extension surviving repeated resolution |
| Higgs/soldering | conversion between internal resolution scale and public causal scale |
| holography | recovery of a resolution from complete seam/partial-source data |
| black-hole horizon | witness data that cannot descend to the same exterior resolution |
| multiverse | inequivalent maximal public resolutions of one source tower |
| Hypertranscendence | no finite reporter algebra remains conservative through all resolutions |

This dictionary is useful only if one reconstruction theorem forces all rows. Independent
realizations for different rows would recreate the collage failure.

## First quantitative bridge under test

The paper-proved finite-network theorem
`../2-fully-proven/arbitrary-graph-quantum-temporal-curvature-law.md` says that for a generic
connected finite system with local dimensions \(q_v\), the projective spectral temporal rank is

\[
\tau+1=\prod_v q_v.
\tag{CW6}
\]

If an internal observer's effective state-space size is \(D_{\rm Ob}\simeq e^{S_{\rm Ob}}\), the
finite stationary shadow suggests

\[
\boxed{
\tau_{\rm Ob}
\simeq
D_{\rm Ob}-1
\simeq
e^{S_{\rm Ob}}-1.
}
\tag{CW7}
\]

For a maximally projective finite stationary realization, the corresponding operator-norm
projective-return density at tolerance \(0<\varepsilon<2\) would be

\[
\boxed{
\delta_\varepsilon(S_{\rm Ob})
\simeq
\left(
\frac{2\arcsin(\varepsilon/2)}{\pi}
\right)^{e^{S_{\rm Ob}}-1}.
}
\tag{CW8}
\]

`(CW7)`--`(CW8)` are not current predictions. They combine an approximate quantum-gravity
observer-dimension proposal with a finite generic stationary theorem whose local-generator
formalization remains incomplete. The bridge assumes a stationary effective Hamiltonian,
spectral completeness, and an asymptotic observation limit. Near-resonance and finite-time
effects can delay the asymptotic regime arbitrarily. It is recorded because it is the first
parameter-free route connecting closed-universe witness entropy to an operational temporal
observable; it must be derived, formalized, and given a feasible protocol before promotion.

## Gravity target

The decisive continuum claim is not “observer dependence is gravity.” Observer-dependent entropy
and quantum-reference-frame transformations already occur in supplied gravitational theories.

The conjecture must prove:

\[
\boxed{
\text{Einstein curvature}
=
\text{continuum obstruction to path-independent comparison of
source-generated public witness resolutions}.
}
\tag{CW9}
\]

The right side must exist before a manifold, metric, connection, causal order, or Einstein action
is supplied. Its regular continuum limit must:

1. reconstruct a four-dimensional Lorentzian manifold or the exact accepted replacement;
2. derive local Lorentz invariance and the equivalence principle;
3. produce the Einstein equation with a derived stress-energy response;
4. separate external Lorentz action from internal weak \(SU(2)\);
5. derive the other gauge and matter equations from the same higher self-relation law; and
6. fix at least one relative normalization or dimensionless observable.

Anything less is analogy.

## Hostile falsifiers

Retire or sharply revise the conjecture if any survives serious repair:

1. realistic nonperturbative four-dimensional closed quantum gravity has no appropriate
   one-fact/one-sector limit;
2. \(\mathfrak W(S)\) requires an externally selected observer, partial source, tensor split,
   future-test alphabet, spacetime, or target category;
3. inequivalent derived enhancements of one source give different physical self-relation
   algebras with identical source consequences;
4. a free or cofree witness resolution satisfies every proposed source axiom;
5. `(CW2)` is definitional or fails to make an obstruction executable as a genuinely new
   successor operation;
6. the family of physical reporters is conservative only because an identity reporter was
   included;
7. one-dimensional global state plus higher self-relations is equivalent to an existing
   closed-universe observer formalism after notation is removed;
8. real, quaternionic, exceptional, tensor-padded, higher-dimensional, or fifth-force phases obey
   the same source law;
9. gravity and internal gauge responses retain independent free scales;
10. the regular continuum fails quantum field theory, general relativity, or Standard Model
    precision tests;
11. `(CW7)`--`(CW8)` are not source-invariant or cannot be operationally distinguished from
    ordinary finite-system recurrence; or
12. no parameter-free observable differs from GR plus the Standard Model.

## Exact open core

`[OPEN CORE: SOURCE-GENERATED SELF-WITNESS RESOLUTION]`

Construct one finite raw closed source \(S\) for which:

1. the terminal public fact is unique;
2. at least two internal witness resolutions are generated rather than selected;
3. their comparison object and higher cells are source-derived;
4. the unique first residual disagreement canonically generates one new filler operation;
5. source extension repeats the construction without a supplied target operation alphabet;
6. coherent, causal, and compositional reporters are individually lossy but jointly conservative;
7. no fixed-carrier totalization preserves all source distinctions and operation-type promotions;
   and
8. the first regular irreducible positive realization is uniquely the required complex
   \(3\times2\) phase or yields an exact alternative classification.

Items 1--5 are the first theorem target. Items 6--8 may not be added as dimension-matching axioms.
After a dependency-closed paper proof, every mathematical claim must be formalized
unconditionally in Lean.

## Nature gate

Nature requires original research, outstanding scientific importance, and an interdisciplinary
conclusion; editorial triage additionally asks whether results are novel, arresting, immediate,
and far-reaching:
<https://www.nature.com/nature/for-authors/editorial-criteria-and-processes>.

- [x] arresting no-outside headline separated from mathematical claims
- [x] closed-universe one-state literature bridge identified
- [x] observer/partial-source and derived-endomorphism priority collisions recorded
- [x] exact \(1\to3\to3\to1\) finite shadow linked to existing Lean
- [ ] source-generated witness category constructed
- [ ] non-tautological obstruction-to-operation transgression proved
- [ ] positive/involutive realization reconstructed without target physics
- [ ] unique complex \(3\times2\) regular phase classified
- [ ] quantum probability and \(3+1\) causal spacetime derived
- [ ] exact gauge/gravity/matter split and relative normalization derived
- [ ] continuum Einstein--Dirac--Yang--Mills--Higgs dynamics derived
- [ ] quantitative closed-universe observable derived and protocol supplied
- [ ] exhaustive specialist novelty audit passed
- [ ] every mathematical claim unconditionally Lean-proved

## No-go closure

- **Exact killing theorem/mechanism:** open.
- **Strongest positive survivor:** complete-comparison one-disagreement rigidity and the normalized
  augmented-simplex contraction are already unconditional Lean theorems. Current closed-universe
  literature independently supports a one-global-state/many-internal-observations tension.
- **New insight:** global Hilbert-space dimension and physical richness need not measure the same
  layer. The universal-law target should reconstruct physics from the higher self-witness
  resolution of the unique fact, not add an observer to a globally trivial state.
- **Status:** universal physical reconstruction, continuum dynamics, and observable remain open.

## Log

- 2026-07-30 — froze the closed-universe self-witness resolution conjecture after auditing
  one-dimensional closed-universe Hilbert spaces, partial-source/observer constructions, derived
  endomorphisms, D-brane Ext spectra, and obstruction-theory parents.
- 2026-07-30 — identified the existing exact \(1\to3\to3\to1\) comparison sequence and augmented
  simplex contraction as the first finite self-resolution shadow, without promoting its physical
  interpretation.
- 2026-07-30 — recorded the conditional observer-entropy/temporal-rank bridge
  `(CW7)`--`(CW8)` as a possible parameter-free observable route, with stationary, generic,
  asymptotic, and formalization caveats explicit.

## First source-only theorem: promote the ambiguity, not one value

The child theorem
[`triangle-fact-orientation-transmutation.md`](../2-fully-proven/not_new_scientific_knowledge/triangle-fact-orientation-transmutation.md)
closes the first static attack.

For the unlabeled three-account source, the augmented comparison sequence is not merely a
dimension pattern. It is an exact source-symmetry sequence
\[
0\longrightarrow O_1
\longrightarrow E_3
\longrightarrow Q_2
\longrightarrow0,
\tag{CW10}
\]
where \(E\) is the comparison layer, \(Q\) the independent-account layer, and \(O\) the unique
loop-disagreement. The residual \(O\) is the sign/orientation representation of the source
automorphism group. An odd relabeling reverses it, so
\[
O^{S_3}=0.
\tag{CW11}
\]

Consequently the unlabeled source cannot choose a nonzero orientation, clockwise cycle, or
absolute time arrow. Doing so inserts an outside ordering. But the source canonically determines
the orientation **type** and an equivariant filler boundary
\[
O\longrightarrow E.
\tag{CW12}
\]

This changes the candidate law:

> **A closed universe does not resolve an internally unchoosable ambiguity by selecting one
> value. It promotes the entire ambiguity representation into a new physical type.**

The theorem is classical finite mathematics, now formalized unconditionally in
`TriangleFactOrientationTransmutation.lean`. Candidate novelty remains the claim that physical
reality iterates this equivariant promotion without a supplied category and that its positive
regular phase is uniquely observed physics.

### Exact gain

The \(3\times2\) target now has one source-native origin:
\[
\dim E=3,\qquad \dim Q=2,\qquad \dim O=1,\qquad E/O\simeq Q.
\tag{CW13}
\]
After a still-unproved source derivation of complex scalars, all faithful linear deformations lie
in
\[
\operatorname{Hom}_{\mathbb C}(Q_{\mathbb C},E_{\mathbb C})
\cong M_{3,2}(\mathbb C).
\tag{CW14}
\]
This does not derive complexification, positivity, or physics, but it replaces independent
\(3\), \(2\), and \(1\) guesses by one exact self-witness sequence.

### Exact quadratic public quotient

The connector
[`no-outside-quadratic-witness-descent.md`](../3-formalized/not_new_scientific_knowledge/no-outside-quadratic-witness-descent.md)
proves the first regular public-report law. A scalar reporter invariant under all relabelings
restricts to an even function \(r\) on the complexified orientation residual. If \(r\) is entire,
then
\[
r(a)=R(a^2)
\tag{CW15}
\]
for an entire \(R\). The orientation value is not public, but every entire scalar fact about it
descends through its squared coordinate.

This turns items 1--2 of the open core into a longer exact finite chain:

```text
source residual transforms as sign
  -> no invariant nonzero representative
  -> invariant entire reports are even
  -> every such report factors through the orientation square.
```

The source-odd positivity theorem independently proves that a nonzero positive law cannot remain
odd and that positive even information survives as reciprocal Gram squares. The finite
source-derived passage to a Hermitian positive square is now proved and Lean-formalized in
[`triangle-source-hermitian-lift.md`](../3-formalized/not_new_scientific_knowledge/triangle-source-hermitian-lift.md):
triangle source symmetry generates the conjugate complex phase algebra, retains both conjugate
account directions, fixes the positive account metric up to scale, and yields the exact complex
\(1\to3\to2\) sequence and \(M_{3,2}(\mathbb C)\) Gram carrier.

### Exact loss

Existing Lean theorems identify a Boolean orientation network with
\(\mathbb Z_2\) clock calibration and prove every global orientation assignment flat. Therefore
`(CW11)`--`(CW12)` can generate only the first clock-orientation torsor. Its loop holonomy detects
failure of global time orientation, not local Riemann curvature.

The next load-bearing theorem must derive relative transport between independently generated
witness types and enlarge the order-two torsor to a complete Lorentz clock/frame transporter.
Only its infinitesimal non-integrability can be tested against gravity.

## Revised open core after the symmetry attack

`[OPEN CORE: DYNAMIC EQUIVARIANT SELF-PROMOTION]`

Construct a source extension law for which:

1. each stage generates its residual representation functorially;
2. no invariant representative is selected when the source symmetry forbids one;
3. the residual representation becomes a genuinely executable successor operation type;
4. comparison of two promoted types is source-derived, not an arbitrary edge calibration;
5. iteration physically identifies and composes the now source-derived Hermitian Gram records,
   with normalization fixed by successor conservation rather than an inserted probability rule;
6. the first regular irreducible positive deformation is uniquely complex \(3\times2\);
7. the continuous comparison object separates internal weak transport from external Lorentz
   transport; and
8. its complete infinitesimal loop law reconstructs Riemann curvature and the three internal
   gauge curvatures with one derived normalization.

The static triangle now satisfies the source-symmetry part of items 1--2. Items 3--8 remain open.

## Additional log

- 2026-07-30 — proved and Lean-formalized the first source-symmetry no-go: the unlabeled triangle
  residual is reversed by a source transposition, so no nonzero residual is source-natural.
- 2026-07-30 — extracted the strongest positive survivor: the source canonically generates an
  orientation representation and equivariant filler type without choosing an orientation.
- 2026-07-30 — rejected the false identification of its \(\mathbb Z_2\) holonomy with gravity;
  dynamic promotion to a complete Lorentz clock/frame comparison is now the active core.
- 2026-07-30 — proved and Lean-formalized that every entire source-natural scalar reporter of the
  orientation residual factors through its square; isolated sign-square to Hermitian-positive
  square as the next exact bridge.
- 2026-07-30 — closed that finite bridge: triangle source phase/conjugation, conjugate-complete
  doublet, invariant positive metric ray, complex exact sequence, \(M_{3,2}(\mathbb C)\) carrier,
  and positive Gram record are paper- and Lean-proved. Physical Born/causal identification and
  composition are now the active core.
