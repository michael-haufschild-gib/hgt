# Self-dual decorated clock boundary as the common obstruction object

- **ID:** `self-dual-decorated-clock-boundary`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT CONJECTURE / CROSS-REPRESENTATION OBSTRUCTION THEORY
- **Scientific status:** `[CONJECTURE] [THREE BARE-CLOCK NO-GOS PROVED] [NO BACKWARD CLOCK FORMALIZED] [COMPACT PROFINITE CARRIER KILLED] [TATE SOURCE REALIZATION OPEN]`
- **Originating conjecture:** Different RH proof chains may be different representations of one
  obstruction interval: spectral incompleteness, continuation failure, positivity failure,
  monodromy, and noncanonical boundary conditions. Critical zeros would be the common self-dual
  degeneracy spectrum of that object.

## First correction: the interval cannot be bare

Let `(F,delta) subset (E,delta)` be a differential-field extension and let `B` be a finite
observable field. Put

```text
C(B) = {b in B : delta b in B}.
```

The prolongation/internal-core adjunction gives the counit-defect interval

```text
[J_1(C(B)),B].                                             (1)
```

For the HT jet tower `P_N=F(x,...,delta^(N-1)x)`, exact clock erosion and prolongation give

```text
C(P_(N+1))=P_N,
J_1(P_N)=P_(N+1),
```

so `(1)` is the zero interval at every cutoff. This proves that the originally proposed bare
adjunction interval cannot carry a nontrivial common spectrum.

There is a second tautological exactness. The clock symbol

```text
partial_B : B/C(B) -> E/B,
partial_B([b])=[delta b],                                  (2)
```

is well defined and injective: changing `b` by an element of `C(B)` changes `delta b` by an element
of `B`, and `partial_B([b])=0` is exactly the definition of `b in C(B)`. Thus `(2)` exposes the thin
boundary but has no intrinsic degeneracy spectrum either.

These are strong no-gos, not failures of the conjectural direction. They force the common object to
contain the external constraint selecting the particular HT function. Bare HT jet geometry is
universal and cannot distinguish Gamma, zeta, a Böttcher coordinate, or another differential
indeterminate.

There is a third, categorically sharper no-go. If `t` is transcendental over a field `P`, then

```text
IsEmpty(P(t) ->_P P).                                    (2a)
```

Indeed, a `P`-algebra homomorphism `r:P(t)->P` is injective. Hence
`t=algebraMap(r(t))`, contradicting transcendence. Every HT clock step is such a simple
transcendental extension, so the forward tower

```text
P_0 -> P_1 -> P_2 -> ...                                  (2b)
```

has no algebraic backward arrows at all. It is not an inverse system in the field category, even
noncanonically. Thus a backward clock operation cannot be discovered inside the HT field. A
residue, place, conditional expectation, Hilbert projection, analytic boundary value, or
self-adjoint extension is necessarily extra source-dependent structure in another category.

This turns noncanonical boundary conditions from one row of the proposed dictionary into a
structural theorem: **the universal HT clock has no algebraic closing operation**. The positive
replacement is a moduli problem of source-selected closures, not a search for a hidden field
retraction.

## Derived boundary at infinity `[CONJECTURE]`

The first two no-gos show that every bare finite boundary is exact. The third shows that these
finite boundaries cannot be assembled backward as fields. Therefore a nontrivial common spectrum
cannot be an intrinsic finite-level kernel. It must be created by a source-selected completion of
the one-way tower and can occur only as a defect of compatible closure at infinity.

A **source realization** should consist of:

1. a functor `R` from finite observable fields into an oriented topological or exact category;
2. source-defined generalized backward maps
   `u_N:R(P_(N+1))->R(P_N)`, which are not field homomorphisms;
3. a reflection-compatible Hermitian duality;
4. a distinguished affine section fixed by the source normalization.

For a countable inverse sequence of boundary modules

```text
A_0 <-u_0- A_1 <-u_1- A_2 <- ...,
```

the first candidate defect at infinity is

```text
D(A_*) = coker(1-S : product_N A_N -> product_N A_N),
(1-S)(a)_N = a_N-u_N(a_(N+1)).                            (2c)
```

This is the standard countable model of `lim^1`, so formula `(2c)` itself is `[BRIDGE]`. The
candidate-new assertion is source-specific:

> **[CONJECTURE]** A constrained HT function canonically determines an oriented self-dual
> realization whose common obstruction is the support of its derived closure defect. Different
> continuation, monodromy, positivity, spectral, and extension constructions represent the same
> obstruction only when they carry the same source-selected class in `(2c)`.

This formulation explains why finite exactness and a nontrivial global obstruction can coexist.
The obstruction is not stored in one jet layer; it is the failure to choose all backward closures
compatibly. It also gives the phrase "infinite algebraic clock capacity concentrated on a thin
constraint boundary" a precise candidate meaning: every layer is rank-one and nonsplittable as a
field step, while the global information is a derived defect of the entire boundary end.

The conjecture remains falsifiable. If the relevant source maps satisfy a Mittag--Leffler condition,
then `(2c)` vanishes and this derived carrier cannot hold the proposed spectrum. Conversely, a
nonzero abstract `lim^1` without an explicit source realization is only generic homological
algebra and does not clear either novelty or significance gate.

## Compactness firewall and the finite-observable corona

There is already a canonical compact inverse limit in the corpus: finite simplicial constraints
and finite Boolean orientations reconstruct uniquely as one global abstract constraint geometry
and one global sign sequence. More generally, every inverse system of nonempty compact Hausdorff
sewing spaces with continuous compatibility maps has a nonempty inverse limit. Therefore compact
finite-stage compatibility cannot be the obstruction sought here.

This yields an exact no-go quadrichotomy. If every finite sewing problem is soluble but no global
source sewing exists, then at least one of the following must occur:

1. the sewing spaces are noncompact;
2. the compatibility relation is not closed;
3. a transition is partial or discontinuous;
4. the relevant obstruction is killed by the compact/profinite completion and survives only in
   its kernel or corona.

The live corpus supplies one exact witness of each relevant shape:

- the Böttcher Prüfer monodromy subgroup is divisible and every finite quotient kills it, so its
  profinite image is trivial although the full monodromy is nontrivial;
- the actual Sonin prime-dilation boundary corner is noncompact and survives after compact effects
  are quotiented in the Calkin algebra;
- the Hedenmalm theta-source obstruction is a failure of closability, hence a nonclosed graph
  defect rather than a finite-dimensional kernel.

These statements do not yet identify one class, but they locate a common mathematical operation:
**quotient out every finitely observable or compactly removable effect and retain the class at
infinity**. Call the still-conjectural universal recipient the **finite-observable HT corona**.
Any proposed common object must map to the profinite-kernel, Calkin, and graph-closure defects and
must carry the same source class under all three maps. A list of separate corona analogies is not
enough.

## Tate-clock refinement `[EXACT SKELETON; SOURCE EXTENSION CONJECTURAL]`

The no-backward-clock theorem fixes the variance of the universal boundary. The HT jet tower is an
Ind-object: it is built only from forward finite observable extensions. Reflection and linear
duality supply the opposite Pro-object. The minimal self-dual completion is therefore an
elementary Tate object, not an ordinary inverse limit of fields.

At the universal linearized level over a field `K`, put

```text
I_K = direct_sum_(n>=0) K = K^(N),
P_K = product_(n>=0) K = K^N,
<a,p> = sum_n a_n p_n.                                    (2d)
```

The sum is finite. Let `S:I_K->I_K` be the forward clock shift and
`B:P_K->P_K` the backward shift. Then

```text
<S a,p> = <a,B p>,                                        (2e)

0 -> I_K --S--> I_K --eval_0--> K -> 0,                  (2f)
0 -> K --boundary_0--> P_K --B--> P_K -> 0.              (2g)
```

Thus the infinite clock and its continuous dual have one and the same rank-one boundary defect:
the cokernel of the forward shift is dual to the kernel of the backward shift. The self-dual
space `P_K + I_K`, with the skew evaluation form, is the algebraic Tate clock. This is the exact
linear meaning of infinite capacity concentrated on a thin boundary: infinitely many independent
clock slots, but one boundary line per tick.

Tate objects, Sato Grassmannians, lattice index, determinant torsors, and duality are parent
theory. The primary collision is explicit: generalized Tate spaces already package lattices,
dimension torsors, determinant gerbes, and self-duality. The candidate-new HT content can only be:

1. derive the Tate extension from the nonlinear HT clock boundary without choosing coordinates;
2. let the actual source constraint, not a zero divisor, select its self-dual lattice and affine
   origin;
3. prove that continuation, monodromy, Calkin orientation, and boundary-condition constructions
   are representations of that one source-selected Tate extension;
4. identify one determinant section before examining its degeneracy set.

This is strictly stronger than the earlier generic boundary-relation candidate. A boundary triple
starts with an operator and boundary space. The Tate program must construct both from the
one-way HT observable tower and the source constraint.

Primary parent anchors:

- Braunling--Groechenig--Wolfson, `Tate Objects in Exact Categories`,
  https://arxiv.org/abs/1402.4969;
- Previdi, `Sato Grassmannians for generalized Tate spaces`,
  https://arxiv.org/abs/1002.4863;
- Braunling--Groechenig--Heleodoro--Wolfson, `On the normally ordered tensor product and duality
  for Tate objects`, https://arxiv.org/abs/1709.07962.

## Refined conjecture

**[CONJECTURE]** A constrained HT function carries, at every finite clock cutoff, an **oriented
self-dual boundary complex**

```text
K_N : Q_N  --Theta_N-->  Q_N^dual,                         (3)
Q_N = P_(N+1)/P_N,
```

where:

1. `Q_N` is the linearized one-layer clock boundary;
2. `Theta_N` is induced by the external source constraint, not chosen from the zero set;
3. an anti-linear involution `kappa_N` implements reflection/self-duality;
4. a Hermitian orientation records signs and negative index invisible to the differential field;
5. a distinguished determinant/Fitting section is fixed by the source constraint.

The common obstruction is the cohomology or degeneracy module of `(3)`, not the field interval by
itself. Two analytic constructions represent the same obstruction only if they are connected by an
oriented self-dual quasi-isomorphism carrying the distinguished source section. Equality of scalar
determinants, zero sets, dimensions, or indices is insufficient.

## Proposed representation dictionary `[CONJECTURAL UNTIL MAPS ARE BUILT]`

| Analytic presentation | Boundary-complex presentation |
|---|---|
| spectral incompleteness | nonzero kernel or cokernel of `Theta_N` |
| continuation failure | nontrivial Cech/descent cohomology of the same complex |
| positivity failure | nonzero negative index of the induced Hermitian form on cohomology |
| monodromy | holonomy of the boundary local system underlying `K_N` |
| noncanonical boundary condition | torsor of Lagrangian splittings of the self-dual complex |

This table is a list of proof obligations, not evidence that the identifications already exist.

## Zeta specialization `[CONJECTURE, NOT AN RH RESULT]`

There should exist a source-defined pro-system `K_zeta` built from the prime and archimedean
constraints, without importing a zero table, such that:

1. its oriented determinant section is the completed zeta function up to a canonically nowhere-zero
   factor;
2. the involution induced by `s |-> 1-conj(s)` fixes the self-dual seam `Re(s)=1/2`;
3. the spectral, continuation, positivity, monodromy, and source-selected boundary-condition chains
   are oriented self-dual realizations of `K_zeta`;
4. the critical zeros are precisely the self-dual degeneracy spectrum of that source-defined
   object.

The research task is the cross-representation construction in item 3. Merely defining a complex
whose determinant is `xi`, or specializing an operator to the known zeros, is circular and fails the
conjecture.

## Live-corpus attacks

1. **Field/completion blindness.** The retired orientation-nondescend topology already proves that
   differential-field, finite-matroid, and compact-open fingerprints can be identical while the
   Krein index varies. Therefore Hermitian orientation is mandatory.
2. **Determinant-line blindness.** A trivial determinant line admits arbitrary sections and zero
   divisors. A distinguished source section is mandatory.
3. **Böttcher monodromy.** Unbounded one-coordinate monodromy gives a genuine algebraic-dependence
   obstruction, but no map to the zeta source boundary is currently known.
4. **Semilocal Jacobi boundary conditions.** Extension ambiguity is a rank-two boundary torsor and
   determinant factors vary with the extension. A source-selected Lagrangian splitting is mandatory.
5. **Prime--Mellin positivity.** The exact inverse-gap Dirichlet energy is nonnegative for arbitrary
   real nodes and is RH-blind. Positivity without source orientation is insufficient.
6. **Involutive clock energy.** The Kadison defect is a canonical positive boundary-crossing energy,
   but positivity is automatic and does not identify a degeneracy divisor.

The attacks agree on the required decorations but do not yet prove that the five chains arise from
one object.

## Strongest live realization candidate: the oriented cross-boundary operator

The corpus already identifies a less arbitrary operator model than a generic map `Theta_N`. Given
an oriented completion of the boundary quotient, let `P` project onto the internally observable
sector and let `U` realize a source constraint or continuation action. Define

```text
Delta = (1-P) U P.                                         (4)
```

Then the two-term boundary complex is the cross-sector map

```text
P H --Delta--> (1-P) H.                                   (5)
```

This has several exact, already formalized faces:

- `CutoffCochain.lean` treats `(4)` as the nonfake cutoff-crossing cochain and detects when it is
  transverse to a non-split Fitting seam;
- `TwoOutcomePinchingKadison.lean` identifies `Delta^* Delta` and its reverse block with the positive
  observability/Kadison defect;
- the Sonin logarithmic consumer identifies the same positive energy with clock--observable
  commutator energy for an involutive source symmetry.

Thus cutoff nonmembership and involutive positivity already share one exact cross-boundary
operator form. This is evidence for two representations, not yet for the user conjecture: no
source-defined realization map from the algebraic quotient `(2)` to `(5)` has been built, and the
Böttcher continuation and semilocal Jacobi extension rows have not been intertwined with the same
`Delta`.

The next map to construct is therefore not another determinant identity. It is an **oriented
boundary realization** carrying the algebraic clock symbol to `(1-P)UP`, with continuation and
boundary-condition changes acting by genuine intertwiners. Only then are kernel, index, holonomy,
and determinant degeneracies representations of one object rather than parallel analogies.

## First theorem targets

### A. Boundary-symbol exact sequence

Formalize `(2)` for a filtered differential field and specialize it to the HT tower, using the
existing exact clock-erosion theorem to identify the kernel before quotienting.

`[FORMALIZED CORE]` The generic quotient construction and injectivity theorem are now in
`HypertranscendentalClockBoundary.lean`:

```text
clockBoundarySubgroup
clockBoundaryRawSymbol
clockBoundarySymbol
clockBoundarySymbol_mk
clockBoundarySymbol_injective
```

Together with `hypertranscendental_clock_internal_iff`, these give the HT boundary exact sequence
without adding a costly specialization wrapper. The formal result also confirms the no-go: the
bare symbol is injective and therefore cannot itself supply the conjectured degeneracy spectrum.

### B. Constraint-induced boundary complex

For a constraint morphism preserving the clock filtration, construct its induced map on `Q_N` and
prove independence from representatives. Add self-duality and show that oriented conjugacies
preserve the degeneracy module and its Fitting support.

This is parent perfect-complex/determinant-line theory and will be marked `[BRIDGE]`. Its purpose is
to make the cross-chain conjecture falsifiable.

Before constructing this complex, the formal no-backward-clock theorem fixes its variance: the HT
jet tower supplies only forward field inclusions. The maps needed for `(3)` and `(2c)` must be
constructed after applying a source realization functor; they cannot be field retractions in
disguise.

### C. Three-chain factorization gate

Construct actual oriented boundary-complex maps for three incompatible rows:

1. Böttcher continuation/monodromy;
2. semilocal Jacobi extension ambiguity;
3. Sonin or Weil/Krein positivity.

The conjecture survives only if these maps land in one source-defined object and preserve the same
distinguished section. Sharing only the abstract shape `(3)` is not enough.

## Novelty boundary

Associated gradeds of filtered differential algebras, Galois connections, perfect complexes,
determinant lines, Fredholm/Lagrangian boundary data, Maslov indices, and Hermitian signatures are
parent theories. None is new here.

A targeted parent audit sharpens the collision. Boundary-triplet/Weyl-function theory already
packages self-adjoint extensions, their spectra and resolvents, boundary parameters, characteristic
functions, and Nevanlinna/Herglotz positivity in one boundary space. Krein--Langer and generalized
Schur--Nevanlinna realization theory already packages negative squares, Pontryagin-space
orientation, and unitary/passive colligations. Thus the generic claim that spectral degeneracy,
boundary conditions, positivity, and a characteristic determinant are representations of one
oriented boundary relation is `[BRIDGE]`, not new science.

Primary anchors:

- Derkach--Malamud, `Generalized resolvents and the boundary value problems for Hermitian operators
  with gaps`, *J. Functional Analysis* 95 (1991), and the authors' consolidated account
  https://arxiv.org/abs/1503.08956;
- Bruening--Geyler--Pankrashkin, `Spectra of self-adjoint extensions and applications to solvable
  Schroedinger operators`, https://arxiv.org/abs/math-ph/0611088;
- Lilleberg, `Generalized Schur--Nevanlinna functions and their realizations`,
  https://doi.org/10.1007/s00020-020-02600-w.

The positive residue is now exact: construct a canonical functor from the algebraic HT clock
boundary symbol `(2)` and the actual non-flow source constraint to a boundary relation/colligation,
including its Hermitian orientation and distinguished determinant section. Then prove that three
existing analytic chains factor through that **same source realization**. Parent boundary theory
starts after such a realization is supplied; it does not construct it from hypertranscendence.

## Gates

- [x] user conjecture isolated without asserting RH
- [x] bare adjunction interval killed by exact HT orbit
- [x] bare clock symbol shown intrinsically exact
- [x] field/completion-only topology no-go imported from the failed corpus
- [x] minimum orientation and source-section decorations identified
- [x] boundary-symbol exact sequence formalized in Lean
- [x] absence of every algebraic backward clock map formalized in Lean
- [x] generic boundary-relation/colligation package downgraded to a parent-theory bridge
- [x] finite-kernel carrier replaced by a falsifiable derived-boundary-at-infinity candidate
- [x] compact/profinite inverse-limit carrier killed by exact compactness
- [x] profinite-kernel, Calkin, and nonclosable-graph manifestations isolated
- [x] algebraic Tate-clock shift/coshift exact skeleton formalized
- [ ] nonlinear HT boundary functor to an elementary Tate object constructed
- [ ] actual source constraint shown to select a self-dual lattice and affine origin
- [ ] constraint-induced boundary complex constructed
- [ ] Böttcher factorization built
- [ ] semilocal boundary-condition factorization built
- [ ] positivity factorization built
- [ ] one common distinguished source section proved
- [ ] primary-literature audit across derived, Fredholm, differential, and observability theories
- [ ] independent specialist novelty verdict

## Log

- 2026-07-15 -- Followed the common-interval conjecture. Exact HT adjunction killed the bare
  counit interval; quotienting by the internal core produced an injective boundary symbol but no
  spectrum. Refined the candidate to an oriented self-dual constraint complex with a distinguished
  source section and stated a three-chain falsification gate.
- 2026-07-15 -- Formalized the generic additive boundary quotient, its clock symbol, and injectivity
  from exact core identification. One targeted cached module build and one direct touched-file check
  passed; no full or concurrent build was run.
- 2026-07-15 -- Boundary-triplet, Weyl-function, and Krein--Langer realization theory absorbed the
  generic oriented-operator unification. Retained the stronger positive residue: a canonical
  source-derived realization functor from the HT algebraic boundary, plus three concrete
  factorization maps preserving one distinguished section.
- 2026-07-15 -- Proved and formalized that a transcendental clock step admits no algebra homomorphism
  back to its base. Combined with finite boundary exactness, this moved the conjectural common
  object from a finite kernel to a source-selected derived closure defect at the infinite clock
  boundary. No `lim^1` novelty is claimed without concrete source transition maps.
- 2026-07-15 -- Killed the compact profinite carrier using inverse-limit compactness and the
  already-formalized canonical constraint--orientation limit. Located three exact escape modes in
  the corpus: profinite-invisible Prüfer monodromy, a noncompact Sonin Calkin class, and a
  nonclosable Hedenmalm graph. Refined the source realization target to a self-dual Tate extension
  of the one-way HT clock and isolated its rank-one shift/coshift boundary skeleton.
- 2026-07-15 -- Formalized the algebraic Tate-clock skeleton in
  `HypertranscendentalClockBoundary.lean`: the forward Finsupp shift has exactly evaluation-at-zero
  cokernel, the dual product backshift has exactly the boundary-line kernel, both outer maps are
  surjective/injective as required, and the restricted evaluation pairing makes the shifts
  adjoint. A direct touched-file Lean check passed using the existing cache; no build was run.
