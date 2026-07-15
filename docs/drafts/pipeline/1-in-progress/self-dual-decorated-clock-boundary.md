# Self-dual decorated clock boundary as the common obstruction object

- **ID:** `self-dual-decorated-clock-boundary`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT CONJECTURE / CROSS-REPRESENTATION OBSTRUCTION THEORY
- **Scientific status:** `[CONJECTURE] [TWO BARE-INTERVAL NO-GOS PROVED] [GENERIC OPERATOR PACKAGE IS A BRIDGE] [COMMON SOURCE REALIZATION OPEN]`
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
- [x] generic boundary-relation/colligation package downgraded to a parent-theory bridge
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
