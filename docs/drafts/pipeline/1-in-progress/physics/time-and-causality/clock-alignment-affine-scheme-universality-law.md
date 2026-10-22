# The clock-alignment law for hypertranscendence geometry

- **ID:** `clock-alignment-affine-scheme-universality-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL HT LAW / ESSENTIAL-IMAGE CLASSIFICATION / AFFINE-SCHEME REALIZATION
- **Scientific status:** `[AUTONOMOUS PHASE LEAN-PROVEN] [TRANSVERSE POLYNOMIAL-ALGEBRA PHASE LEAN-PROVEN FOR POLYNOMIAL LAW ALGEBRAS] [ARBITRARY-ALGEBRA DIFFERENTIAL-FIELD LIFT IN PROGRESS] [NOVELTY PROVISIONAL]`
- **Paper target:** a replacement master narrative for
  `analytic-grassmann-lattice-dirichlet-fields`

## 1. The universal law

The geometry of complete ordinary differential dependence is controlled not by commutativity
alone, but by the position of the differentiation clock relative to the structural law algebra.

### Aligned autonomous phase

Let `K` be a characteristic-zero field, let `A` be a commutative `K`-algebra represented linearly
on a state space `M`, choose a root `m`, and let `L : V -> A` be a linear law pencil.  In direction
`v`, use the same selected action both as the law and as the clock:

```text
J_v(m) = (m, L(v)m, L(v)^2m, ...).
```

Then the complete dependence horizon

```text
H(m) = {v : J_v(m) is algebraically dependent over K}
```

is a vector subspace of `V`.  Conversely every vector subspace occurs as such a horizon, using
the regular action of `Sym(V/H)` on the root `1`.  Therefore

```text
essential image of aligned commutative one-root horizons
  = all vector subspaces.                                      (A)
```

This phase is already unconditional in
`CommutativeRepresentationHorizon.lean` and
`CommutativeHorizonExactClassification.lean`.

### Transverse-clock phase

Let `A` now be an arbitrary commutative `K`-algebra and `I` an arbitrary ideal.  Put

```text
Q_I = A/I,
S_I = direct-sum_(n>=0) Q_I.
```

Let `T` shift the layer index, let `e_n[a]` denote the class `[a]` in layer `n`, and form the
symmetric observable domain `B_I=Sym_K(S_I)` and its fraction field `L_I`.  The shift induces a
derivation `partial` of `B_I` and then of `L_I`.  For every structural law `a in A`, define the
single-root structural observable

```text
x_a = iota(e_0[a]) in L_I.
```

Then

```text
partial^n x_a = iota(e_n[a]).                                  (B1)
```

Consequently, for every family `(a_j)_(j in J)`,

```text
{partial^n x_(a_j) : n>=0, j in J} is algebraically independent
  iff
{[a_j] : j in J} is K-linearly independent in A/I.              (B2)
```

In particular,

```text
x_a is hypertranscendental over K  iff  a notin I,               (B3)

{a : x_a is differentially algebraic over K} = I.               (B4)
```

Thus every proper affine constraint scheme, including every nonreduced scheme and every scheme
with embedded components, is the exact complete-jet constraint scheme of a single root in a
differential field.  The complete differential matroid is not merely supported on `Spec(A/I)`:
it is exactly the linear matroid of `A/I`, so nilpotent and embedded information is retained.
Equivalently,

```text
essential image of transverse-clock one-root constraint schemes
  = all affine schemes.                                         (B)
```

Equations `(A)` and `(B)` form the **clock-alignment law**.  Moving one fixed clock from the law
direction to a transverse axis enlarges the essential image from linear subspaces to arbitrary
affine schemes.  This is the proposed master theorem.

## 2. Why this is one theorem rather than a collection

Both phases use the same data: a commutative law algebra, a cyclic root state, a symmetric
observable algebra, and complete ordinary jets.  The sole structural change is the clock:

- aligned: the selected law element is iterated;
- transverse: a fixed shift is iterated after the law class has selected an observable.

The theorem identifies this clock placement as the exact control parameter for the realizable
geometry.  The Grassmann, prime-clock, and constraint-spectrum results become consequences or
natural sectors of this one dichotomy rather than independent layers.

## 3. Source-faithful arithmetic sector

The prime-profile carrier is a natural, non-universal transverse sector.  Its logarithmic prime
clock acts on the source quotient, and differential adjunction is exactly the least invariant
clock saturation.  The represented fields form a complete embedded Grassmann lattice: arbitrary
joins and nonempty meets of source subspaces are preserved.  Relative differential algebraicity
is polynomial-clock torsion in the saturated quotient.

Thus the arithmetic theorem is the source-selected restriction of `(B)`:

```text
synthetic transverse clock: every affine constraint scheme is possible;
prime transverse clock: only clock-saturated source geometry is possible. (C)
```

This makes the arithmetic source marking, not bare hypertranscendence, the selecting structure.

## 4. Proof

For `(A)`, the root annihilator in `A` is an ideal.  Modulo that annihilator, dependence of the
power orbit of `L(v)` is equivalent to algebraicity of its quotient class over `K`.  In a
commutative algebra the algebraic elements form a `K`-subalgebra, so their inverse image under
`L` is a vector subspace.  For the converse, in `Sym(V/H)` the degree-one class of a nonzero
quotient vector is transcendental, whereas the class of a vector in `H` is zero.

For `(B1)`, the symmetric-algebra derivation induced by `T` sends the linear observable of a state
to the linear observable of its shifted state.  Induction gives the displayed jet formula, and
the quotient-rule extension gives the same formula in `L_I`.

For `(B2)`, the layers are a direct sum.  Hence the states `(e_n[a_j])_(n,j)` are linearly
independent exactly when the quotient classes `([a_j])_j` are linearly independent.  The canonical
linear embedding of a vector space in its symmetric algebra converts linear independence into
algebraic independence.  The injection into the fraction field preserves and reflects algebraic
independence.  Statements `(B3)` and `(B4)` are the singleton and annihilator cases.  If `I` is
proper, the root `x_1` is hypertranscendental.

No radical is taken anywhere.  The exact equality `(B4)`, not equality of zero loci, is why the
scheme structure survives.

## 5. Counterexample attacks and scope locks

1. **No conflict with the aligned theorem.**  In `(B)`, `a` selects the order-zero observable and
   the fixed shift `T` supplies its jet.  The law does not iterate itself.
2. **Not a characteristic-variety theorem.**  `Spec(A/I)` is the exact structural DA
   annihilator scheme, not the characteristic variety of a coherent D-module; classical
   involutivity constraints on characteristic varieties do not apply.
3. **The root is genuinely single.**  All `x_a` come from the orbit of one cyclic source class;
   the countable layers are clock states, not separately chosen roots.
4. **The field lift is necessary.**  The symmetric algebra is a domain, and the final theorem must
   place the root in its fraction field with the quotient-rule derivation.  A polynomial-algebra
   statement alone is not advertised as a theorem about HT field elements.
5. **No analytic-function claim.**  The unconditional theorem constructs an abstract rational
   differential field.  Entire or meromorphic realization is a separate analytic question and is
   not imported into the paper unless independently completed.
6. **No finite-dimensionality claim.**  Universal scheme capacity uses countably many clock
   layers.  Minimal finite-state capacity is a different invariant.
7. **No RH conclusion.**  The theorem is a structural selection law and route filter, not a
   zero-location theorem.

## 6. Novelty and parent gate

Established parents not claimed as novelty:

- cyclic modules and `Ann_A(1 mod I)=I`;
- symmetric algebras and derivations induced by linear endomorphisms;
- support and rank varieties of modules, including realization theorems for reduced
  cohomological support varieties;
- characteristic varieties of D-modules and their involutivity/coisotropy constraints;
- parameterized difference and differential Galois theory;
- the finite-character and invariant-subspace arguments behind the Grassmann lattice sector.

The candidate-new result is the exact conjunction at complete-jet level:

1. an essential-image classification of aligned commutative one-root HT horizons;
2. an essential-image classification of transverse-clock one-root HT constraint **schemes**;
3. preservation of the full ideal and the full family differential matroid, not only a reduced
   support variety;
4. the identification of clock alignment as the phase variable separating linear rigidity from
   affine-scheme universality.

Searches through July 2026 located realization results for cohomological support varieties over
complete intersections and finite tensor categories, rank varieties for finite group schemes,
D-module characteristic varieties, and parameterized Galois criteria for particular functions.
They did not locate a theorem realizing every affine scheme, scheme-theoretically, as an exact
complete-jet DA annihilator of one root together with the quotient matroid, nor the aligned versus
transverse essential-image dichotomy.  This is an absence-of-hit result, not a priority
certificate; an independent specialist audit remains required.

## 7. Scientific significance

The theorem says that bare HT constraint geometry has universal affine-scheme capacity, while
autonomous commutative directional HT has exact linear rigidity.  This changes the selection
question for natural special functions.  A natural function is not distinguished by possessing a
complicated finite constraint scheme: every such scheme can be synthesized.  It must be
distinguished by the way a canonical source chooses the clock, the carrier, and the additional
analytic structure on that scheme.

For physics-inspired search, the algebraic picture is a coherent structural register coupled to a
separate shift clock.  Alignment locks the register into a linear phase; transversality permits
arbitrary constraint architecture.  This is only a source of mathematical conjectures: no quantum
system, state, positivity, locality, or energy interpretation is asserted by the theorem.

## 8. RH pressure test

Any RH route that depends only on a finite affine DA constraint scheme of a zeta carrier is
nonselective: the same scheme can occur in a synthetic one-root HT field.  A viable route must
therefore supply and use a source-canonical selection datum beyond the bare scheme.  In the
present corpus the available candidates are:

- the Euler prime-valuation source marking;
- its logarithmic clock saturation and complete embedded field lattice;
- archimedean completion and reflection;
- positivity or a polarized Hilbert-space realization;
- an analytic growth/effectivity condition that excludes the universal synthetic carrier.

The positive statement is: **an RH-capable HT carrier must be rigidified by a canonical
source-clock-polarization structure whose essential image is strictly smaller than the universal
transverse scheme class.**

## 9. Formalization route

1. [DONE] aligned commutative horizon is always a subspace;
2. [DONE] every subspace has an explicit aligned realization;
3. [DONE for polynomial law algebras in the symmetric observable domain] arbitrary ideal exactness
   and full family matroid;
4. [IN PROGRESS] generalize the transverse theorem from `K[X_i]` to an arbitrary commutative
   `K`-algebra `A`;
5. [IN PROGRESS] extend the clock derivation and all observables to the fraction field;
6. [TODO] prove the field-level singleton, family-matroid, exact-annihilator, and proper-root
   theorems;
7. [TODO] package `(A)` and `(B)` in one clock-alignment capstone;
8. [TODO] exact leaf checks, one final targeted module audit, and axiom audit;
9. [TODO] rewrite and render the paper around the verified theorem.

