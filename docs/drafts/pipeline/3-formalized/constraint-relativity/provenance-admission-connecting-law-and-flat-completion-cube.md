# Provenance-admission connecting law and flat completion cube

- **ID:** `provenance-admission-connecting-law-flat-completion-cube`
- **Stage:** 3-formalized
- **Type:** THEOREM / FRAMED PROVENANCE GEOMETRY / RELATIVE EXACTNESS
- **Scientific status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`
  `[PAPER-PROVED] [NOT RH]`
- **Novelty status:** mapping-cone and Boolean-cube ingredients are classical. Candidate-new role
  is foundational: obstruction is exact in formal completion but nonexact in source-admitted
  cochains; absolute representation geometry is flat while provenance admission carries class.
- **Parent:**
  `../../1-in-progress/constraint-relativity/constraint-relativity-and-relation-completion-spacetime.md`.

## 1. Purpose

Many corpus obstructions share a precise shape:

1. an algebraic/regular/completed ambient object contains a primitive or filler;
2. the primitive is not admitted by source provenance, boundedness, domain, or cofinal topology;
3. every downstream scalar sees only a shadow of this failure.

This card proves the universal algebra behind that pattern. It replaces vague “incompatibility”
with a complete obstruction group and shows why higher curvature cannot arise from formally
available completion insertions alone.

## 2. Formal completion insertion is a flat cube

Let `P_0,...,P_n` be posets. For `1<=i<=n`, let `T_i:P_(i-1)->P_i` be monotone. For
`1<=i<=n`, let `c_i:P_i->P_i` be a closure operator: monotone, inflationary, and idempotent. Fix
`x in P_0`.

For a subset `S subset {1,...,n-1}`, define

\[
 x_S
 =c_nT_n c_{n-1}^{\epsilon_{n-1}}T_{n-1}
 \cdots c_1^{\epsilon_1}T_1x,
 \tag{2.1}
\]

where `epsilon_i=1` for `i in S`, `epsilon_i=0` otherwise, and `c_i^0=I`.

### Theorem 2.1 — closure-insertion cube

The assignment

\[
 S\longmapsto x_S
 \tag{2.2}
\]

is monotone from the Boolean lattice `B_(n-1)` to the closed part of `P_n`. Thus every formal
choice of intermediate completion is a vertex of one coherent `(n-1)`-cube.

#### Proof

It suffices to insert one missing index `i`. At the `i`-th stage,

\[
 y\le c_i y
\]

by inflationarity. All later transports and closures are monotone, so the final output without
that insertion is at most the output with it. Repeating proves monotonicity for every
`S subset S'`. The final `c_n` makes every output closed. QED.

### Proposition 2.2 — exact additive Bianchi law

Let `U(P_n)` be the free abelian group on the elements of `P_n`, and define

\[
 J(a,b)=e_b-e_a
 \qquad(a\le b).
 \tag{2.3}
\]

For distinct `i,j notin S`, the square face obeys

\[
\begin{aligned}
 &J(x_S,x_{S\cup\{i\}})
 +J(x_{S\cup\{i\}},x_{S\cup\{i,j\}})\\
 &\qquad=
 J(x_S,x_{S\cup\{j\}})
 +J(x_{S\cup\{j\}},x_{S\cup\{i,j\}}).
\end{aligned}
 \tag{2.4}
\]

More generally, the sum along every monotone path from `emptyset` to the full subset is

\[
 e_{x_{\mathrm{full}}}-e_{x_\varnothing}.
 \tag{2.5}
\]

#### Proof

Both sides of `(2.4)` telescope to
`e_(x_(S union {i,j}))-e_(x_S)`. Repeated telescoping proves `(2.5)`. QED.

### Consequence

The abstract Boolean cube is contractible. Therefore insertion of formal completion operators
cannot by itself create higher holonomy. Any nontrivial loop/filler obstruction must come from a
restriction on which vertices, edges, homotopies, or primitives are source-admissible. Ordinary
laxity supplies comparison cells; curvature begins only when provenance refuses some cells.

## 3. Nested formal and source-admitted complexes

Let

\[
 0\longrightarrow S^\bullet
 \xrightarrow{\iota}R^\bullet
 \xrightarrow{q}Q^\bullet
 \longrightarrow0
 \tag{3.1}
\]

be a short exact sequence of cochain complexes over a ring. Interpret:

- `R`: formal, regular, or completed cochains;
- `S`: source-provenant/admitted cochains;
- `Q=R/S`: primitive escape beyond admission.

Define the **admission-curvature group**

\[
 \mathcal E^k(R,S)
 =\frac{dR^{k-1}\cap S^k}{dS^{k-1}}.
 \tag{3.2}
\]

An element is formally exact, source-admitted in degree `k`, but considered modulo classes with a
source-admitted primitive.

### Theorem 3.1 — complete primitive-escape classification

There are canonical isomorphisms

\[
 \boxed{
 \mathcal E^k(R,S)
 \cong
 \ker\bigl(H^k(S)\to H^k(R)\bigr)
 \cong
 \operatorname{im}\bigl(
 \delta:H^{k-1}(Q)\to H^k(S)
 \bigr).}
 \tag{3.3}
\]

More explicitly, if `ell in R^(k-1)` and

\[
 \omega=d\ell\in S^k,
 \tag{3.4}
\]

then `bar ell=q(ell)` is closed in `Q`, and

\[
 \boxed{\delta[\bar\ell]=[\omega].}
 \tag{3.5}
\]

The following are equivalent:

1. `omega` has a source-admitted primitive `s in S^(k-1)`;
2. its class in `mathcal E^k(R,S)` is zero;
3. `[omega]=0` in `H^k(S)`;
4. `[bar ell]` lies in the image of `H^(k-1)(R)->H^(k-1)(Q)`.

If `H^(k-1)(R)=0`, these are also equivalent to `[bar ell]=0` in `H^(k-1)(Q)`.

#### Proof

Every element of `dR^(k-1) cap S^k` is closed because `d^2=0`, so it determines a class in
`H^k(S)`. Its image in `H^k(R)` vanishes by formal exactness. The kernel of the map
`H^k(S)->H^k(R)` consists conversely of source cocycles which become boundaries in `R`. Quotienting
by `dS^(k-1)` proves the first isomorphism in `(3.3)`.

The long exact cohomology sequence of `(3.1)` identifies this kernel with image of the connecting
map, proving the second isomorphism. For `(3.4)`,

\[
 d\bar\ell=q(d\ell)=q(\omega)=0,
\]

and definition of the connecting homomorphism gives `(3.5)`.

Conditions 1--3 restate vanishing modulo `dS^(k-1)`. Exactness of the long cohomology sequence
makes condition 3 equivalent to 4. If `H^(k-1)(R)=0`, the preceding image is zero. QED.

### Interpretation: exactness--admission uncertainty

A nonzero element of `mathcal E^k(R,S)` is a complete, not metaphorical, incompatibility witness:

\[
 \text{formal primitive exists}
 \quad\text{but}
 \quad\text{no source-admitted primitive exists}.
 \tag{3.6}
\]

There is no universal numerical uncertainty product. The oriented connecting class is the
primitive invariant. Scalar sizes require observer states and cannot be canonical by the scalar
no-go theorem.

## 4. Smallest algebraic countermodel

Let `k` be a field. Define two-term complexes

\[
 S^0=0,
 \qquad S^1=k,
 \qquad d_S=0,
\]

and

\[
 R^0=k,
 \qquad R^1=k,
 \qquad d_R=I.
\]

Embed `S` into `R` by the zero map in degree zero and identity in degree one. Then every
`omega in k= S^1` is exact in `R`; only zero is exact in `S`. Hence

\[
 \mathcal E^1(R,S)\cong k.
 \tag{4.1}
\]

The completed/formal theory has trivial `H^1`; the admitted theory has `H^1=k`. Thus absolute
cohomology after completion can be zero while the entire source obstruction survives.

## 5. Singular analytic countermodel

Let

\[
 S^0=\ell^1,
 \qquad S^1=\ell^2,
 \qquad d_S:\ell^1\hookrightarrow\ell^2,
\]

and

\[
 R^0=\ell^2,
 \qquad R^1=\ell^2,
 \qquad d_R=I.
\]

The natural inclusions make `S` a subcomplex of `R`. Take

\[
 \omega=(1/n)_{n\ge1}\in\ell^2\setminus\ell^1.
\]

Then `omega=d_R omega` has a formal `ell^2` primitive but no `ell^1` source primitive. Therefore
it gives a nonzero class in

\[
 \mathcal E^1(R,S)=\ell^2/\ell^1.
 \tag{5.1}
\]

Because `ell^1` is dense and nonclosed in `ell^2`, the topological quotient is non-Hausdorff.
This is the elementary model of a singular admission horizon: completion kills ordinary
cohomology while the provenance restriction records primitive escape.

## 6. Corpus consequences

### RH horizontal class

The current arithmetic model describes an ordinary-exact horizontal cochain whose primitive
escapes the permitted source bornology. Its restricted class

\[
 [D\ell_\rho]\longmapsto1-2\operatorname{Re}\rho
\]

has exactly the type `(3.2)`. Ordinary `H^2=0` and `C^3=0` are compatible with a nonzero admission
class; they do not prove a degree-three associator.

This changes the field-level question. Do not construct more formal completion faces. Construct
the source-admitted primitive, or prove a source law placing the formal primitive inside the
admitted complex.

### Hypertranscendence

Finite jet languages can agree while their inverse-limit relation complexes differ. The theorem
predicts that a useful HT invariant should be a pro-version of `mathcal E^k(R,S)` measuring
failure of compatible finite primitives to define one admitted tail primitive. This is not yet
proved for the corpus HT towers.

### Holography and recurrence

Boundary algebras and resource filtrations define admitted subtheories; joint completion defines a
larger formal theory. Calling the quotient a wormhole is forbidden unless its connecting class is
proved equal to an independently defined recoverability, proto-area, or wormhole-length
observable. Recurrence concerns dynamics of observer pairings, not the bare connecting class.

## 7. Failed universal conjecture and strict survivor

### Failed: every obstruction is admission curvature

This is false. The following countermodels have no missing primitive:

1. a zero-differential complex with a noninjective bounded observer has regular blindness;
2. the map `t -> t^2` loses orientation with full domain and no exactness issue;
3. a smooth compacting sequence can lose norm separation without any cochain differential;
4. HT nonstabilization concerns prolongation of a pro-system, not one primitive;
5. two isogenous copies of one detector repeat a radical without changing admission;
6. pairwise source experiments can lack one synchronized subnet even when every individual
   complex is exact.

Thus `(3.2)` classifies only formal-exact/source-nonexact primitive escape.

### Source-framed strict fracture conjecture

There is a source-canonical quasi-abelian diagram of arithmetic, spectral, and geometric
admission complexes over one formal complex, with a distinguished primitive, whose total
homotopy cofiber carries a pointed class

\[
 \kappa_{ASG}.
 \tag{7.1}
\]

It should vanish exactly when one strict source-synchronized filler exists, retain ordinary-prime
labels, multiplicity, reflection orientation, and critical bornology, and map conservatively to
the known horizontal class. This is live only if the actual three admission functors are
constructed before divisor specialization.

Fatal falsifiers:

1. class depends on chosen completion or ambient primitive;
2. Hausdorff reduction kills it while claimed realizations remain nonzero;
3. it reduces to ordinary mapping-cone cohomology without a new source functor;
4. route realizations forget prime coefficients, grade, or orientation;
5. source annihilation is equivalent to RH by definition.

## 8. Novelty boundary

Short exact sequences, mapping cones, connecting homomorphisms, closure cubes, and relative
cohomology are classical. Novelty cannot be claimed for Theorems 2.1 or 3.1 alone. Candidate new
field content would require:

1. a source-framed higher category whose intrinsic curvature is `(7.1)`;
2. a classification covering the heterogeneous RH and HT obstruction census;
3. a canonical source current and nontrivial field equation;
4. an independent arithmetic and physical realization of one connecting class;
5. new predictions not used to define admission.

The internal corpus already contains thin-boundary relative cohomology, pointed/unpointed
relative no-gos, strict quasi-abelian mapping-cone formulations, and source/observer comparison
curvature. Therefore even the abstract synthesis is not new to this project. Only an actual
source-canonical strict diagram and coefficient-faithful realization can advance the frontier.

## 9. Lean handoff notes

Formalized in
`formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ProvenanceAdmissionCube.lean`
(wired into `GaloisForLFunctions.HTGeometry`).  Theorem 2.1, Proposition 2.2, Theorem 3.1 and both
countermodels are green and unconditional; the declaration-by-equation map and the axiom audit are
in the companion card
`provenance-admission-connecting-law-and-flat-completion-cube-formalized.md`.  The bornological,
pro-, corpus and physical realizations remain separate future interfaces, and the source-framed
strict fracture conjecture `(7.1)` is untouched.
