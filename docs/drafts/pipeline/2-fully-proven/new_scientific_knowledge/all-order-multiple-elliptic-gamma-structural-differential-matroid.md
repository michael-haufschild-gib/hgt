# Every multiple-elliptic-gamma structural orbit has its Stanley--Reisner differential matroid

- **ID:** `all-order-multiple-elliptic-gamma-structural-differential-matroid`
- **Stage:** 2-fully-proven / adversarial paper audit passed / unconditional Lean proof open
- **Type:** THEOREM (paper) / ALL-ORDER FACE-FILTRATION CLASSIFICATION
- **Date:** 2026-07-10
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` -- the all-order paper proof and its
  generic order-one elliptic-gamma atomic parent survived a separate adversarial audit. The result
  is not final under the project standard until the complete analytic and differential-Galois
  argument is formalized unconditionally in Lean. The abstract replication, summability, and
  simplicial-gluing lemmas are `[BRIDGE]` components. The candidate scientific content is the
  all-order conclusion that the known squarefree hierarchy ideal generates every nonlinear
  differential dependence among every finite structural family.
- **Parents:**
  `elliptic-gamma-rank-three-da-spectrum`;
  `multiple-elliptic-gamma-transverse-constraint-depth`;
  `order-three-elliptic-gamma-bottom-face-joint-atomicity`;
  `order-three-elliptic-gamma-full-structural-differential-matroid`
- **Statement:** For every generic order `r>=1`, the complete differential-algebraic matroid of the
  structural translation orbit of `Psi_r` is the linear matroid of the localized
  Stanley--Reisner ring of the `(r-2)`-skeleton. Equivalently, nonlinear differential polynomials
  create no dependence beyond the squarefree degree-`r` face ideal.

## Main theorem

Let

```text
F_r=Psi_r(z;tau_0,...,tau_r),
S=C[delta],
R_r=S[t_0^(+-1),...,t_r^(+-1)],
x_i=t_i-1,
I_r=(product_(i in J)x_i : |J|=r).
```

Assume

```text
1,tau_0,...,tau_r
```

are linearly independent over `Q`. For arbitrary `P_1,...,P_m in R_r`, let `Pbar_j` be their
classes in `R_r/I_r`. Then

```text
dtrdeg_(C(z)) C(z)<P_1(T)F_r,...,P_m(T)F_r>_delta
  =dim_(C(delta)) span{Pbar_1,...,Pbar_m}                 (1)
```

inside

```text
C(delta) tensor_(C[delta]) (R_r/I_r).                     (2)
```

Consequently:

1. the full differential-operator annihilator of `F_r` modulo DA functions is `I_r`;
2. a finite structural family is differentially dependent exactly when its operator classes are
   linearly dependent over `C(delta)` modulo `I_r`;
3. every dependence is already witnessed by a constant-coefficient differential-linear relation
   after clearing denominators;
4. no additional nonlinear differential relation exists.

The theorem for `r=1` is immediate from the generic elliptic-gamma theorem: structural translates
differ by DA functions and the remaining common coordinate is hypertranscendental. The proof below
assumes `r>=2`.

## The face coordinates

Put

```text
V={0,...,r},
n=|V|=r+1.
```

For `J subset V`, define

```text
x_J=product_(j in J)x_j,
F_J=x_JF_r,
O_J={T_J^aF_J:a in Z^J}.                                 (3)
```

Here `T_J^a=product_(j in J)T_j^(a_j)`. The hierarchy gives

```text
F_J=Psi_(r-|J|)(z;tau_i:i notin J)                       (4)
```

up to a DA normalization. The proper non-DA face coordinates are exactly those with

```text
0<=|J|<=r-1=n-2.                                         (5)
```

For `q notin J`, commutativity gives the exact face relation

```text
(T_q-1)T_J^aF_J=T_J^aF_(J union {q}).                    (6)
```

When `|J|=n-2`, the right side of (6) is an order-zero theta logarithmic derivative and is DA.

Let `D` be the differential field of all `1`-periodic DA meromorphic functions. It is stable under
all translations and is differential algebraic over `C(z)`. We shall prove that the union

```text
{F_empty} union union_(1<=|J|<=n-2)O_J                   (7)
```

is differentially algebraically independent over `D`.

## Free-block replication `[PROVED IN THE ORDER-THREE PARENT]`

We use the following lemma repeatedly. Let `sigma` commute with the derivation, let `K/k` have
finite differential transcendence degree, and assume every `sigma^m(K)` is DA over `K`. Let `B` be
a finite family admitting arbitrarily many pairwise disjoint `sigma`-translated copies whose union
is differentially independent over `k`. Then `B` remains differentially independent over `K`.

Indeed, if `|B|=s` and `d=dtrdeg_kK`, a dependence in each of `M` disjoint translated blocks gives
the upper bound

```text
d+M(s-1),
```

while their independence gives the lower bound `Ms`. Taking `M>d` is impossible.

This lemma uses differential transcendence only as a finite obstruction budget. It does not
linearize the hypothetical relation.

## Uniform simplicial-star orbit gluing `[PROVED HERE]`

Let `W` be a finite vertex set with commuting differential automorphisms `(sigma_q)_(q in W)`. Fix
an integer `s>=1`. For every `s`-subset `J` in a chosen `s`-uniform hypergraph, let `O_J` be a
family satisfying:

1. `O_J` is differentially algebraically independent over a differential field `k`;
2. for `q in J`, every finite block in `O_J` has arbitrarily many disjoint `sigma_q`-translates
   inside `O_J`;
3. for `q notin J` and `Y in O_J`, every `sigma_q^m(Y)-Y` is DA over `k`.

Then

```text
union_J O_J                                                (8)
```

is differentially algebraically independent over `k`.

### Nested-star proof

For `A subset W`, `|A|<=s`, define

```text
Star(A)=union_(J superset A, |J|=s)O_J.                   (9)
```

We prove by descending induction on `|A|` that every `Star(A)` is independent. If `|A|=s`, at most
one hyperedge contains `A`, so this is assumption 1.

Suppose the result is known for stars with `|A|+1` fixed vertices and that `Star(A)` contains a
finite minimal differential circuit `C`. Choose an edge `J` represented in `C` and a vertex

```text
q in J\A.
```

Partition

```text
B=C intersect Star(A union {q}),
C_0=C\B.                                                  (10)
```

The block `B` is nonempty. Minimality makes `C_0` independent, and therefore makes `B` dependent
over

```text
K=k<C_0>_delta.                                           (11)
```

Every hyperedge represented in `C_0` contains `A` but avoids `q`. Assumption 3 implies

```text
sigma_q^m(K) is DA over K for every m in Z.               (12)
```

By the induction hypothesis, `Star(A union {q})` is independent. Hence arbitrarily many separated
`sigma_q`-translates of `B` are disjoint and jointly independent over `k`. Free-block replication
contradicts dependence over (11). Thus `Star(A)` has no circuit.

Taking `A=empty` proves (8). `QED`

For `s=2` this is the graph-star theorem used at order three. The proof shows that the order-four
three-uniform hypergraph is not a new obstruction: one descends through a double star and then a
triple star until only one atomic orbit remains.

## Bottom layer: all order-one faces are jointly atomic `[PROVED HERE]`

The bottom non-DA faces have

```text
|J|=n-2,
F_J=Psi_1(z;tau_a,tau_b),  {a,b}=V\J.                    (13)
```

Their external translation subgroup is generated by `(tau_j)_(j in J)`. Rational independence of
`1,tau_0,...,tau_r` makes distinct exponent vectors in `Z^J` distinct modulo the DA spectrum

```text
Z+Z tau_a+Z tau_b.
```

The order-one atomic theorem and its full-orbit consequence therefore make every `O_J`
differentially independent over `C(z)`, hence over the DA extension `D`.

If `q notin J`, then `q` is one of the two structural parameters of this order-one face. Equation
(6) is DA. Thus the bottom families satisfy the simplicial-star hypotheses over `D`, with
`s=n-2`. It follows that

```text
union_(|J|=n-2)O_J                                       (14)
```

is jointly differentially algebraically independent over `D`.

This is the all-order form of the six-face order-three theorem.

## Free-shift one-slice nonsummability `[PROVED IN THE ORDER-THREE PARENT]`

Let `K_0` be a difference-differential field and let

```text
{X_(alpha,m):alpha in A,m in Z}
```

be differential indeterminates with

```text
sigma(X_(alpha,m))=X_(alpha,m+1).
```

In the differential-rational field generated by these variables, no nonzero finite form

```text
sum_alpha L_alpha(delta)X_(alpha,0),  L_alpha in C[delta], (15)
```

is a `sigma`-coboundary.

The proof has three exact steps. An `X`-dependent denominator would have a pole in an infinite
irreducible shift orbit and hence an uncancelled boundary pole. Thus a rational primitive must be
polynomial in the jets. Its nonlinear top degree would be a finite shift-invariant polynomial,
which cannot exist. A finite linear primitive has two occupied boundary slices, whereas (15) has
only one. This is the free-variable specialization of the classical discrete-residue obstruction
to rational summability.

## Descending face-lifting lemma `[PROVED HERE]`

Fix

```text
0<=s<=n-3                                                   (16)
```

and assume all deeper face coordinates

```text
O_L,  s+1<=|L|<=n-2                                      (17)
```

are jointly independent over `D`. Put

```text
K_(s+1)=D<union_(s+1<=|L|<=n-2)O_L>_delta.               (18)
```

Then, for every `J subset V` with `|J|=s`, the orbit `O_J` is differentially algebraically
independent over `K_(s+1)`.

### Stability of the deeper field

The field `K_(s+1)` is stable under every `T_q`. If `q in L`, translation shifts an orbit
coordinate inside `O_L`. If `q notin L`, equation (6) changes that coordinate by a member of
`O_(L union {q})`, or by a DA function when `|L|=n-2`.

### Simultaneous primitive equations

Fix a finite block

```text
Y_a=T_J^aF_J,  a in A subset Z^J.                         (19)
```

Choose distinct `q,u in V\J`; this is possible because (16) gives `|V\J|>=3`. Equation (6)
gives two compatible primitive systems over `K_(s+1)`:

```text
(T_q-1)Y_a=T_J^aF_(J union {q}),
(T_u-1)Y_a=T_J^aF_(J union {u}).                          (20)
```

All functions involved are `1`-periodic. A meromorphic function fixed by `T_q` and `T_u` has the
three periods `1,tau_q,tau_u`. Their group is nondiscrete, so the common fixed field in the
extension generated by (19) is exactly `C`.

Suppose the block (19) is differentially dependent over `K_(s+1)`. The simultaneous telescoping
lemma proved in the order-one parent supplies operators

```text
L_a in C[delta], not all zero,
```

and one `G in K_(s+1)` with

```text
(T_q-1)G=sum_(a in A)L_a(delta)T_J^aF_(J union {q}).      (21)
```

### The deeper field is free in the target face orbit

Let `K_0` be generated by `D` and all families in (17) except `O_(J union {q})`. It is
`T_q`-stable. Indeed, for another deeper face `L`:

- if `q in L`, `T_q` shifts inside `O_L`;
- if `q notin L`, its difference belongs to `O_(L union {q})` or `D`;
- equality `L union {q}=J union {q}` would force `L=J`, impossible because `|L|>|J|`.

The assumed joint independence of the deeper layer identifies

```text
K_(s+1)=K_0<O_(J union {q})>_delta                       (22)
```

as a free differential-rational extension. Under `T_q`, the `q`-exponent of this orbit shifts by
one, while the exponents in `J` label independent transverse coordinates.

The right side of (21) is a nonzero constant-coefficient differential-linear form supported on the
single `q`-slice with exponent zero. Free-shift one-slice nonsummability contradicts (21). Hence
every finite block (19) is independent over `K_(s+1)`. `QED`

The case `s=0` is included: `O_empty={F_r}`. Thus the same argument proves that the top primitive is
independent from every proper face, without a separate long-interval argument.

## Completing one face layer `[PROVED HERE]`

Continue under the hypotheses of the face-lifting lemma, now with `s>=1`. Each `s`-face orbit
`O_J` is independent over `K_(s+1)`. For `q notin J`, equation (6) lies inside `K_(s+1)`, so

```text
T_q^m(Y)-Y in K_(s+1) for every Y in O_J,m in Z.          (23)
```

Apply uniform simplicial-star gluing over the base field `K_(s+1)` to the `s`-uniform family
`(O_J)_(|J|=s)`. It gives joint independence of the entire `s`-layer over the deeper field.

Therefore

```text
K_s=D<union_(s<=|L|<=n-2)O_L>_delta                      (24)
```

is a free differential-rational extension of `D` and is stable under every structural
translation.

Starting from the bottom layer (14) and descending through

```text
s=n-3,n-4,...,1,0
```

proves differential independence of the full coordinate family (7). This closes the analytic
face-filtration induction in every order. `QED`

## Adversarial check: the first order-four hypergraph

At order four, `V` has five vertices. The ten bottom faces are indexed by three-subsets. A naive
sequential induction fails because a late hyperedge need not contain a direction absent from every
earlier hyperedge.

The nested-star proof does not require such an ordering. Given a minimal circuit, choose a vertex
`q` of one represented triple. The `q`-star moves while its complement is DA-stationary. Inside
that star, choose a second vertex `u`; the `{q,u}`-double star moves while the rest of the `q`-star
is `T_u`-stationary. The double star reduces to individual triple orbits after one more fixed
vertex. Each replication is over a finite differential-transcendence coefficient field, so no
cycle survives. Thus the first apparent hypergraph obstruction is genuinely closed by the general
proof, rather than assumed away.

## Stanley--Reisner module decomposition

Each Laurent factor has the direct decomposition

```text
S[t_i^(+-1)]=S direct_sum x_iS[t_i^(+-1)].
```

Tensoring over all vertices and quotienting by the degree-`r=n-1` squarefree ideal gives

```text
R_r/I_r
 =direct_sum_(J subset V, |J|<=n-2)
    x_JS[t_j^(+-1):j in J].                               (25)
```

The decomposition is unique. Acting on `F_r`, its coordinate indexed by `J` is

```text
Q_J(delta,T_J)F_J,                                       (26)
```

modulo DA hierarchy normalizations. These are constant-coefficient differential-linear forms in
the independent family (7).

For any finite operator family `P_1,...,P_m`, only finitely many coordinates occur. The coefficient
matrix of (26) has rank equal to the rank of `Pbar_1,...,Pbar_m` in (2). Smith normal form over the
PID `C[delta]` shows that the differential transcendence degree of constant-coefficient
differential-linear forms in differential indeterminates equals the matrix rank over `C(delta)`.
This proves (1). `QED`

## Multiplicative all-order theorem `[PROVED HERE]`

For `E_j in Z[t_0^(+-1),...,t_r^(+-1)]`, let `G_(r,E_j)` be the finite integer product of
structural translates of the order-`r` multiple elliptic gamma function prescribed by `E_j`. Then

```text
dtrdeg(G_(r,E_1),...,G_(r,E_m))
  =dim_C span{Ebar_1,...,Ebar_m}                           (27)
```

in

```text
C[t_0^(+-1),...,t_r^(+-1)]/I_r.
```

The lower bound follows because the logarithmic derivatives are `E_j(T)F_r` and (1) computes their
rank. The integral version of (25) is torsion-free. Choose a rational basis among the integral
classes and clear denominators in every remaining relation. The associated integer product has DA
logarithmic derivative, hence is DA by differential-algebraic transitivity. Each remaining product
is algebraic over the differential field generated by the basis products and DA functions, giving
the matching upper bound.

## Structural consequences

### Exact face-circuit geometry

For structural translates `T^(a_1)F_r,...,T^(a_m)F_r`, their exact differential transcendence
degree is the linear rank of the Laurent monomials `t^(a_j)` in `R_r/I_r`. Thus the circuits are
precisely the linear circuits of the localized Stanley--Reisner skeleton.

Every `r`-dimensional structural cube has `2^r` vertices and one alternating DA face relation, so
its differential transcendence degree is `2^r-1`. The theorem proves that no nonlinear relation
lowers it further.

### No emergent nonlinear dependence at higher depth

The hierarchy acquires arbitrarily many face layers as `r` grows. Nevertheless no new nonlinear
dependence appears at any intermediate depth. Each layer is a simultaneous primitive extension of
the next one, and its only possible collapse would be a one-slice rational coboundary. The free
orbit residue excludes exactly that collapse.

### Constraint, not flow

The quotient `R_r/I_r` is not a state space propagated from lower order. It is the compatibility
module of all proper faces. The function is fixed, modulo DA terms, by occupying one free
differential coordinate for every face monomial that survives the squarefree constraint.

## Attacks and boundaries

1. **Atomic parent.** The entire special-function theorem depends on the generic order-one atomic
   theorem. Failure there demotes this card; the abstract face-filtration theorem remains
   conditional infrastructure.
2. **Dependent periods.** Rational relations identify orbit coordinates, enlarge common fixed
   fields, and can create additional circuits. Formula (1) is not asserted in that regime.
3. **Structural translations only.** The theorem concerns the Laurent group generated by the
   hierarchy parameters. Arbitrary complex translations require the larger universal face-signature
   modules and are not classified here.
4. **Meromorphic category.** The common-constant and pole-orbit arguments use meromorphic functions
   on `C`. Essential-singularity distributions or formal solutions require a separate constants
   theorem.
5. **Nonconstant differential coefficients.** The module uses `C[delta]`. Allowing DA function
   coefficients changes the summability problem and is not covered.
6. **Order zero.** Theta functions are the DA boundary of the hierarchy and do not fit the
   hypertranscendental formula as an `r=0` case.

## Parent-theory and literature audit

The proof deliberately separates established mechanisms from the candidate theorem.

- Free-block replication is elementary differential-transcendence bookkeeping.
- The one-slice obstruction is the free-variable form of Abramov/Chen--Singer discrete rational
  summability and modern orbital residues.
- Simultaneous nonlinear-to-linear telescoping comes from several-automorphism parameterized
  Picard--Vessiot theory and Cassidy's additive differential algebraic groups.
- Smith normal form supplies the final differential-linear rank formula.

Hardouin's diagonal difference systems compute differential independence for derivatives of
solutions to a fixed diagonal system. Ogawara treats triangular classical Vigneras multiple gamma
functions under one common shift. Adamczewski--Dreyfus--Hardouin--Wibmer compare solutions attached
to two independent operator classes and obtain algebraic independence. These are strong parents
for individual moves, but no located theorem treats a simplicial hierarchy of commuting additive
primitive systems whose coefficient field is recursively generated by all deeper faces.

Nishizawa and Narukawa establish the multiple-elliptic-gamma hierarchy, modular identities, and
integral formulas. Winding treats cone variants. Kato proves DA for rational period tuples and
states that the generic non-rational DA/HT question is unknown. The 2025--2026 geometric-family
papers study cocycles, modular symbols, and arithmetic applications.

Exact, equivalent, stronger, and mechanism searches through 2026 located no result computing
`R_r/I_r` as a nonlinear differential matroid, no all-order differential transcendence-degree
formula for structural translates or products, and no theorem that the squarefree face ideal
generates every nonlinear differential relation in the hierarchy.

The parent mechanisms are known; their face-filtration synthesis and the special-function
classification were not located. Scientific novelty is therefore provisionally positive,
conditional on independent audit of the proof, priority boundary, and order-one atomic parent.

## Adversarial validity audit `[PAPER PROOF PASSED; NOT FINAL]`

The audit attacked every implication capable of invalidating the all-order induction.

1. **One simultaneous telescoper.** Hardouin--Singer Appendix 6.2 permits several commuting
   automorphisms. Apply it to the compatible unipotent system for `T_q` and `T_u`. Differential
   dependence makes the parameterized Galois group a proper differential algebraic subgroup of
   `G_a^A`; Cassidy's additive-group theorem supplies one homogeneous differential-linear form.
   The multi-automorphism fixed-field theorem then puts that same form at one element `G` of the
   base field. It does not produce unrelated primitives for the two translations. Extension from
   `C` to a differential closure preserves the joint fixed field, and descent is a finite
   polynomial system after a nonzero coefficient is normalized. No derivative of an unknown
   coefficient occurs in the simultaneous coboundary equations.
2. **Joint constants.** Every field in the descent consists of `1`-periodic meromorphic functions.
   Joint invariance under two distinct structural translations gives the nondiscrete period group
   generated by `1,tau_q,tau_u`, hence only constants.
3. **Target isolation.** After removing `O_(J union {q})`, the remaining deeper field is
   `T_q`-stable. If a different deeper face `L` avoiding `q` satisfied
   `L union {q}=J union {q}`, deleting `q` would give `L=J`, contradicting `|L|>|J|`.
4. **One-slice obstruction.** Joint differential independence of the deeper layer makes the target
   orbit a genuine differential-rational free shift over the remaining field. The right side of
   (21) is nonzero and occupies one `q`-slice, so the denominator-orbit, top-degree, and two-boundary
   argument excludes a rational `T_q`-primitive.
5. **Hypergraph gluing.** The nested-star induction does not assume a sequential ordering of
   hyperedges. A minimal circuit is split into a moving star block and a finite-transcendence
   coefficient block; free-block replication contradicts dependence. The order-four triple-face
   case is therefore covered rather than extrapolated.
6. **Rank passage.** Evaluation at `t_i=1` gives
   `S[t_i^(+-1)]=S direct_sum x_iS[t_i^(+-1)]`. Tensoring and deleting supports containing a
   degree-`r` squarefree generator yields (25). Finite coefficient matrices then have differential
   transcendence degree equal to their rank over `C(delta)`; integer clearing gives the
   multiplicative upper bound.
7. **Atomic parent.** The order-one proof was rechecked through joint-constant collapse, the
   injectivity of `E_tau tensor_C E_sigma` for noncommensurable lattices, specialization to one
   elliptic factor, and the nonzero highest principal part on an isolated translation orbit. The
   same vector argument proves the full defect-coset matroid used at the bottom layer.

No paper-level counterexample or missing implication was found. This establishes a positive paper
audit, not the final theorem: every item above must still be represented in Lean without axioms or
placeholder hypotheses.

## Stronger structural boundary

The simplex skeleton is not essential. The same induction works for any finite
downward-closed face complex in which every nonmaximal face has two distinct immediate coface
directions, provided maximal-face orbits are atomic and the same joint-constant and one-slice
hypotheses hold. Purity is unnecessary: first glue all maximal faces by nested-star induction on
their inclusion antichain, then descend through nonmaximal faces by cardinality. A useful intrinsic
sufficient condition for two-thickness is that the maximal faces form a pure ridge-thick complex: every
codimension-one face lies in at least two maximal faces. Lower-codimension faces obtain two
directions inside one maximal face, while ridges obtain them from the two incident maximal faces.

The resulting operator module is the localized Stanley--Reisner ring of that complex, not merely
the `(r-2)`-skeleton of a simplex. This generalization is recorded separately as
`simplicial-constraint-tower-stanley-reisner-matroid`. Its pure/ridge-thick implication and the
nonpure maximal-antichain termination step are already unconditional Lean theorems in
`GaloisForLFunctions.SimplicialConstraintTower`.

## Significance gate

The theorem resolves, in the generic regime, the nonlinear differential dependence problem for an
infinite hierarchy of named hypertranscendental functions. It advances beyond individual HT, exact
translation spectra, and linear annihilator ideals to the complete differential transcendence
degree of every finite additive and multiplicative structural family. It also supplies a reusable
constraint-side mechanism: recursively free face fields are certified by one-slice obstructions,
not generated by a hidden flow.

## Unconditional Lean status

The final proof is open. The current Lean contribution proves the first generalized combinatorial
input, not a surrogate for the special-function theorem:

```text
exists_two_coface_directions_of_pure_ridgeThick
ridgeThick_uniformFacets
twoThick_of_pure_ridgeThick
exists_fresh_vertex_of_facetAntichain_star_nontrivial
```

The remaining formal dependency chain is substantive:

1. differential polynomial rings, differential algebraicity, differential independence, and
   differential transcendence degree for differential fields; the field-relative jet-family
   definition and its first preservation theorems now exist in
   `GaloisForLFunctions.DifferentialIndependence`.  Its new
   `differentialJet_algebraMap_apply` bridge makes coefficient-ring jet transport explicit, and
   the base-gauge invariance theorem is now a specialization of the stronger jets-in-base law;
2. several-automorphism parameterized Picard--Vessiot rings and the additive simultaneous
   telescoping theorem, including constant extension and descent; the commuting
   difference-differential field interface, differential-operator commutation, cocycle
   compatibility, and common-primitive consequence are now proved in
   `GaloisForLFunctions.DifferenceDifferential`, while the converse existence theorem remains;
3. meromorphic periodicity, nondiscrete-period constant collapse, elliptic curves, elliptic
   function fields, tensor-product injectivity, and specialization; continuous constancy under a
   dense additive period subgroup and differentiable constancy under arbitrarily small nonzero
   periods and meromorphic-normal-form constancy under those periods are now proved in
   `GaloisForLFunctions.PeriodRigidity`. A rank-three subgroup of `C` need only be nondiscrete.
   `GaloisForLFunctions.RankThreePeriods` proves nondiscreteness from three `Q`-linearly independent
   periods, constructs small nonzero periods, and proves normal-form meromorphic constancy. The
   remaining analytic step is to package the actual meromorphic fixed field in normal form;
4. theta logarithmic derivatives, elliptic gamma, the multiple-elliptic-gamma hierarchy, and their
   exact functional equations;
5. elliptic principal parts and the non-torsion orbit-residue obstruction;
6. free differential-shift nonsummability, nested-star gluing, and the Stanley--Reisner
   decomposition; the generic dependent operator-row rank theorem is now formalized in
   `DifferentialOperatorMatroid.lean`;
7. the concrete all-order capstone with its additive and multiplicative corollaries.

The abstract gluing engine of item 6 — free-block replication and the simplicial-star orbit gluing
over an arbitrary incidence predicate — is now formalized axiom-clean in
`GaloisForLFunctions.DifferentialMatroidGluing`: `Rank.freeBlock`,
`Rank.crossNeutral_iUnion_indep`, `Rank.graphGluing`, and
`Rank.uniformFace_nestedStar_indep`. The last theorem performs the descending nested-star recursion
for an arbitrary uniform face family. `MatroidNatRank.matroidRank` and
`DifferentialMatroidRank.differentialRank` now discharge the rank abstraction: its `IndepSet`
predicate is exactly differential independence in the genuine differential matroid. Differential
automorphisms now preserve that rank automatically, and `CrossNeutral` follows from translated-
packet closure inclusion. `Rank.hasFreeTranslates_of_intHeight` obtains free translates from the
integer orbit-height law. `DifferentialOperatorMatroid.lean` identifies every finite family of
polynomial differential-operator outputs with its ordinary localized row matroid, including the
rank of dependent packets. `LocalizedStanleyReisnerMatroidRank.lean` then proves that complete
facet coordinates, common Laurent-denominator clearing, and finite coordinate expansion preserve
the entire subset matroid, and gives the explicit localized row-span dimension for every dependent
packet. What remains is the concrete special-function proof of star independence, the orbit-height
realization, and the off-star packetwise DA statements, followed by the concrete hierarchy-to-row
identification and the all-order capstone.

The theorem must not move to Stage 3 until this chain terminates in the concrete statement (1),
the formal lint passes, and `#print axioms` reports only Lean's standard logical axioms.

## Gates

- [x] free-block replication lemma available
- [x] uniform simplicial-star orbit gluing proved
- [x] all bottom order-one face orbits proved jointly atomic
- [x] descending face-lifting lemma proved
- [x] every intermediate layer proved jointly independent over all deeper layers
- [x] top primitive proved independent from every proper face
- [x] exact all-order additive structural matroid proved
- [x] exact all-order multiplicative structural matroid proved
- [x] order-four hypergraph obstruction attacked and closed
- [x] exact/stronger/equivalent literature gate completed provisionally through 2026
- [x] adversarial paper-proof audit of every all-order implication
- [x] primary-source audit of the several-automorphism simultaneous telescoper
- [x] adversarial paper audit of the generic order-one atomic parent
- [x] arbitrary finite two-thick generalization isolated; pure ridge-thick sufficiency and nonpure
  maximal-antichain termination formalized in Lean
- [ ] independent proof audit
- [ ] independent specialist priority audit
- [ ] full unconditional Lean formalization of the concrete theorem
- [x] arbitrary-translation universal face-matroid extension proved in
  `all-depth-compatible-pair-face-differential-matroid`

## Log

- 2026-07-10 -- Generalized graph-star replication to nested stars in every uniform hypergraph.
- 2026-07-10 -- Proved that the bottom order-one faces are jointly atomic in every hierarchy order.
- 2026-07-10 -- Proved the descending face-lifting lemma by simultaneous telescoping and one-slice
  nonsummability.
- 2026-07-10 -- Closed every intermediate face layer, the top primitive, and the all-order additive
  and multiplicative Stanley--Reisner differential matroids.
- 2026-07-11 -- Strengthened the structural Laurent-orbit theorem to the full arbitrary-complex-
  translation differential matroid in `all-depth-compatible-pair-face-differential-matroid`.
  The universal module splits over full-lattice cosets into Stanley--Reisner blocks, and the
  arbitrary-label face-lifting proof makes all blocks jointly free.

## Lean progress — the bottom layer `(13)`--`(14)` over the differentially algebraic extension

`formal/GaloisForLFunctions/HTGeometry/EllipticGammaAtomicOverDAExtension.lean` (axiom-clean,
umbrella registered).

The bottom-layer section of this card asserts: *"The order-one atomic theorem and its full-orbit
consequence therefore make every `O_J` differentially independent over `C(z)`, hence over the DA
extension `D`."*  Both steps are now Lean theorems.

- **`differentialIndependent_differentialAdjoin_of_rationalBase`** — differential independence over
  the embedded rational coordinate field survives adjunction of *any* set of germs differentially
  algebraic over the constants.  This is the "hence over `D`" step, and it is unconditional: it
  combines `differentialIndependent_meromorphicRationalCoordinateField_iff` (proved in
  `EllipticCompositumMatroidTransport`) with the corpus's arbitrary base-change law
  `DifferentialIndependent.extendScalarsDifferentialAdjoin`.
- **`ellipticGammaExternalDefectFamily_differentialIndependent_daExtension`** — hence every
  separated order-one external-defect packet is differentially independent over every such
  extension `D`.  The `C(z)` input is the already formalized
  `ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase`.
- **`ellipticGammaExternalDefectFamily_differentialIndependent_ellipticCompositum'`** — the
  concrete instance for a paired elliptic compositum as the extension.

The prerequisite that made this unconditional is the elliptic-field bridge proved for the rank-three
card: every element of a paired elliptic compositum — indeed every doubly periodic meromorphic germ —
is differentially algebraic over the constants, with no Weierstrass generation theorem.

Note on the dependency chain above: items 3 and 4 of the "Unconditional Lean status" list are stale.
The rank-three fixed-field packaging exists (`rankThree_generator_jointFixed_iff_constant`,
`exists_complex_of_ellipticMeroField_translation_fixed`), and the all-order hierarchy itself is built
(`FinitePiProductSummability`, `MultipleEllipticGammaLogKernel`, `MeromorphicMultipleEllipticGamma`,
`MultipleEllipticGammaFieldHierarchy`, `MultipleEllipticGammaAdditiveHierarchy`).  What genuinely
remains is the concrete discharge of the four simplicial-star hypotheses of
`Rank.uniformFace_nestedStar_indep` for the multiple elliptic-gamma packets — atomicity (now
available at the bottom layer), the rank-automorphism property, free translates via the integer
orbit-height law, and cross-neutrality off the star — followed by the hierarchy-to-row
identification and the capstone.

## Lean progress — the orbit-height realization, abstract and for the actual translations

`formal/GaloisForLFunctions/HTGeometry/OrbitHeightFreeTranslates.lean` (axiom-clean, umbrella
registered) discharges the second of the four simplicial-star hypotheses of
`Rank.uniformFace_nestedStar_indep` — free translates — down to a single concrete input.

- `orbitUnion sigma base` — the union of the full `sigma`-orbits of a base set;
- **`hasFreeTranslates_orbitUnion`** — an orbit union whose exponent is *recoverable* (distinct
  exponents give distinct elements) has free translates.  The `ZZ`-valued height required by
  `Rank.hasFreeTranslates_of_intHeight` is constructed from the parametrization itself: the
  exponent is well defined by injectivity, extended by `0` off the packet;
- **`hasFreeTranslates_orbit_of_aperiodic`** — the single-orbit criterion: it is enough that no
  nonzero power of the direction fixes the base point;
- `meroTranslationPerm q`, `meroTranslationPerm_zpow_apply` — the actual additive translation of the
  global meromorphic field as a permutation, with `sigma_q^n = sigma_(n q)` for every integer `n`;
- **`hasFreeTranslates_meroOrbit_of_aperiodic`** — hence, for a genuine meromorphic germ `x` and a
  shift `q`, the whole translation orbit of `x` has free translates as soon as
  `sigma_(n q) x != x` for every nonzero integer `n`.

So the "orbit-height realization" listed as remaining is now reduced to *aperiodicity of the
structural translate*, which for the elliptic-gamma packets is exactly nonresonance of the shift —
already available in the exact-spectrum theorems.  What remains of the four hypotheses is the
concrete packet definition for the higher faces (with its atomicity, the bottom layer being done),
the rank-automorphism property, and cross-neutrality off the star.

## Lean progress — the all-order gluing theorem in genuine differential form

`formal/GaloisForLFunctions/HTGeometry/DifferentialUniformFaceGluing.lean` (axiom-clean, umbrella
registered).  The corpus already carried the order-three six-face gluing theorem specialized to the
genuine differential matroid (`differentialRank_orderThree_sixFace_diffIndepOn`).  This file does the
same at **all orders**, so the abstract engine no longer stands between the card and its concrete
inputs.

- **`differentialRank_uniformFace_nestedStar_diffIndepOn`** — for a uniform face family, a total
  star is jointly differentially independent over `F` provided: each face packet is differentially
  independent (atomicity), each star direction is stable with an integer height increasing by `n`
  under `sigma^n`, and every off-star translated finite packet is differentially algebraic over the
  packet it came from.  The three abstract hypotheses of `Rank.uniformFace_nestedStar_indep` are
  discharged internally: rank-automorphism by
  `HTGeometry.DifferentialAlgEquiv.mem_differentialRank_rankAutSubgroup`, free translates by
  `Rank.hasFreeTranslates_of_intHeight`, cross-neutrality by
  `differentialRank_crossNeutral_of_image_differentialAlgebraic`.
- **`differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit`** — the same conclusion with the
  height replaced by an orbit presentation of each star: each star is the union of full orbits of a
  base set on which distinct exponents give distinct elements.  This is the form the structural
  translates of the hierarchy take, via `orbitUnion` and `hasFreeTranslates_orbitUnion`.

Remaining for the capstone: the concrete packets `O_J` of the multiple elliptic-gamma faces with
their atomicity at every layer (the bottom layer `|J| = n-2` is done), the orbit presentation of each
star (reduced to nonresonance by `hasFreeTranslates_meroOrbit_of_aperiodic`), the off-star DA
statements, and then the hierarchy-to-row identification.

### Concrete packet plan (next step, recorded)

The corpus's face coordinate is `multipleEllipticGammaLogDerivFaceMero tau htau J`, indexed by the
**deleted** set `J` (so its surviving parameters are the complement), with the intrinsic coface
equation `multipleEllipticGammaLogDerivFaceMero_addTranslation_sub`: translating by `tau q` for
`q notin J` and subtracting deletes exactly `q`.  Matching the card's convention, the external
translation subgroup of the face `J` is generated by `(tau_j)_(j in J)`, so the packet is

```text
O_J = { sigma_g (F_J) : g in Z-span{ tau_j : j in J } },  F_J = multipleEllipticGammaLogDerivFaceMero tau htau J.
```

With that definition the two orbit hypotheses of
`differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit` become:

1. `faceStar faces O (insert q A) = orbitUnion (meroTranslationPerm (tau q)) base`, where `base` is
   the union over `J` containing `insert q A` of the sub-orbits with vanishing `q`-exponent.  This
   is bookkeeping: each `O_J` with `q in J` is a union of full `sigma_(tau q)`-orbits, and a union of
   orbit unions is the orbit union of the union of the bases (`orbitUnion_union`; the indexed
   version is the only missing piece of pure bookkeeping).
2. `hStarInj`: distinct `tau_q`-exponents give distinct germs — exactly nonresonance of `tau_q`
   against the DA spectrum of the face, which is where the special-function input enters.

## Lean progress — the concrete face packets, and all-order star independence

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaFacePacket.lean` (axiom-clean, umbrella
registered) carries out the packet plan recorded above.

- `faceShiftLattice tau J` — the integer span of the parameters **deleted** by the face `J`, i.e.
  its external translation subgroup, and `faceShiftLatticeSlice tau J q` its zero-exponent slice in
  a deleted direction, with the splitting lemma `exists_slice_of_mem_faceShiftLattice`;
- `multipleEllipticGammaFacePacket tau htau J` — the packet `O_J`, the face coordinate
  `multipleEllipticGammaLogDerivFaceMero tau htau J` translated by that lattice;
- **`multipleEllipticGammaFacePacket_eq_orbitUnion`** — for every deleted direction `q in J` the
  packet is the union of the *full* `sigma_(tau q)`-orbits of its zero-exponent slice;
- **`faceStar_eq_orbitUnion`** — hence the entire star of a direction is an orbit union (every face
  of that star contains the direction; the union of orbit unions is the orbit union of the union of
  slices, `orbitUnion_biUnion`);
- **`multipleEllipticGammaFaceStar_diffIndepOn`** — the concrete all-order star-independence
  statement: with these packets and the genuine additive translations as directions, the total star
  is jointly differentially independent over the constants provided three analytic inputs hold —
  each face packet is atomic, distinct exponents in a star direction give distinct germs
  (nonresonance), and off-star translated packets are differentially algebraic over the packet they
  came from.

Both orbit hypotheses of `differentialRank_uniformFace_nestedStar_diffIndepOn_of_orbit` are now
discharged by construction; the abstract engine, the rank-automorphism property, the free-translate
mechanism, and the packet bookkeeping are all behind us.  What remains of `(14)` is exactly the three
named analytic inputs — of which atomicity is already available at the bottom layer `|J| = n-2` — and
after that the hierarchy-to-row identification and the capstone `(1)`.

## Lean progress — the one-direction telescope of a face coordinate

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaTelescope.lean` (axiom-clean, umbrella
registered).  Iterating the intrinsic coface equation gives the algebraic shape that the free-shift
nonsummability and orbit-height arguments consume.

- **`multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum`** — for `q notin J` and every `k`,

  ```text
  sigma_(k tau_q) F_J - F_J = sum_(j<k) sigma_(j tau_q) F_(J cup {q}).
  ```

  So the total displacement of a face coordinate under `k` structural translations is exactly the
  telescoped sum of translates of the *next* face.
- **`sum_translate_eq_zero_of_periodic`** — hence `k`-fold periodicity of `F_J` in the direction
  `tau_q` forces that telescoped sum to vanish, and **`not_periodic_of_sum_translate_ne_zero`** is
  the criterion form: nonvanishing of the sum excludes the periodicity.  This is precisely the
  single-face case of the `hStarInj` hypothesis of `multipleEllipticGammaFaceStar_diffIndepOn`.
- **`not_periodic_one_of_next_face_ne_zero`** — the first instance needs nothing but nonvanishing of
  the next face: one translation displaces `F_J` by exactly `F_(J cup {q})`.

The remaining analytic content of `hStarInj` is therefore isolated as a nonvanishing statement about
telescoped sums of lower-face translates — the free-shift one-slice nonsummability of the card's
order-three parent, at all orders.

### Status correction: the nonsummability half is already formalized

The card lists "free-shift one-slice nonsummability" as `[PROVED IN THE ORDER-THREE PARENT]` and the
dependency chain treats it as pending.  It is in fact already unconditional in the corpus:

- `FreeShiftOneSliceNonsummability.lean` — `freeShiftOneSlice_ne_coboundary`: on a free bilateral
  shift grid, no nonzero finite constant-coefficient linear form supported on one slice is a shift
  coboundary (finite periodic collapse, no residue calculus);
- `DifferentialIndependentOneSliceNonsummability.lean` —
  `differentialIndependent_oneSlice_ne_coboundary`: the same obstruction transported to the
  differential field generated by *any* genuinely differentially independent bilateral palette
  `x : alpha x Z -> K`.

That is exactly the shape the face-lifting lemma consumes, and it dovetails with the packet
structure built above: a packet is an orbit union, so its natural bilateral parametrization
`x (a, m) = sigma^m (base a)` is precisely such a palette.  The next assembly is therefore the
descending face-lifting lemma: take the lower-face palette (differentially independent by the layer
below), apply `multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum` to turn a putative
higher-face relation into a one-slice coboundary, and conclude by
`differentialIndependent_oneSlice_ne_coboundary`.

## Lean progress — the one-slice obstruction now applies to the actual translations

`formal/GaloisForLFunctions/HTGeometry/FreeShiftTransport.lean` (axiom-clean, umbrella registered).

The corpus's one-slice nonsummability theorem is stated for the *canonical* unit translation
`differentialIndependentFreeShiftEquiv` of the field generated by a differentially independent
bilateral palette.  In the elliptic-gamma application the shift is a genuine ambient differential
automorphism — an additive translation of the meromorphic field.  This file identifies the two, so
the obstruction is usable as stated:

- **`differentialIndependentFreeShiftEquiv_coe_eq`** — if an ambient differential automorphism
  `Psi` moves the palette one slice (`Psi (x (a, m)) = x (a, m+1)`), then on the generated field it
  *is* the canonical palette shift.  Both are `C`-algebra maps commuting with the derivation, and
  they agree on the generating jets (`DifferentialAlgEquiv.map_differentialJet`), so an
  `IntermediateField.adjoin` induction closes it.
- **`oneSlice_ne_coboundary_of_ambient_shift`** — hence no nonzero finite constant-coefficient
  linear form in the jets of one slice is a coboundary for the ambient automorphism.

This was the missing connector: the one-slice obstruction had no users in the corpus because it was
phrased for the abstract shift.  It is now in the form the descending face-lifting lemma needs — the
face packets are orbit unions, so their bilateral parametrisation `x (a, m) = sigma^m (base a)`
satisfies the hypothesis of the identification by construction.

## Lean progress — the face packet as a bilateral palette

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaFacePalette.lean` (axiom-clean, umbrella
registered) closes the gap between the packet construction and the nonsummability obstruction.

- `facePalette tau htau J q` — the bilateral palette `x (a, m) = sigma_(m tau_q) a` of the packet of
  the deleted face `J` in the deleted direction `q`, indexed by the zero-exponent slice and by `Z`;
- **`facePalette_shift`** — the genuine additive translation by `tau q` moves the palette exactly one
  slice, which is the hypothesis of the transport identification;
- **`range_facePalette`** — the palette enumerates the packet (immediate from
  `multipleEllipticGammaFacePacket_eq_orbitUnion`);
- **`facePacket_oneSlice_ne_coboundary`** — hence, as soon as the palette is differentially
  independent over the constants, no nonzero finite constant-coefficient linear form in the jets of
  its zero slice is a coboundary **for the actual translation**.

Together with the telescope `multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum`, this is
the complete machinery of the descending face-lifting step: a putative differential relation among
the higher-face packet is telescoped into a one-slice form, and the obstruction above forbids it.
What is still needed to run the induction is the identification of the telescoped displacement with
a one-slice jet form of the lower-face palette — i.e. the concrete hierarchy-to-row dictionary.

## Lean progress — coface behaviour of the packets (the primitive systems `(20)`)

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaPacketCoface.lean` (axiom-clean, umbrella
registered) formalizes the "stability of the deeper field" step of the descending face-lifting lemma.

- `faceShiftLattice_mono` — the external lattice grows with the deleted face;
- **`facePacket_translate_mem`** — a *deleted* direction `q in J` moves the packet `O_J` inside
  itself;
- **`facePacket_translate_sub_mem`** — a *surviving* direction `q notin J` changes a packet element
  by an element of the next packet `O_(J cup {q})`;
- **`facePacket_coface`** — explicitly, on a translated block,
  `(T_q - 1)(T^g F_J) = T^g F_(J cup {q})`, which is the primitive system `(20)` of the card.

Both statements follow from the intrinsic coface equation together with commutativity of the
translations.  With the palette and the transported one-slice obstruction of the previous entry, the
face-lifting step now has all of its structural inputs; what remains is the simultaneous-telescoping
argument itself, whose two ingredients are the corpus's automorphism-family Ostrowski criterion and
the rank-three fixed-field theorem `rankThree_generator_jointFixed_iff_constant`.

### Face-lifting assembly plan (recorded)

The face-lifting lemma is an instantiation of the corpus's noncommutative-family criterion
`automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping`
(`AutomorphismFamilyOstrowski.lean`) with

- `L = meroField univ`, `C = C`, and `K = K_(s+1)` the deeper field `(18)`;
- index set `I = {1, tau_q, tau_u}` — **three** directions, not two: `hfixed` needs the joint fixed
  field to be `C`, which is the corpus's `rankThree_generator_jointFixed_iff_constant` for the
  `Q`-independent triple `1, tau_q, tau_u`;
- `x` the block `(19)`, and `b i k` the displacement, supplied by `facePacket_coface`:
  `(T_q - 1)(T^g F_J) = T^g F_(J cup {q})`, which lies in `K_(s+1)` by
  `facePacket_translate_sub_mem`;
- `hnot` — the simultaneous-telescoping exclusion, which is where
  `facePacket_oneSlice_ne_coboundary` enters.

Two concrete prerequisites are visible and not yet in the corpus: translation stability of `K_(s+1)`
as a differential subfield (its ingredients are `facePacket_translate_mem` and
`facePacket_translate_sub_mem`), and `1`-periodicity of the multiple elliptic-gamma face
coordinates, i.e. `sigma_1 F_J = F_J` — true because the kernel is built from the `1`-periodic
exponential coordinate, but not yet stated for `multipleEllipticGammaLogDerivMero`.

## Lean progress — the unit period of the whole hierarchy

`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaUnitPeriod.lean` (axiom-clean, umbrella
registered) supplies the first of the two prerequisites recorded above.

Every factor of the all-order products depends on the point only through the exponential coordinate
`exp(2 pi i z)`, and `multipleEllipticGammaCoordinate_add_one` says that coordinate is unchanged by
`z -> z + 1`.  Hence:

- `multipleEllipticGammaForwardProduct_add_one`, `..._Backward..._add_one` — both entire products
  are `1`-periodic pointwise;
- `addTranslationAnalyticEquiv_one_...Analytic` — hence both germs are fixed by the unit
  translation;
- **`addTranslationMeroEquiv_one_multipleEllipticGammaMero`** — so is the meromorphic element, in
  both parity branches;
- **`addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero`** and
  **`addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivFaceMero`** — and therefore its
  logarithmic derivative and *every face coordinate* of the hierarchy.

This is exactly the statement the face-lifting argument needs to run with three directions
`1, tau_q, tau_u`: the unit translation acts trivially on the whole block, so it contributes the
zero displacement to the simultaneous system while completing the rank-three period triple whose
joint fixed field is `C`.

## Lean progress — translation stability of the deeper face field

`formal/GaloisForLFunctions/HTGeometry/FacePacketFieldStability.lean` (axiom-clean, umbrella
registered) supplies the second prerequisite, i.e. the "stability of the deeper field" claim of the
face-lifting lemma in the form the Ostrowski criterion consumes.

- `facePacketUnion tau htau S` — the union of the packets of a family `S` of deleted faces;
- **`facePacketUnion_translate_mem`** — if `S` is **upward closed** (`L in S`, `q notin L` implies
  `insert q L in S`), every structural translation maps each generator into the generated
  differential field: a deleted direction preserves the packet, a surviving direction changes the
  element by a member of the next packet, and the element itself is already there;
- **`differentialAdjoin_facePacketUnion_translate_stable`** — hence the whole generated differential
  field `K = C<facePacketUnion>_delta` is stable under every structural translation.  The proof is an
  `IntermediateField.adjoin` induction: on generators the translation commutes with the jets
  (`DifferentialAlgEquiv.map_differentialJet`) and `K` is derivation closed, and the field
  operations are preserved because the translation is a ring homomorphism fixing the constants.

Both prerequisites recorded earlier are now in place — the unit period of the hierarchy and the
translation stability of `K_(s+1)`.  What remains for the descending face-lifting lemma is the
instantiation of `automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping`
itself, with the three directions `1, tau_q, tau_u`, the displacement data from `facePacket_coface`,
the joint fixed field from `rankThree_generator_jointFixed_iff_constant`, and the telescoping
exclusion from `facePacket_oneSlice_ne_coboundary`.

## Lean progress — the structural translations restrict to automorphisms of the deeper face field

`formal/GaloisForLFunctions/HTGeometry/FacePacketFieldTranslation.lean` (axiom-clean, umbrella
registered) upgrades stability to invertibility, which is what the Ostrowski criterion actually
consumes: it takes a *family of ring automorphisms* of the base field, not merely stable maps.

- `differentialAdjoin_translate_stable_of_generators` — a translation that moves the generators of a
  generated differential field inside it moves the whole field inside it (adjoin induction);
- **`facePacketUnion_neg_translate_mem`** — the *inverse* translation also moves the generators
  inside.  Reading the coface equation at the shifted lattice point `-tau_q + g` and cancelling
  gives `sigma_(-tau_q) y = y - sigma_(-tau_q + g) F_(L union {q})`, and the subtracted term is a
  member of the next packet, which is in the family because it is upward closed;
- **`differentialAdjoin_facePacketUnion_neg_translate_stable`** — hence the deeper face field is
  stable under `sigma_(-tau_q)` too;
- **`facePacketFieldTranslation`** — therefore the structural translation restricts to a genuine
  ring automorphism `K_(s+1) ~= K_(s+1)`, with `facePacketFieldTranslation_coe` identifying its
  underlying map.

## Finding — the one-slice obstruction must survive a *moving* base field

The corpus's free-shift one-slice nonsummability, and its transported form
`facePacket_oneSlice_ne_coboundary`, are stated for a shift that fixes the coefficient field of the
free grid pointwise.  The face-lifting lemma cannot use them directly: its base field
`K_0 = D<all deeper orbits except O_(J union {q})>_delta` is only `T_q`-*stable*, and `T_q` moves it
(already `D` contains `C(z)`, on which `T_q` is `z -> z + tau_q`).  So the obstruction needed is the
`K_0`-semilinear one: the shift advances the grid slice by one **and twists the coefficients**.

The corpus's periodic-collapse proof does not survive that twist — after collapsing the shifted
support back onto the original support the two sides of the cleared identity become
`p^(phi^N) q - p q^(phi^N)`, which need not vanish.  A different argument is required, and it is in
fact stronger and shorter.

## Lean progress — twisted one-slice nonsummability

`formal/GaloisForLFunctions/HTGeometry/TwistedFreeShiftNonsummability.lean` (axiom-clean, umbrella
registered) proves the semilinear obstruction by a two-sided variable-window argument.

- `twistedShiftPolyEquiv phi`, `twistedShiftFieldEquiv phi` — the `phi`-twisted unit shift of the
  free bilateral jet grid and of its rational function field;
- `mem_vars_twistedShiftPolyEquiv` — its variables are exactly the shifted variables (the twist is
  injective on coefficients, so it changes no variable);
- **`twistedShiftPoly_sub_ne_oneSlice`** — the polynomial case.  If `T P - P` is supported on the
  slice `0`, then the variable of `P` of largest slice `M` reappears in `T P` at slice `M + 1`,
  which must be `0`; and the variable of smallest slice `m` must have come from slice `m - 1`,
  so `m = 0`.  Hence `M = -1 < 0 = m`, impossible; so `P` is constant, and a constant primitive
  changes by a constant, not by a nonzero one-slice form;
- **`twistedShiftOneSlice_ne_coboundary`** — the rational case.  A reduced fraction `p / q` of a
  primitive satisfies `q | T q` (coprimality plus the cleared identity), and comparing the smallest
  slice of the variables of `q` with those of `T q` forces `q` to be constant, so the primitive is a
  polynomial;
- `twistedShiftFieldEquiv_refl` — for the trivial twist this is the canonical free shift, so the
  new theorem contains the corpus's untwisted one.

`formal/GaloisForLFunctions/HTGeometry/TwistedFreeShiftTransport.lean` (axiom-clean, umbrella
registered) transports it to any ambient realization:

- **`twistedShift_parametrization_coe`** — if a bilateral palette is differentially independent over
  a base field `F` and an ambient ring automorphism `Psi` commutes with the derivation, moves the
  palette one slice, and acts on `F` by `phi`, then the canonical parametrization of the generated
  differential field intertwines `Psi` with the `phi`-twisted shift (checked on `C` and `X` by
  polynomial induction, then on fractions);
- **`oneSlice_ne_coboundary_of_twisted_ambient_shift`** — hence no nonzero finite `F`-linear form in
  the jets of the zero slice is a coboundary for `Psi`.  This is the exact statement the descending
  face-lifting lemma needs, with `F = K_0` and `Psi = T_q`.

## Lean progress — the rank-three difference system of a face packet

`formal/GaloisForLFunctions/HTGeometry/FacePacketDifferenceSystem.lean` (axiom-clean, umbrella
registered) assembles the three structural directions into the exact input shape of the corpus's
several-automorphism Ostrowski criterion.

- `meroTranslationRestrict` — a translation stabilizing an intermediate field in both directions
  restricts to a ring automorphism of it (the stability lemmas of the two previous files are now
  stated per direction, which is all they ever used);
- `differentialAdjoin_fixed_of_generators`, **`differentialAdjoin_facePacketUnion_one_fixed`** — the
  unit translation fixes every packet element (`sigma_1 sigma_g F_L = sigma_g sigma_1 F_L`), hence
  fixes the whole deeper face field pointwise; the same holds for `sigma_(-1)`;
- `facePacketPeriods tau q u = ![1, tau_q, tau_u]` — the three structural periods;
- **`facePacketDifferenceSystem`** — the three restricted translations as a
  `CommutingDifferenceDifferentialField (Fin 3) C K_(s+1)`: they commute, they commute with the
  derivation, and they fix the constants;
- **`facePacketBlock`** — the translation block of the face `J`, indexed by its own packet;
- **`facePacketDisplacement`** — its displacements, which lie in the deeper face field: the unit
  direction contributes `0`, and each surviving direction contributes the coface element
  `T_J^a F_(J union {q})`;
- **`facePacket_differentialIndependent_of_no_telescoping`** — the descending face-lifting lemma:
  with `1, tau_q, tau_u` rationally independent, the block is differentially algebraically
  independent over `K_(s+1)` as soon as no nonzero finite constant-coefficient jet form of the
  displacements is a simultaneous coboundary there.  The joint fixed field is supplied by
  `rankThree_generator_jointFixed_iff_constant`.

The lemma is therefore now reduced to a single remaining implication: the exclusion of a
simultaneous jet telescoper, which is what the twisted one-slice obstruction of the previous section
is for.

## Lean progress — the descending face-lifting lemma

`formal/GaloisForLFunctions/HTGeometry/FacePacketFreeTelescoping.lean` (axiom-clean, umbrella
registered) closes the last implication of the face-lifting lemma by feeding the twisted
obstruction into the difference system.

- `facePacketBaseFamily S J q = S \ {insert q J}` and **`facePacketBaseFamily_closed`** — removing
  the target packet leaves a family still closed in the direction `q`: a deeper face `L` with
  `insert q L = insert q J` satisfies `L = J`, which is excluded because `J` is not deeper than
  itself.  This is step (22) of the paper argument;
- **`facePacket_displacement_mem_slice`** — the displacement of a block element in a surviving
  direction is the coface element `T_J^a F_(J union {q})`, and its exponent in the direction `q`
  vanishes: it lies in the *zero slice* of the next packet;
- `facePacketDisplacementSlice` — hence the displacement labelling of the block by that zero slice;
- **`facePacket_no_telescoping_of_free`** — if the target packet is differentially independent over
  `K_0` and generates `K_(s+1)` over it, and the displacement labelling is injective, then in the
  direction `q` no nonzero finite constant-coefficient jet form of the displacements is a
  coboundary: transporting through the free parametrization turns the translation into the
  `phi`-twisted shift with `phi` its own restriction to `K_0`, and the form is supported on the
  single slice `0`;
- **`facePacket_differentialIndependent_of_free`** — the descending face-lifting lemma: the
  translation block of the face `J` is differentially algebraically independent over the deeper face
  field.

**`facePacketUnion_le_free_adjoin`** discharges the generation half unconditionally: every packet of
a face other than the target lies in the complementary base field, and the target packet is exactly
the range of its own palette (`range_facePalette`), so the deeper face field is contained in
`K_0<O_(J union {q})>_delta`.  The paper proof of the face-lifting lemma is therefore formalized in
full, with only two remaining inputs: the freeness of the target packet over the complementary base
(the induction hypothesis of the descending induction) and the injectivity of the displacement
labelling (a nonresonance statement: distinct translates of `F_(J union {q})` are distinct), together
with the `Q`-independence of `1, tau_q, tau_u`.

## Lean progress — the gluing engine over a moving base

The layer-completion step applies uniform simplicial-star gluing *over `K_(s+1)`*, and the
structural translations do **not** fix `K_(s+1)` pointwise — they only normalize it.  The corpus's
gluing specialization was stated for coefficient-fixing automorphisms
(`HTGeometry.DifferentialAlgEquiv`), so it did not apply.

`formal/GaloisForLFunctions/HTGeometry/SemilinearDifferentialRank.lean` (axiom-clean, umbrella
registered) removes that restriction, reusing the corpus's existing base-normalizing transport
(`HTGeometry.DifferentialSemilinearEquiv.differentialIndependent_map_iff`):

- **`HTGeometry.DifferentialSemilinearEquiv.diffIndepOn_image_iff`** — a base-normalizing
  differential automorphism preserves differential independence of sets exactly;
- `differentialMatroid_mapEquiv_differentialSemilinearEquiv` — hence it is an automorphism of the
  differential matroid;
- **`HTGeometry.DifferentialSemilinearEquiv.mem_differentialRank_rankAutSubgroup`** — hence it
  preserves the genuine differential rank, which is all the gluing engine ever needed;
- **`differentialRank_uniformFace_nestedStar_diffIndepOn_semilinear`** and
  **`..._of_orbit_semilinear`** — the all-order uniform-face nested-star gluing theorems with the
  acting automorphisms only normalizing the base.

## Lean progress — completing one face layer

`formal/GaloisForLFunctions/HTGeometry/FacePacketLayerGluing.lean` (axiom-clean, umbrella
registered) performs the layer-completion step of the paper over the deeper face field.

- **`facePacketSemilinearEquiv`** — the structural translation `T_q` as a base-normalizing
  differential automorphism of the meromorphic field over `K_(s+1)`: it normalizes `K_(s+1)` by
  `facePacketFieldTranslation` and commutes with the derivation;
- **`multipleEllipticGammaFaceStar_diffIndepOn_deeper`** — the nested-star gluing engine over
  `K_(s+1)`: the star of every direction is a union of full translation orbits
  (`faceStar_eq_orbitUnion`), so the whole layer is jointly independent over `K_(s+1)` given
  atomicity of each packet over that field, star nonresonance and off-star differential
  algebraicity;
- **`multipleEllipticGammaFaceLayer_diffIndepOn_deeper`** — the layer step itself: with two
  surviving directions per face, the face-lifting lemma supplies the atomicity input, so the entire
  `s`-layer is jointly differentially independent over the deeper face field.

Together with the previous sections this formalizes the paper's chain
"face lifting -> layer completion" over a *moving* base field, which is what the structure of the
hierarchy forces.  The remaining inputs are the analytic ones the card already isolates: bottom-layer
atomicity, star nonresonance (`hStarInj`), off-star differential algebraicity (`hOffDA`), and the
per-face freeness/injectivity data that the descending induction is to carry.

## Lean progress — the descending induction

`formal/GaloisForLFunctions/HTGeometry/FaceLayerDescendingUnion.lean` (axiom-clean, umbrella
registered) turns the layer steps into the descending induction of the paper.

- **`diffIndepOn_union_of_base`** — if `B` is differentially independent over `k` and `A` is
  differentially independent over `k<B>_delta`, then `A ∪ B` is differentially independent over `k`.
  Disjointness of `A` and `B` is *automatic*: an element of `k<B>_delta` is differentially algebraic
  over it, so it cannot belong to a family independent over it;
- `faceStar_empty_eq_facePacketUnion` — the total star of a face family is the union of its packets,
  so the layer theorem's conclusion is exactly a packet union;
- `facePacketUnion_union`, `facePacketUnion_empty` — the packet union of a union of face families
  splits;
- **`facePacketUnion_diffIndepOn_union`** — the descending step for face families;
- **`facePacketUnion_diffIndepOn_iterate`** — the descending induction: adding one layer at a time,
  each independent over the field generated by the layers already added, every partial union is
  differentially independent over the constants.

This is the paper's "starting from the bottom layer and descending" step; combined with the layer
theorem it reduces the target statement (7) — joint independence of the whole face filtration — to
the analytic inputs alone.

## Finding — the bottom layer needs the *orbit*, and the orbit is a shear of the defect family

The bottom-layer input is the independence of the translation *orbit* `O_J = {T_J^a F_J}`, not of the
family of external defects.  The corpus's order-one atomic theorem
(`ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase`) is about defects.  The
two statements differ by adding the untranslated member to each defect, which is an *invertible
shear of the free differential polynomial ring*, so they are equivalent once the untranslated member
is part of the family.

An attempt to run the Ostrowski criterion directly on the orbit fails for a structural reason worth
recording: the `sigma`-increment of a translate `sigma_h Psi` is `sigma_h` of the *plain* theta
logarithmic derivative, which is quasi-elliptic, not elliptic — it does not lie in the paired
elliptic compositum, whereas the increment of a *defect* is a genuine theta defect and does.  This is
exactly why the corpus's order-one machinery is phrased with defects, and why the orbit statement
needs the extra input below rather than a re-run of the criterion.

## Lean progress — translate families versus defect families

`formal/GaloisForLFunctions/HTGeometry/TranslateFamilyIndependence.lean` (axiom-clean, umbrella
registered) formalizes the shear.

- **`optionShearAlgHom`** — the substitution of the free jet polynomial ring adding `eps` times the
  distinguished jet variable to every other jet variable of the same order, with the opposite shear
  as inverse (`optionShearAlgHom_comp`, `optionShearAlgHom_injective`);
- **`differentialIndependent_option_add_base`**, **`..._sub_base`**, **`..._iff`** — a family
  `(v, (v + x i))` is differentially independent exactly when `(v, (x i))` is;
- **`diffIndepOn_range_of_differentialIndependent`** — an independent family has an independent
  range (a section of the parametrization is injective);
- `notMem_of_hypertranscendentalOver_differentialAdjoin`;
- **`diffIndepOn_insert_translate`** — the set form: if `insert v S` is independent, so is
  `insert v ((v + ·) '' S)`, which is the shape of a translation orbit.

## Lean progress — the order-one translation packet

`formal/GaloisForLFunctions/HTGeometry/EllipticGammaTranslatePacket.lean` (axiom-clean, umbrella
registered) assembles the bottom-layer atomicity from the corpus's defect theorem.

- `ellipticGammaTranslateFamily` and `ellipticGammaTranslateFamily_eq_add_defect` — the orbit is the
  untranslated logarithmic derivative plus its defect family;
- **`ellipticGammaTranslatePacket_diffIndepOn`** — the orbit is differentially independent over the
  constants, given the corpus's separated-defect independence and the single further input that the
  logarithmic derivative is hypertranscendental over the differential field generated by its own
  defects;
- **`ellipticGammaTranslatePacket_diffIndepOn_daExtension`** — the same over every differentially
  algebraic extension, i.e. over the field `D` of the all-order argument.

The bottom layer of the card is therefore reduced to exactly one analytic statement:

```text
Psi is hypertranscendental over C(z)<Delta_h Psi : h in A>_delta                (BL)
```

for a separated nonresonant finite shift family `A`.  This is the residual analytic frontier of the
bottom layer; everything else in the layer is now formal.

## The bottom-layer input (BL) is a free-block replication count — proof plan

(BL) — `Psi` is hypertranscendental over `C(z)<Delta_h Psi : h in A>_delta` — does **not** need new
analytic input.  It is a rank count in the differential matroid, i.e. the free-block replication
lemma of this card, instantiated with a generic external shift:

1. Suppose `Psi` is DA over the field generated by the `A`-defects, `|A| = m`.  Then in the
   differential matroid over `C` (equal to the matroid over `C(z)` by
   `differentialMatroid_meromorphicRationalCoordinateField_eq`), `Psi` lies in the closure of the
   `A`-defects, so the block `S_1 = {Psi} union Delta(A)` has rank at most `m`.
2. Translation by a shift `w` is a *coefficient-fixing* differential automorphism over `C`, so it
   transports matroid closures (`mem_differentialMatroid_closure_image_iff`); hence the translated
   block `S_2 = sigma_w(S_1)` also has rank at most `m`.
3. The generated field of `S_1 union S_2` contains the defects at `A`, at `A + w` and at `w`,
   because `Delta_{a+w} = sigma_w(Delta_a) + Delta_w` and `Delta_w = sigma_w Psi - Psi`.
4. For a *generic* `w` those `2m+1` shifts are pairwise separated and nonresonant, so the
   corresponding defect family is differentially independent by the order-one atomic theorem, giving
   rank exactly `2m+1`.
5. Submodularity of the matroid rank gives `2m+1 <= rank(S_1) + rank(S_2) <= 2m`, a contradiction.

The genericity step is now formalized:
`formal/GaloisForLFunctions/HTGeometry/ThetaGenericShift.lean` (axiom-clean, umbrella registered)
supplies `thetaResonanceSet`, its countability, and **`exists_thetaGenericShift`** — for any finite
set of offsets there is a shift `w` with every `w + s` nonresonant — together with the instance
`Uncountable ℂ` that the argument needs.  Steps 1–5 are the next Lean target; every ingredient they
use (`differentialMatroid_mem_closure_iff_differentialAlgebraicOver_differentialAdjoin`,
`mem_differentialMatroid_closure_image_iff`, `Matroid.eRk_union_le_eRk_add_eRk`,
`Matroid.Indep.eRk_eq_encard`, `ellipticGammaExternalDefectFamily_differentialIndependent_rationalBase`)
is already present in the corpus or mathlib.
