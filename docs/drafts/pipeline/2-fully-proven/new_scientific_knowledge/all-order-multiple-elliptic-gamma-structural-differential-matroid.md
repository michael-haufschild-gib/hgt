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
   `GaloisForLFunctions.DifferentialIndependence`;
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
6. free differential-shift nonsummability, nested-star gluing, the Stanley--Reisner decomposition,
   and the rank theorem;
7. the concrete all-order capstone with its additive and multiplicative corollaries.

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
