# The order-three elliptic-gamma structural orbit has no hidden nonlinear relations

- **ID:** `order-three-elliptic-gamma-full-structural-differential-matroid`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / THREE-LAYER DIFFERENTIAL-ALGEBRAIC MATROID
- **Date:** 2026-07-10
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` -- conditional on the independently
  unaudited order-one elliptic-gamma atomic theorem. The theorem closes the first case containing
  several atomic bottom faces, external orbits of higher faces, and a top primitive. Its
  free-shift summability lemma is a `[BRIDGE]`; the candidate scientific content is the exact
  nonlinear matroid of the generic order-three multiple-elliptic-gamma structural orbit.
- **Parents:**
  `order-three-elliptic-gamma-bottom-face-joint-atomicity`;
  `order-two-elliptic-gamma-full-structural-differential-matroid`;
  `multiple-elliptic-gamma-transverse-constraint-depth`;
  `elliptic-gamma-rank-three-da-spectrum`
- **Statement:** For the generic order-three multiple elliptic gamma logarithmic derivative, the
  differential transcendence degree of every finite structural family is the linear rank of its
  operator classes in the localized Stanley--Reisner ring `R_3/I_3`. Hence the squarefree
  triple-face ideal generates every nonlinear differential dependence.

## Setup

Let

```text
F=Psi_3(z;tau_0,tau_1,tau_2,tau_3),
T_i=T_(tau_i),
x_i=T_i-1,
```

and assume

```text
1,tau_0,tau_1,tau_2,tau_3
```

are linearly independent over `Q`.

The proper structural faces have two layers. For distinct indices put

```text
B_i=x_iF=Psi_2(z;tau_j,tau_k,tau_l),                     (1)
A_ij=x_ix_jF=Psi_1(z;tau_k,tau_l),                       (2)
```

where the parameters on the right are the complementary ones, up to the harmless DA hierarchy
normalization. Define their external orbits

```text
O_i={T_i^nB_i:n in Z},                                   (3)
O_ij={T_i^aT_j^bA_ij:a,b in Z}.                          (4)
```

The separate bottom-face theorem proves that the union of all six families (4) is differentially
algebraically independent over `C(z)`.

## The bottom differential field

Let `D` be the differential field of all `1`-periodic meromorphic functions that are DA over
`C(z)`. It is stable under every complex translation. Since `D/C(z)` is differential algebraic,
the bottom family remains independent over `D`.

Let

```text
K=D<union_(i<j) O_ij>_delta.                              (5)
```

Thus `K` is a free differential-rational field over `D` on the six bottom-face orbit families. It
is stable under every `T_i`. Indeed, `T_i` either shifts one external orbit coordinate or, when
`i` is structural for that face, changes it by a member of `D`.

The first new task is to show that no order-two face primitive becomes differentially dependent
after adjoining this entire bottom field.

## Free-shift one-slice nonsummability `[PROVED HERE]`

Let `(K_0,delta,sigma)` be a difference-differential field of characteristic zero. Let

```text
{X_(alpha,n):alpha in A, n in Z}
```

be differential indeterminates over `K_0`, and extend `sigma` by

```text
sigma(X_(alpha,n))=X_(alpha,n+1),
sigma delta=delta sigma.                                  (6)
```

Put

```text
L=K_0<X_(alpha,n):alpha in A,n in Z>_delta.
```

For a finite set `A_0 subset A` and operators `P_alpha in C[delta]`, not all zero, where `C` is a
subfield of the joint constants, the one-slice form

```text
H=sum_(alpha in A_0)P_alpha(delta)X_(alpha,0)             (7)
```

is not a `sigma`-coboundary in `L`:

```text
H!=sigma(G)-G for every G in L.                           (8)
```

### Proof: denominators cannot occur

Regard all jets

```text
X_(alpha,n)^(r)=delta^rX_(alpha,n)
```

as algebraically independent variables. Every `G in L` is a rational function in finitely many of
them.

Suppose `sigma(G)-G` is polynomial in the jet variables. If the denominator of `G` has an
irreducible factor `p` involving a jet variable, the `sigma`-orbit of `p` is infinite up to units of
`K_0`: every iterate shifts the finite set of second indices occurring in `p`, and a nonzero finite
subset of `Z` has no nontrivial translation stabilizer.

Only finitely many members of this irreducible orbit can occur as poles of `G`. Choose a pole whose
predecessor is not a pole. At that divisor `sigma(G)` is regular while `G` has a pole, so
`sigma(G)-G` has a pole. This contradicts polynomiality. Hence every denominator belongs to
`K_0`, and `G` is a polynomial in the jet variables with coefficients in `K_0`.

### Proof: nonlinear degrees cannot occur

The automorphism preserves total jet degree. If `G` has degree `d>1`, its top homogeneous part
`G_d` satisfies

```text
sigma(G_d)=G_d,
```

because (7) has degree one. But a nonconstant finite polynomial in the free shift variables cannot
be `sigma`-invariant: every nonconstant monomial has an infinite orbit under simultaneous shift of
its second indices. Therefore `G_d=0`, a contradiction. Thus

```text
G=G_0+sum_(alpha,n,r)c_(alpha,n,r)X_(alpha,n)^(r),        (9)
```

with only finitely many nonzero coefficients in `K_0`.

### Proof: a finite primitive has two boundary slices

Fix `(alpha,r)` and write `c_n=c_(alpha,n,r)`. The coefficient of `X_(alpha,n)^(r)` in
`sigma(G)-G` is

```text
sigma(c_(n-1))-c_n.                                       (10)
```

If the finite sequence `(c_n)` is nonzero, let `p` and `q` be its least and greatest occupied
indices. At slice `p`, (10) equals `-c_p`; at slice `q+1`, it equals `sigma(c_q)`. A nonzero finite
primitive therefore has two distinct boundary slices. It cannot produce a form supported only at
slice `0`.

Applying this independently to every `(alpha,r)` forces every coefficient in (7) to vanish,
contrary to assumption. This proves (8). `QED`

This is the rational-function version of an orbital-residue obstruction: the sum of the linear
coefficients along a free shift orbit must vanish for a finite coboundary. The proof above is
included because the ambient field contains all differential jets and arbitrary rational
expressions, not only linear polynomials.

## Each order-two external orbit is independent over the bottom field `[PROVED HERE]`

Fix `i` and a finite set `S subset Z`. Put

```text
Y_n=T_i^nB_i,  n in S.                                   (11)
```

Choose two distinct indices `q,r` different from `i`. The hierarchy gives simultaneous additive
difference equations over `K`:

```text
(T_q-1)Y_n=T_i^nA_iq,
(T_r-1)Y_n=T_i^nA_ir.                                    (12)
```

All elements of `K<Y_n:n in S>` are `1`-periodic. An element fixed by both `T_q` and `T_r` has
periods `1,tau_q,tau_r`; their period group is nondiscrete, so a meromorphic common invariant is
constant. Hence the common fixed field is `C`.

Assume the `Y_n` are differentially dependent over `K`. Apply the simultaneous telescoping lemma
proved in `elliptic-gamma-rank-three-da-spectrum` for commuting translations. It supplies
operators

```text
L_n in C[delta], not all zero,
```

and one `G in K` satisfying, in particular,

```text
(T_q-1)G=sum_(n in S)L_n(delta)T_i^nA_iq.                 (13)
```

Let `K_0` be generated over `D` by every bottom orbit except `O_iq`. It is stable under `T_q`:
on another edge containing `q`, the translation shifts that edge orbit, while on an edge avoiding
`q` it adds a DA function in `D`.

Joint bottom-face independence identifies

```text
K=K_0<T_i^aT_q^bA_iq:a,b in Z>_delta                    (14)
```

with a differential-rational free shift field over `K_0`. Under `T_q`, the second exponent in
(14) shifts by one. The right side of (13) is a nonzero constant-coefficient differential-linear
form supported entirely on the slice `b=0`. The one-slice nonsummability theorem contradicts
(13).

Therefore every finite subfamily (11) is independent over `K`, and the full external orbit `O_i`
is differentially algebraically independent over the entire bottom field. `QED`

## The four order-two face orbits are jointly independent `[PROVED HERE]`

Order the four indices arbitrarily. Suppose finite parts of earlier orbits have been adjoined to
`K`, and let `E` be the resulting differential field. To adjoin a finite block `B subset O_i`, use
`sigma=T_i`.

For every earlier face `B_j`, `j!=i`, the direction `tau_i` is structural and

```text
(T_i-1)T_j^nB_j=T_j^nA_ij in K.                          (15)
```

Since `K` is `T_i`-stable, finite telescoping shows

```text
T_i^m(E)=E for every m in Z.                              (16)
```

Arbitrarily many separated `T_i`-translates of `B` are disjoint subfamilies of `O_i`, which is
independent over `K`. Apply the free-block replication lemma over the base field `K`. It makes `B`
independent over `E`.

Induction gives

```text
union_(i=0)^3 O_i                                        (17)
```

differentially algebraically independent over `K`. `QED`

## The order-three primitive is independent from every proper face `[PROVED HERE]`

Fix finite sets `S_i subset Z` and suppose `F` is DA over the field generated by `K` and

```text
{T_i^nB_i:i in {0,1,2,3}, n in S_i}.                     (18)
```

Choose one direction `i` and a positive integer `N` so large that

```text
J={0,...,N-1}\(S_i union (S_i+N))
```

is nonempty. Translate the assumed relation by `T_i^N`. The `i`-face indices shift to `S_i+N`.
Every other face generator changes by an element of `K` by (15), and `K` itself is stable.
Consequently both `F` and `T_i^NF` are DA over the field generated by `K`, the other finite face
coordinates, and the `i`-face coordinates indexed by `S_i union (S_i+N)`.

Their difference is DA over that field. But

```text
T_i^NF-F=sum_(n=0)^(N-1)T_i^nB_i.                        (19)
```

Subtracting the terms whose indices are already in `S_i union (S_i+N)` makes the nonempty sum

```text
sum_(n in J)T_i^nB_i                                    (20)
```

DA over the field generated by all complementary proper-face coordinates. This contradicts the
joint independence (17). Thus `F` is differentially transcendental over every finite proper-face
field. `QED`

Combining the bottom theorem, (17), and the primitive theorem shows that the full coordinate family

```text
{F}
 union {T_i^nB_i:i,n}
 union {T_i^aT_j^bA_ij:i<j,a,b}                          (21)
```

is differentially algebraically independent over `D`, hence over `C(z)`.

## Squarefree structural module

Let

```text
S=C[delta],
R=S[t_0^(+-1),t_1^(+-1),t_2^(+-1),t_3^(+-1)],
I_3=(x_0x_1x_2,x_0x_1x_3,x_0x_2x_3,x_1x_2x_3).
```

The tensor decomposition

```text
S[t_i^(+-1)]=S direct_sum x_iS[t_i^(+-1)]
```

gives the unique direct sum

```text
R/I_3
 =S
  direct_sum direct_sum_i x_iS[t_i^(+-1)]
  direct_sum direct_sum_(i<j)x_ix_jS[t_i^(+-1),t_j^(+-1)].    (22)
```

Acting on `F`, the three layers in (22) become, modulo DA normalizations,

```text
L(delta)F,
Q_i(delta,T_i)B_i,
Q_ij(delta,T_i,T_j)A_ij.                                 (23)
```

They are constant-coefficient differential-linear forms in the independent coordinates (21).
It follows first that the full differential-operator annihilator is exactly

```text
Ann_R(F modulo DA)=I_3.                                  (24)
```

The parent theorem had established (24) by a linear support argument. Here it is recovered as the
rank-one shadow of the stronger nonlinear family theorem below.

## Complete order-three structural differential-matroid theorem `[PROVED HERE]`

For arbitrary `P_1,...,P_m in R`, let `Pbar_j` be their classes in `R/I_3`. Then

```text
dtrdeg_(C(z)) C(z)<P_1(T)F,...,P_m(T)F>_delta
  =dim_(C(delta)) span{Pbar_1,...,Pbar_m}                 (25)
```

inside

```text
C(delta) tensor_(C[delta]) (R/I_3).
```

### Proof

Only finitely many coordinates from (21) occur in (23) for the displayed family. They are
differentially independent. The unique decomposition (22) identifies the coefficient rank of the
resulting differential-linear forms with the rank of the classes `Pbar_j`.

Smith normal form over the PID `C[delta]` reduces any finite coefficient matrix to its nonzero
diagonal invariant factors. A nonzero constant-coefficient differential operator applied to one
differential indeterminate remains differentially transcendental, and distinct diagonal
coordinates remain independent. Hence the differential transcendence degree equals the matrix rank
over `C(delta)`, proving (25). `QED`

Therefore every nonlinear differential dependence among finitely many structural combinations is
already witnessed by a constant-coefficient differential-linear relation modulo `I_3`. No hidden
nonlinear dependence locus remains.

## Structural translates and one explicit circuit

For exponent vectors `n^(1),...,n^(m) in Z^4`, the differential transcendence degree of

```text
T^(n^(1))F,...,T^(n^(m))F
```

is the ordinary linear rank of the Laurent monomials `t^(n^(j))` in the localization of the
Stanley--Reisner ring of the one-skeleton on four vertices.

For example, the eight vertices of a cube in directions `0,1,2` have degree `7`. Their one relation
is the DA triple face

```text
(T_0-1)(T_1-1)(T_2-1)F=Psi_0,
```

and (25) proves that no nonlinear differential relation lowers the degree below `7`.

## Multiplicative order-three theorem `[PROVED HERE]`

For integral Laurent polynomials `E_1,...,E_m`, let `G_(3,E_j)` be the corresponding finite integer
products and quotients of structural translates of the order-three multiple elliptic gamma
function. Then

```text
dtrdeg(G_(3,E_1),...,G_(3,E_m))
  =dim_C span{Ebar_1,...,Ebar_m}                           (26)
```

in `C[t_0^(+-1),...,t_3^(+-1)]/I_3`.

The lower bound follows by logarithmic differentiation and (25). The integral form of (22) is
torsion-free. Therefore rational relations among integral classes have an integer basis after
clearing denominators. Every such integer relation gives a product whose logarithmic derivative is
DA, so the product itself is DA by differential-algebraic transitivity. Choosing a basis of the
classes shows that all remaining products are algebraic over the differential field generated by
that basis and DA functions, giving the upper bound.

## What this changes and what remains open

The order-two theorem had one primitive over three atomic branches. Order three is qualitatively
different: it contains six atoms on different elliptic curves, four external orbits of order-two
primitives, and the top primitive. The theorem proves exact nonlinear independence through all
three layers.

It does not prove the all-order conjecture. At order four, bottom order-one faces have
three-dimensional external orbits indexed by hyperedges, and the graph-star proof no longer
automatically supplies joint atomicity. Intermediate faces also form more than one nontrivial
filtration layer. A hypergraph elimination order or a different residue invariant is required.

## Parent-theory and literature attack

The one-slice lemma is a self-contained differential-rational form of classical rational
difference summability and orbital residues. Chen--Singer's discrete residues and the modern
Arreche--Sitaula formulation characterize rational shift summability by vanishing orbit residues;
the two-boundary-slice argument is the free-variable specialization of that known obstruction.
Smith normal form and the final rank passage are standard. The simultaneous telescoping implication
is inherited from several-automorphism parameterized Picard--Vessiot theory. None is promoted
independently.

The nonroutine synthesis is the three-layer face argument:

1. graph-star replication makes all six bottom elliptic curves jointly atomic;
2. free-shift nonsummability prevents an order-two external primitive from collapsing over the
   complete bottom field;
3. relative block replication glues the four order-two face orbits;
4. a long structural translation recovers the top primitive;
5. the face decomposition converts these analytic facts into the exact Stanley--Reisner matroid.

Hardouin's diagonal systems and Hardouin--Singer parameterized difference Galois theory treat
solutions of fixed linear difference systems. Ogawara treats a triangular classical multiple-gamma
hierarchy under one common shift. Adamczewski--Dreyfus--Hardouin--Wibmer compare solutions belonging
to two independent operator classes and obtain algebraic independence. These theories are serious
parents for individual steps, but no located theorem computes the nonlinear differential matroid of
a three-layer, four-translation squarefree hierarchy.

Narukawa, Winding, Kato, and the geometric multiple-elliptic-gamma literature treat modularity,
integral formulas, cone variants, rational-period DA, and cocycles. Exact, equivalent, stronger,
and mechanism searches through 2026 located no order-three structural family theorem, no
Stanley--Reisner differential matroid, and no classification asserting that the squarefree
triple-face relations generate all nonlinear dependence.

The scientific novelty verdict is provisionally positive, conditional on the order-one atomic
parent and independent expert audit. If the atomic parent fails, every special-function conclusion
on this card is demoted; the abstract summability and replication lemmas remain bridges only.

## Significance gate

The theorem advances from DA/HT status of one function and linear annihilator membership to the
exact differential transcendence degree of every finite additive and multiplicative structural
family. It also proves that the first higher face filtration has no emergent nonlinear dependence
at any layer. This eliminates the principal live failure mode of the all-order conjecture at order
three.

## Gates

- [x] joint bottom-face atomicity imported from the separate proved theorem
- [x] free-shift one-slice nonsummability proved for rational differential functions
- [x] each external order-two orbit proved independent over the complete bottom field
- [x] four order-two face orbits proved jointly independent
- [x] order-three primitive proved independent from every proper face
- [x] complete additive structural differential matroid proved
- [x] multiplicative finite-product matroid proved
- [x] exact/stronger/equivalent literature gate completed provisionally through 2026
- [ ] independent proof audit
- [ ] independent specialist priority audit
- [ ] independent audit of the order-one atomic parent
- [ ] order-four hypergraph face-filtration theorem

## Log

- 2026-07-10 -- Reduced external order-two orbit independence to simultaneous telescoping over the
  free bottom field.
- 2026-07-10 -- Proved the one-slice nonsummability theorem by denominator orbits, polynomial degree,
  and the two boundary slices of every finite primitive.
- 2026-07-10 -- Glued all four external order-two face orbits by relative block replication.
- 2026-07-10 -- Recovered the top primitive by a long structural translation and computed the full
  order-three additive and multiplicative differential matroids.
