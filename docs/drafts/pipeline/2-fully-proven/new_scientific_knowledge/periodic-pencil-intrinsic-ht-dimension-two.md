# Periodic pencils compress the intrinsic HT dimension of nonpure relation geometry

- **ID:** `periodic-pencil-intrinsic-ht-dimension-two`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / INTRINSIC HT CONSTRAINT-DIMENSION GEOMETRY
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** A periodic-pencil representation of the facet complements of a finite simplicial
  complex produces an entire non-multiple-Gamma HT system in the same analytic dimension whose
  exact full nonlinear differential matroid is the localized Stanley--Reisner matroid.  Analytic
  dimension one is exactly the simplex-or-pure-principal stratum.  The
  connected nonpure two-thick complex `S^1 wedge S^2` has periodic-pencil dimension and intrinsic
  HT realization dimension exactly two, although its faithful hyperplane dimension is four.

## The geometric invariant

Let `Delta` be a finite simplicial complex on an essential finite vertex set `V`.  A **periodic-
pencil facet separation in dimension `d`** consists of

```text
a_v in C^d                                  for v in V,
ell_A in Hom_C(C^d,C) \ {0},  omega_A in C^* for A in Fac(Delta),        (1)
```

such that:

1. the vectors `(a_v)` are linearly independent over `Q`;
2. for every facet `A` and every `v notin A`,

   ```text
   ell_A(a_v)/omega_A in Z;                                  (2)
   ```

3. for every facet `A`, the family

   ```text
   {1} union {ell_A(a_v)/omega_A:v in A}                     (3)
   ```

   is linearly independent over `Q`.

Condition (2) places the complement of `A` in the periodic pencil

```text
union_(n in Z) ell_A^(-1)(n omega_A),                        (4)
```

while (3) makes the integral translation action of the vertices of `A` faithful modulo that
pencil.  In particular, no vertex of `A` lies in (4).

Define

```text
ppDim(Delta)=min{d:a periodic-pencil facet separation exists}.            (5)
```

This differs from faithful facet-separation dimension: a facet complement need not lie in one
hyperplane.  It may occupy different parallel leaves of one periodic pencil.

The companion theorem `periodic-pencil-matrix-rank-formula.md` removes the existential
quantification: `ppDim` is the minimum of `rank_C M+epsilon_Q(M)` over PP-admissible
facet-evaluation matrices, where the correction is one exactly when `ker M` contains a nonzero
rational vector.

## Periodic-pencil realization theorem `[PROVED HERE]`

If `ppDim(Delta)=d`, there are an entire function `F` on `C^d`, translations

```text
T_vF(z)=F(z+a_v),                                            (6)
```

and a constant directional derivation `delta=D_w` such that, with

```text
D=C(z_1,...,z_d),
S=C[delta],
R=S[t_v^(+-1):v in V],
I_Delta=(prod_(v in N)(t_v-1):N is a minimal nonface),       (7)
```

one has

```text
Ann_R(F)=I_Delta                                             (8)
```

and, for every finite `P_1,...,P_m in R`,

```text
dtrdeg_D D<P_1(T)F,...,P_m(T)F>_delta
 =dim_(C(delta)) span{Pbar_1,...,Pbar_m}                     (9)
```

inside

```text
C(delta) tensor_(C[delta]) (R/I_Delta).                      (10)
```

The sources are generic entire functions on the cylinder `C/Z`; no multiple-Gamma function or
multiple-Gamma recurrence is used.

### Periodic-pencil orbit lemma

Fix finitely many nonzero complex-linear forms `u_j:C^d -> C`, a vector `w` with
`u_j(w)!=0` for every `j`, and countable sets `H_j subset C/Z`.  There exist entire `1`-periodic
functions `h_j` such that the joint family

```text
{h_j(u_j(z)+alpha):j, alpha in H_j}                          (11)
```

is differentially algebraically independent over `C(z_1,...,z_d)` for `delta=D_w`.

#### Proof of the orbit lemma

Write

```text
h_j(u)=H_j(exp(2 pi i u)),   H_j in O(C^*).                  (12)
```

Use the finite product of Frechet spaces `prod_j O(C^*)` as parameter space.  The finite lists of
shift classes, jet orders, and supports of expanded differential monomials form a countable set.
For one such finite support, let `L` be the locus on which its evaluated meromorphic functions are
linearly dependent over `C`.  Dependence is equivalent to the vanishing of every square evaluation
determinant, so `L` is closed.

It has empty interior.  Start with a neighborhood controlled on compact annuli in the copies of
`C^*`.  Choose finitely many evaluation points `z_a` so that, for each `j`, all points

```text
exp(2 pi i (u_j(z_a)+alpha))                                 (13)
```

appearing in the support are pairwise distinct and lie outside the controlling annulus.  To see
that this is possible, choose `b in C^d` outside the finitely many kernels of the `u_j` and put
`z_a=t_a b`.  Choose a ray for `t` on which

```text
Im(t u_j(b)) -> +infinity or -infinity                       (14)
```

for every `j`; only finitely many ray directions are excluded.  The nodes in (13) then tend to
`0` or `infinity`.  Translation collisions exclude only a discrete set of choices of the `t_a`.
After choosing such centers, allow each `z_a` to vary in a sufficiently small full-dimensional
neighborhood of `t_a b`.  The exterior-node and noncollision conditions persist there.  Thus the
admissible evaluation points contain a nonempty open subset of `(C^d)^N`; they are not confined to
the auxiliary line.

The distinct expanded monomials are linearly independent as polynomials in `z` and the finite jet
variables.  Their restrictions to the admissible open set remain linearly independent.  The
standard evaluation lemma therefore permits admissible points and target jets for which one
evaluation determinant is nonzero.  Finite Hermite interpolation with Runge
approximation on `C^*` realizes those target jets while changing each `H_j` arbitrarily little on
its controlling annulus.  The passage from jets of `H_j` at a nonzero node `x` to `delta`-jets of

```text
H_j(exp(2 pi i(u_j(z)+alpha)))                               (15)
```

is triangular, with nonzero order-`r` diagonal coefficient

```text
(2 pi i u_j(w) x)^r.                                        (16)
```

Thus the prescribed jets are genuinely free.  The determinant can be made nonzero in every
parameter neighborhood, so `L` is nowhere dense.

Baire category now removes all countably many finite supports.  Clearing rational denominators
turns every differential-algebraic relation over `C(z_1,...,z_d)` into a constant linear relation
among one of the enumerated supports.  None remains, proving (11). `QED`

### Construction from the pencil geometry

Choose `w in C^d` outside all `ker ell_A` and apply the orbit lemma to

```text
u_A(z)=ell_A(z)/omega_A,
H_A={sum_(v in A)n_v ell_A(a_v)/omega_A mod Z:n in Z^A}.     (17)
```

Condition (3) makes the map `Z^A -> H_A` injective.  Let the resulting periodic entire sources be
`h_A`, and put

```text
Y_A(z)=h_A(u_A(z)),
F(z)=sum_(A in Fac(Delta))Y_A(z).                            (18)
```

For `v notin A`, condition (2) and `1`-periodicity give `T_vY_A=Y_A`.  For the vertices in `A`,
condition (3) and the orbit lemma make all distinct integral translates of `Y_A` jointly
differentially algebraically independent, also jointly across different facets.

For each facet define

```text
rho_A:R -> S[t_v^(+-1):v in A]                              (19)
```

by setting `t_v=1` outside `A`.  Then

```text
P(T)F=sum_A rho_A(P)(T)Y_A.                                 (20)
```

Joint orbit freeness makes (20) vanish exactly when every `rho_A(P)` vanishes.  The localized
facet-prime decomposition gives

```text
ker(product_A rho_A)
 =intersection_A(t_v-1:v notin A)
 =I_Delta,                                                   (21)
```

which proves (8).

For finitely many `P_i`, expand (20) in its finite free orbit support.  The coefficient matrix is
over the Euclidean domain `C[delta]`.  Smith normal form reduces it to nonzero diagonal
differential operators on independent differential indeterminates; the leading-jet term of each
nonzero operator preserves differential transcendence.  Its row rank is the rank of the classes
`Pbar_i` under the injection in (21).  This proves (9). `QED`

## Relation to faithful hyperplane dimension `[PROVED HERE]`

Every faithful facet separation in dimension `d` gives a periodic-pencil separation in dimension
`d`.  For each facet, retain `ell_A` and choose `omega_A` outside the `Q`-span of its finitely many
nonzero facet values.  Complement values are zero and (3) holds.  Therefore

```text
ppDim(Delta)<=ffsDim(Delta)<=min(|V|,|Fac(Delta)|).          (22)
```

The first inequality can be strict because distinct parallel leaves in (4) are analytically
identified by a periodic source even though no single hyperplane contains them.

## Exact dimension-one phase law `[PROVED HERE]`

Let `Delta` be a complex on a nonempty essential vertex set `V`.  The following are equivalent:

```text
(i)  peDim(Delta)=1;
(ii) htDim(Delta)=1;
(iii) ppDim(Delta)=1;
(iv) Delta is the full simplex, or there is a nonempty U subset V with
     Fac(Delta)={V\{u}:u in U};
(v)  I_Delta=0, or I_Delta=(prod_(u in U)(t_u-1)) for one nonempty U.       (D1)
```

### Necessity

If `peDim(Delta)=1`, every facet complement is contained in a closed subgroup `P_A subset C` with
noncompact quotient.  Its identity component cannot be `C`, so `P_A` is discrete.  A discrete
subgroup of `C` of rank two is a full lattice with compact elliptic quotient; hence `P_A` has
`Z`-rank at most one.  The globally `Q`-independent translation steps in `V\A` all lie in `P_A`, so

```text
|V\A|<=1 for every facet A.                                 (D2)
```

The same conclusion follows directly from a one-dimensional periodic-pencil separation, since
the nonzero form `ell_A:C->C` is injective and maps all complement steps into the one-dimensional
`Q`-space `omega_A Q`.  It follows from the period-escape inequality
`peDim<=htDim<=ppDim` for either of the other dimension-one hypotheses as well.

If `V` itself is a facet, it is the unique facet and `Delta` is the full simplex.  Otherwise every
facet is `V\{u}` for a vertex `u`; writing `U` for the nonempty set of omitted vertices gives (iv).
A set is then a face exactly when it omits an element of `U`, so `U` is the unique minimal nonface
and (v) follows.

### Sufficiency and sharpness

Choose `Q`-linearly independent nonzero numbers `(a_v)_(v in V)`.

If `Fac(Delta)={V\{u}:u in U}`, use `ell_u(z)=z` and `omega_u=a_u`.  The complement value is one
period, and

```text
{1} union {a_v/a_u:v!=u}                                   (D3)
```

is `Q`-linearly independent: multiplication by `a_u` gives the original independent family
`{a_v:v in V}`.  This is a periodic-pencil separation in `C`.

For the full simplex, use its sole facet `V`, take `ell(z)=z`, and choose `omega` outside the
`Q`-span of the finite family `(a_v)`.  Then `{1} union {a_v/omega}` is independent.  The
periodic-pencil realization theorem supplies in both cases an entire one-variable HT system with
the exact annihilator and full nonlinear matroid.  Thus (iv) implies `ppDim=htDim=1`, and its period
groups give `peDim=1`.  This proves (D1).

Faithful single-hyperplane dimension has a sharper boundary:

```text
ffsDim(Delta)=1 iff Delta is the full simplex.               (D4)
```

Indeed, a nonzero linear form on `C` cannot vanish on a nonzero translation step, so a faithful
one-dimensional facet can have no complement.  Conversely the full simplex is immediate.  Hence
periodicity is not a technical convenience even in dimension one: its cyclic leaves realize every
nonzero principal squarefree ideal that a single hyperplane cannot.

## The nonpure two-thick wedge has periodic-pencil dimension two `[PROVED HERE]`

Let `Delta_wedge` have vertices `{0,1,2,3,4,5}` and facets

```text
{0,1}, {1,2}, {2,0},
{0,3,4}, {0,3,5}, {0,4,5}, {3,4,5}.                         (23)
```

This is the connected nonpure two-thick complex `S^1 wedge S^2`.

Let `e_1,e_2` be the standard basis of `C^2` and define

```text
a_0=pi^3 e_1+pi^2 e_2,
a_1=e_2,                 a_2=pi e_2,
a_3=e_1,                 a_4=pi e_1,        a_5=pi^2 e_1.  (24)
```

These six vectors are `Q`-linearly independent.  The first coordinate of a rational relation,
using the transcendence of `pi`, first kills the coefficients of `a_0,a_3,a_4,a_5`; the second
then kills those of `a_1,a_2`.

For the three edge facets use `ell_E(z)=z_2`, with periods

```text
omega_{01}=pi,   omega_{12}=pi^2,   omega_{20}=1.            (25)
```

The complement of each edge consists of the three `e_1`-axis vertices and respectively
`a_2,a_0,a_1`.  Its values under `ell_E` are therefore `0` or one copy of the displayed period.
The normalized values on the two vertices of the edge, together with `1`, are respectively

```text
{1,pi,pi^(-1)},
{1,pi^(-2),pi^(-1)},
{1,pi,pi^2}.                                                 (26)
```

Each family is `Q`-linearly independent after multiplication by a power of `pi`.

For the four triangular facets use `ell_S(z)=z_1`, with periods

```text
omega_{034}=pi^2,   omega_{035}=pi,
omega_{045}=1,      omega_{345}=pi^3.                       (27)
```

For the first three facets, the complement is `{1,2}` together with respectively `a_5,a_4,a_3`;
for the last it is `{0,1,2}`.  Again every complement value is `0` or one copy of its displayed
period.  In every case the normalized facet values together with `1`, after multiplication by a
power of `pi`, are exactly the four powers

```text
{1,pi,pi^2,pi^3},                                           (28)
```

up to reordering.  They are `Q`-linearly independent.  Thus `ppDim(Delta_wedge)<=2`.

Dimension one is impossible already from an edge complement.  In `C`, a nonzero complex-linear
form is injective.  Condition (2) would send the four `Q`-independent complement vectors into the
one-dimensional `Q`-space `omega_A Q`, contradicting their independence.  Hence

```text
ppDim(Delta_wedge)=2.                                       (29)
```

## Intrinsic HT realization dimension is exactly two `[PROVED HERE]`

Define `htDim(Delta)` to be the least `d` for which a scalar meromorphic function on `C^d`, under
`Q`-independent additive translation vectors and one constant directional derivation, satisfies
the exact annihilator identity (8) and the full nonlinear matroid identity (9).

The periodic-pencil realization gives

```text
htDim(Delta)<=ppDim(Delta).                                  (30)
```

The exact dimension-one phase law (D1), proved above, shows that `htDim(Delta)=1` exactly when every
facet complement has cardinality at most one.  The edge facets of `Delta_wedge` have complements
of cardinality four, so

```text
htDim(Delta_wedge)>=2.                                      (31)
```

The companion paper proof
`faithful-facet-separation-dimension-ht-realization.md` proves the faithful value four: its explicit
four-dimensional coordinates give the upper bound, while for `L=span_C{a_3,a_4,a_5}` any faithful
realization in dimension at most three has a contradiction whether `dim L>=2` or `dim L<=1`.
Combining that theorem with (29)--(31) gives the strict dimension law

```text
htDim(Delta_wedge)=ppDim(Delta_wedge)=2
                  < ffsDim(Delta_wedge)=4.                  (32)
```

Thus the intrinsic analytic cost of this nonpure two-thick geometry is two complex variables, not
four.  The lost two dimensions are exactly recovered by allowing a facet complement to occupy
several leaves of a cyclic period pencil instead of forcing it into one hyperplane.

## Scientific meaning and RH-facing consequence

The new object is the dimension geometry in (32), not periodic functions, Baire interpolation,
Stanley--Reisner decomposition, or the individual two-axis coordinates.  Those are contributing
parts.  The geometric law is that exact HT constraint geometry measures directions only after
quotienting by the carrier's period lattice.  Hyperplane dimension can therefore overcount the
intrinsic HT dimension.

The positive RH-facing requirement is now sharper: a nonpure prime/Euler relation complex must
carry at least two analytic directions, but those directions may be realized as transverse cyclic
period pencils rather than four independent linear coordinates.  Any proposed route that sees
only one scalar analytic clock must become pure and principal; any viable nonpure route must expose
at least a second analytic direction or an equivalent periodic-pencil quotient.  No assertion that
the zeta function supplies such a pencil is made here.

For a finite prime set `P`, the horizontal steps `(log p)_(p in P)` are `Q`-linearly independent:
after clearing denominators, a rational relation would give an integer relation among prime powers,
and unique factorization kills every exponent.  Therefore the dimension-one phase law applies
without a genericity assumption.  Any scalar meromorphic prime-translation carrier that realizes a
full exact Stanley--Reisner matroid must have

```text
I=(product_(p in U)(T_(log p)-1))                            (RH1)
```

for one finite prime subset `U`, or `I=0`.  This is the positive scalar route normal form: every
facet omits exactly one prime from `U`.  A route requiring two incomparable forbidden prime blocks,
mixed circuit degrees, or nonpure prime compatibility must construct a second analytic escape
coordinate, a vector/sheaf equivalent, or a non-additive action whose stabilizers are not scalar
period lattices.  The theorem constrains the form of a successful route; it does not assert that a
zeta-derived carrier satisfies the full-matroid hypothesis.

## Parent and novelty boundary

- The generic periodic-source lemma is a cylinder version of standard Baire--Runge jet
  interpolation and of the project's fixed-divisor orbit-freeness method.
- The exact kernel uses the classical localized facet-prime decomposition of a Stanley--Reisner
  ideal; the nonlinear rank step uses Smith normal form.
- Periodic meromorphic functions on `C^d/Gamma` and their quasi-Abelian reductions are classical;
  Capocasa--Catanese characterize when a discrete period group supports a nondegenerate meromorphic
  function.
- The candidate-new content is the periodic-pencil invariant, its exact HT realization theorem,
  and the strict intrinsic dimension computation `2<4` for the first connected nonpure two-thick
  relation geometry.  Exact and adjacent searches found hyperplane-arrangement and hypergraph
  representation dimensions, but no representation invariant using cyclic parallel-leaf pencils
  to compute the full nonlinear Stanley--Reisner differential matroid.

Novelty remains provisional pending independent specialist comparison with gain-graph, toric-
arrangement, arithmetic-matroid, and hypergraph representation dimensions.

The closest primary theories checked are:

1. F. Capocasa and F. Catanese, *Periodic meromorphic functions*, Acta Math. **166** (1991),
   27--68, DOI `10.1007/BF02398883`.  Their generalized Riemann relations and quasi-Abelian
   reduction classify period groups and periodic meromorphic functions, not facet-indexed
   simplicial relation geometry or its differential matroid.
2. M. D'Adderio and L. Moci, *Arithmetic matroids, the Tutte polynomial and toric arrangements*,
   Adv. Math. **232** (2013), 335--367, DOI `10.1016/j.aim.2012.09.001`.  Arithmetic matroids encode
   ranks and lattice multiplicities of one list in a finitely generated abelian group.  They do not
   define the facetwise periodic-pencil minimum (5) or realize a Stanley--Reisner differential
   matroid by HT sources.
3. D. Forge and T. Zaslavsky, *Lattice point counts for the Shi arrangement and other
   affinographic hyperplane arrangements*, J. Combin. Theory Ser. A **114** (2007), 97--109, DOI
   `10.1016/j.jcta.2006.03.006`.  Gain-labelled affine hyperplanes encode balanced-cycle and
   coloring combinatorics, not the exact facet-complement/inside dichotomy (2)--(3).

## Gates

- [x] periodic-pencil facet dimension defined
- [x] generic non-Gamma periodic orbit lemma proved
- [x] exact Stanley--Reisner kernel proved
- [x] full nonlinear differential matroid proved
- [x] comparison `ppDim<=ffsDim` proved
- [x] explicit two-dimensional wedge representation proved
- [x] dimension-one periodic-pencil impossibility proved
- [x] intrinsic equality `htDim=2` proved using scalar purity
- [x] strict geometry gap `htDim=ppDim=2<ffsDim=4` proved
- [ ] independent specialist proof and novelty audit
- [ ] complete unconditional Lean formalization before stage 3
