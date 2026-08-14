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

## Lean formalization status

`GaloisForLFunctions/HTGeometry/PPMatrixRankFormula.lean` formalizes the invariant and its exact
matrix-rank formula.  `PPMatrixRankFormulaConsequences.lean` now additionally formalizes the full
finite-dimensional wedge computation: the explicit two-coordinate pencil, its PP-admissibility,
the dimension-one obstruction, and `boundaryWedge_ppDim_eq_two` uniformly for all boundary wedges
with `r,s>=2`.  The exact faithful value four is formalized separately in
`WedgeFacetLowerBound.lean`.

The card remains at stage 2 because its generic Baire--Runge periodic-source theorem, exact
Stanley--Reisner differential-matroid realization, and the analytic definition and lower bound for
`htDim` are still paper-level.  The exact `ppDim=2` result is no longer part of that gap.

## Gates

- [x] periodic-pencil facet dimension defined
- [x] generic non-Gamma periodic orbit lemma proved
- [x] exact Stanley--Reisner kernel proved
- [x] full nonlinear differential matroid proved
- [x] comparison `ppDim<=ffsDim` proved
- [x] explicit two-dimensional wedge representation proved
- [x] dimension-one periodic-pencil impossibility proved
- [x] exact boundary-wedge `ppDim=2` formalized unconditionally in Lean
- [x] intrinsic equality `htDim=2` proved using scalar purity
- [x] strict geometry gap `htDim=ppDim=2<ffsDim=4` proved
- [ ] independent specialist proof and novelty audit
- [ ] complete unconditional Lean formalization before stage 3

## Lean progress — the exact Stanley--Reisner kernel `(8)`, with an explicit source

`GaloisForLFunctions/HTGeometry/PencilExponentialSeed.lean` and
`GaloisForLFunctions/HTGeometry/PencilSRRealization.lean` (axiom-clean, build green,
umbrella-registered) formalize the annihilator statement `(8)` unconditionally, and replace the
generic Baire--Runge source by an explicit one for that half of the theorem.

**The datum.**  `PencilSeparation facets E` packages exactly conditions `(2)`--`(3)` in exponentiated
form: steps `ω : α → E`, one additive phase `L_A : E →+ ℂ` per facet (`L_A = 2πi·ell_A/omega_A`), with

- `phase_surjective` — each `L_A` covers `ℂ` (automatic for a nonzero linear form);
- `outside` — `exp (L_A (ω v)) = 1` for `v ∉ A`, i.e. `(2)`;
- `inside` — `exp(∑_{v ∈ A} g_v L_A (ω v)) = 1` with `g ∈ ℤ^A` forces `g = 0`, i.e. `(3)`.

**The source.**  `PencilSeparation.seed S z = ∑_{A ∈ Fac} exp (exp (L_A z))`, one exponential seed per
facet.  It is entire whenever the phases are (`differentiable_seed`), so no Runge approximation and
no Fréchet-space parameter is used.

**The kernel, both inclusions.**

- `seedAnnihilates` — every nonface product of difference operators annihilates the source: a nonface
  escapes every facet, and the escaping step is a period of that facet's seed.  This is
  `I_Δ ⊆ Ann(F)`.
- `exists_ne_seedCarrierPoly` — conversely, a polynomial whose carrier is **constant** lies in
  `I_Δ`.  The proof isolates one facet by multiplying by one escaping variable per *other* facet
  (available because the facets form an antichain), uses that `exp ∘ L_A` covers `ℂ∖{0}` to force
  every positive-level Taylor coefficient of the surviving dilate combination to vanish, and reads
  those coefficients as the *symbols* `P(exp(m·L_A(ω v)) − 1)`.  Condition `inside` makes the symbol
  nodes `∏_v exp(L_A(ω v))^{ν_v}` pairwise distinct on exponents supported in `A`, so a Vandermonde
  induction kills every coefficient supported in `A`; as `A` ranges over the facets this says exactly
  that every monomial of `P` has nonface support.

Together these give `Ann(F) = I_Δ` in the difference-operator ring `ℂ[X_v]`, `X_v ↦ T_{ω v} − 1` —
statement `(8)` with constant coefficients, and in the sharper form "constant carrier, not merely
zero carrier".

- `entireSRRealization` — consequently a periodic-pencil separation in `d` variables produces an
  `EntireSRRealization d` of the complex: entire carriers, vertex coordinates acting as difference
  operators along `ℚ`-independent steps, nonconstant carriers for nonzero classes.  This is
  `htDim ≤ ppDim` in the entire/nonconstant realization sense, for **every** complex, not only the
  boundary wedge.

**What is still paper-level.**  The differential-matroid statement `(9)` — the transcendence-degree
formula over `D = ℂ(z₁,…,z_d)` with the derivation `δ = D_w` — is untouched: it needs the orbit
lemma `(11)` in its full joint-differential-independence form, not only the annihilator.  The
explicit source above is differentially algebraic (`exp∘exp` satisfies `y y'' − y y' − y'² = 0`), so
it cannot serve `(9)`; what it shows is that `(8)` never needed genericity.

## Lean progress — the exact dimension-one phase law `(D1)`

`GaloisForLFunctions/HTGeometry/PPDimensionOnePhaseLaw.lean` (axiom-clean, build green,
umbrella-registered) formalizes both directions of the `ppDim = 1` equivalence, for the corpus's
`ppDim` of `PPMatrixRankFormula.lean`.

**Necessity `(D2)`.**  `card_sdiff_le_one_of_ppAdmissible_one`: a one-dimensional admissible
configuration forces every facet complement to have at most one vertex.  In dimension one the facet
form is multiplication by a single scalar `c = U B 0`; a nonempty facet makes `c ≠ 0`, because the
`ℚ`-independent family of `(3)` contains `c · a_{v₀}` and hence cannot vanish.  Two distinct omitted
vertices `v, v'` then satisfy `c·a_v = n`, `c·a_{v'} = n'` with `n, n' ∈ ℤ`, and the rational
combination `n' a_v − n a_{v'}` vanishes; `ℚ`-independence of the steps forces `n = n' = 0`, whence
`a_{v'} = 0`, contradicting independence again.

`facetComplementRankOne_of_ppAdmissible_one` restates this as
`FacetComplementRankOne univ (Set.range faces)`, which is exactly the hypothesis of the corpus's
`facetAntichain_eq_singleton_or_deletionFacets`; composing the two gives the classification
`(iii) ⇒ (iv)`: the family is `{V}` or a deletion family `{V∖{u} : u ∈ U}`.

**Sufficiency.**  Both surviving families are realized in dimension one by the powers of one
transcendental number, with the injective positive labelling `vertexExponent` of the vertex type:

- `ppDim_le_one_deletion` — for `faces B = V∖{u B}` take `a_v = τ^{e(v)}` and the facet form
  `(τ^{e(u B)})⁻¹`.  The single omitted vertex evaluates to `1 ∈ ℤ`, and multiplying the family
  `{1} ∪ {τ^{e(v)−e(u B)} : v ≠ u B}` by `τ^{e(u B)}` turns it into distinct powers of `τ`, so it is
  `ℚ`-independent.
- `ppDim_le_one_simplex` — for the sole facet `V` take the same steps and the facet form `1`; the
  complement is empty and the family `{τ⁰} ∪ {τ^{e(v)}}` is again a family of distinct powers
  because `e` is positive.

This closes `(D1)` in the form the corpus's `ppDim` expresses, uniformly in the vertex and facet
index types.  What `(D1)` still borrows from paper level is only the chain
`peDim ≤ htDim ≤ ppDim`, i.e. the equivalences `(i) ⟺ (ii) ⟺ (iii)`, which quantify over the
analytic dimensions rather than the pencil one.

## Lean progress — a pencil realizes its complex, and `htDim <= ppDim`

`GaloisForLFunctions/HTGeometry/PencilFromPPAdmissible.lean` (axiom-clean, build green,
umbrella-registered) closes the loop between the matrix form of `ppDim` and the analytic realization.

An admissible configuration `(a, U)` of `PPMatrixRankFormula` *is* a periodic-pencil separation:

- `facetForm (U B) z = 2πi ∑ᵢ U B i · zᵢ` is the additive phase of the facet, `ℂ`-linear, entire, and
  surjective whenever `U B ≠ 0` — which the `ℚ`-independence of `(3)` forces as soon as the facet is
  nonempty, since the family it constrains contains the value `M B v₀`;
- the integrality condition `(2)` says exactly `exp (L_B (a v)) = 1` for `v ∉ B`;
- the `ℚ`-independence `(3)` of `{1} ∪ {M B v : v ∈ B}` says exactly that
  `exp (∑_{v ∈ B} g_v L_B (a v)) = 1` with integer `g` forces `g = 0`: exponentiating turns the
  relation into `∑_v g_v M B v = k ∈ ℤ`, which is a rational relation of the constrained family with
  the coefficient `−k` on the entry `1`.

`pencilOfPPAdmissible` assembles this into a `PencilSeparation` on the facet family
`facetFinset faces = image faces univ`, choosing one representing index per facet.  Feeding it to
`PencilSeparation.entireSRRealization` gives:

- **`entireSRRealization_of_ppAdmissible`** — a periodic-pencil separation in dimension `d` produces
  an entire `d`-variable Stanley–Reisner realization of the complex, for every facet antichain with
  nonempty facets;
- **`srDim_le_of_ppAdmissible`** and **`srDim_le_ppDim`** — hence the intrinsic realization
  dimension `srDim = sInf {d | realizable}` satisfies `srDim ≤ d` for every admissible dimension `d`,
  and `srDim ≤ ppDim` whenever the periodic-pencil dimension is attained.

This is the card's `htDim ≤ ppDim` for **every** complex, in the entire/nonconstant realization
sense, with no genericity: the source is the explicit facet-indexed exponential seed of `(21)`.

## Lean progress — the linear layer of the differential matroid `(9)`

`GaloisForLFunctions/HTGeometry/PencilLinearMatroid.lean` (axiom-clean, build green,
umbrella-registered) records what the exact kernel gives at the level of `ℂ`-coefficients.

Since the carrier assignment is `ℂ`-linear and, by the kernel theorem, only the zero class has
constant carrier, the induced map

```text
ℂ[x_v]/I_Δ  ⟶  {functions}/{constants},   q ↦ P(T)F  mod constants
```

is injective (`seedCarrierQuot_ker_eq_bot`, `seedCarrierQuot_injective`).  Consequently
`linearIndependent_seedCarrierQuot`: a `ℂ`-linearly independent family of Stanley--Reisner classes
has `ℂ`-linearly independent carriers modulo constants, so the span of finitely many carriers has
exactly the dimension of the span of their classes.  `eq_of_seedCarrier_sub_const` is the pointwise
form: two classes whose carriers differ by a constant are equal.

That is `(9)` with `ℂ` in place of `ℂ(δ)`.  The differential layer does **not** follow from this
source and cannot: `exp∘exp` satisfies `y y'' − y y' − y'² = 0`, so every carrier built here is
differentially algebraic and the differential transcendence degree of any finite family of them is
zero, whereas `(9)` predicts `dim span{P̄ᵢ}`.  The genuine remaining content of `(9)` is therefore
exactly the orbit lemma `(11)`: a source whose translation orbit is differentially independent.  The
kernel `(8)`, the dimension comparison `htDim ≤ ppDim`, the dimension-one phase law `(D1)`, and the
linear matroid are now all independent of it.

## Lean progress — exponential sums with polynomial coefficients

`GaloisForLFunctions/HTGeometry/ExponentialPolynomialVandermonde.lean` (axiom-clean, build green,
umbrella-registered) proves the separation theorem that upgrades the symbol argument from `ℂ` to
`ℂ[δ]` coefficients:

> **`expPolySum_eq_zero`.**  If `∑_{i ∈ S} p_i(m) · z_i^m = 0` for every `m ≥ 1`, with the nodes
> `z_i` pairwise distinct and nonzero and the `p_i` polynomials, then every `p_i = 0`.

Mechanism.  Subtracting `z_a` times the `m`-th equation from the `(m+1)`-st replaces `p_i` by
`vandermondeStep p_i z_i z_a = p_i(X+1)·z_i − z_a·p_i`.  Off the distinguished node this preserves
the degree, because the leading coefficient is scaled by `z_i − z_a ≠ 0`
(`polyWeight_vandermondeStep_of_ne`); at the distinguished node the leading terms cancel and the
degree strictly drops (`polyWeight_vandermondeStep_self_lt`, via `degree_sub_lt` applied to
`p(X+1)` and `p`, which share degree and leading coefficient).  So the weight
`∑_i (deg p_i + 1)`, with the zero polynomial weighing nothing, strictly decreases and the induction
closes; the surviving distinguished polynomial then vanishes at every positive integer, hence is
zero.

Why this is the right tool for `(9)`.  The directional derivation `δ = D_w` acts on the pencil
carrier `Ψ(exp(L_A z))` by `Ψ'(exp(L_A z))·exp(L_A z)·L_A(w)`, i.e. it multiplies the `m`-th Taylor
coefficient of `Ψ` by `m·L_A(w)` — diagonally.  So an operator `𝒟 ∈ ℂ[δ][x_v]` multiplies that
coefficient by `∑_r c_r (m L_A(w))^r · symb_A(m, P_r)`, a *polynomial in `m`* times the node power.
The theorem above is exactly what turns the vanishing of all those coefficients into the vanishing
of each `P_r`, which is the `ℂ[δ]`-row-rank statement inside the card's Smith-normal-form argument
for `(9)`.  Only the last step of `(9)` — "the leading jet of each nonzero diagonal operator
preserves differential transcendence" — then still needs the orbit lemma `(11)`.

## Lean progress — the derivation acts diagonally

`GaloisForLFunctions/HTGeometry/EulerOperatorDiagonal.lean` (axiom-clean, build green,
umbrella-registered) supplies the second half of the `ℂ[δ]` upgrade: the fact that the pencil's
directional derivation is *diagonal* on the inner Taylor coefficients.

Along a facet phase the carrier is `Ψ(exp (L z))`, and the chain rule turns `δ = D_w` into
`L(w)` times the Euler operator `Θ Ψ (u) = u · Ψ'(u)` on the inner variable.  On coefficients `Θ` is
multiplication by the index:

- **`iteratedDeriv_id_mul`** — the Leibniz identity `(u·g)⁽ⁿ⁺¹⁾ = u·g⁽ⁿ⁺¹⁾ + (n+1)·g⁽ⁿ⁾`, proved by
  induction with `HasDerivAt` (the `fun`-shaped product and sum rules, since the `Pi`-shaped
  `deriv_mul`/`deriv_add` do not match the required syntactic form);
- **`iteratedDeriv_eulerOp_zero`** — hence `(ΘΨ)⁽ᵐ⁾(0) = m · Ψ⁽ᵐ⁾(0)`, the first term of the Leibniz
  identity dying at the origin;
- **`iteratedDeriv_eulerOp_iterate_zero`** — hence `(Θ^r Ψ)⁽ᵐ⁾(0) = m^r · Ψ⁽ᵐ⁾(0)`;
- `contDiff_iteratedDeriv`, `differentiable_iteratedDeriv`, `contDiff_eulerOp` — the smoothness
  bookkeeping that lets the induction and the iteration run.

Together with `expPolySum_eq_zero` this is the complete toolkit for the `ℂ[δ]`-coefficient kernel: an
operator `𝒟 = ∑_r δ^r P_r(T)` multiplies the `m`-th inner coefficient of the isolated facet carrier
by `∑_r (m·L_A(w))^r · symb_A(m, P_r)`, which is a polynomial in `m` against the node power `Z_ν^m`,
and the separation theorem then forces each `P_r` into the ideal — provided `L_A(w) ≠ 0`, i.e. the
card's requirement that `w` lie outside every `ker ell_A`.

## Lean progress — the directional derivation of a pencil carrier

`GaloisForLFunctions/HTGeometry/PencilDirectionalDerivation.lean` (axiom-clean, build green,
umbrella-registered) is the bridge between the card's derivation `δ = D_w` and the diagonal action
established in the previous module.

- `dirDeriv w f z = deriv (fun t => f (z + t·w)) 0` — the derivation of `(9)`;
- `phaseComp L Ψ = fun z => Ψ (exp (L z))` — the shape of every pencil carrier along a facet phase;
- **`dirDeriv_phaseComp`** — `D_w (Ψ ∘ exp ∘ L) = (L w) · (Θ Ψ) ∘ exp ∘ L`.  Writing
  `L (z + t·w) = L z + t·(L w)` splits the inner exponential as
  `exp (L z) · exp (t · L w)`, whose `t`-derivative at `0` is `exp (L z) · L w`; the chain rule then
  produces exactly `L w` times the Euler operator;
- **`dirDeriv_iterate_phaseComp`** — iterating gives `(L w)^r · Θ^r`, using that scaling passes
  through the Euler operator (`eulerOp_const_mul`);
- **`iteratedDeriv_inner_dirDeriv_iterate`** — hence the `m`-th inner Taylor coefficient of an
  `r`-fold directional derivative is `(m · L w)^r` times the original one.

The two halves of the `ℂ[δ]` symbol calculus are therefore in place: `δ` acts on the inner
coefficient of index `m` by the scalar `m · L_A(w)`, and `expPolySum_eq_zero` separates node powers
carrying polynomial-in-`m` coefficients.  The remaining assembly is bookkeeping: run the facet
isolation of `PencilSRRealization` with an operator `𝒟 = ∑_r δ^r P_r(T)` in place of a single
polynomial, read off the coefficient identity `∑_ν p_ν(m) Z_ν^m = 0` with
`p_ν(X) = ∑_r c_{r,ν} (L_A w)^r X^r`, and conclude `P_r ∈ I_Δ` for every `r` — valid exactly when
`L_A(w) ≠ 0`, the card's condition that `w` avoid every `ker ell_A`.

## Lean progress — the derivation against the shift algebra

`GaloisForLFunctions/HTGeometry/PencilDerivationPlumbing.lean` (axiom-clean, build green,
umbrella-registered) supplies the structural facts about `δ = D_w` that the `ℂ[δ]`-coefficient
argument consumes.

- `differentiable_line`, `differentiableAt_comp_line` — restricting an entire function to a line in
  a fixed direction is differentiable, which is the side condition every derivative rule below
  needs;
- `dirDeriv_const`, `dirDeriv_add`, `dirDeriv_const_mul`, `dirDeriv_sum` — the derivation kills
  constants and is `ℂ`-linear, including over finite sums;
- **`dirDeriv_shiftAlgHom`** — `D_w` commutes with every element of the difference-operator algebra.
  Writing `shiftAlgHom a f z = ∑_γ a_γ f (z + γ)` and reassociating `z + t·w + γ = (z + γ) + t·w`,
  the derivative passes through the finite sum term by term;
- `contDiff_dilateSumHom`, `differentiable_dilateSumHom'` — a dilate combination is smooth, being a
  finite sum of `c · exp (g · u)`.

With these, an operator `𝒟 = ∑_r δ^r P_r(T)` can be pushed through the facet isolation of
`PencilSRRealization`: the difference operator that isolates a facet commutes past every `δ^r`, the
sum over `r` splits, and each summand is a `phaseComp` to which
`dirDeriv_iterate_phaseComp` applies.  The remaining step is the coefficient bookkeeping that feeds
`expPolySum_eq_zero`.

## Lean progress — iterated derivations of a pencil carrier

Two further modules (both axiom-clean, build green, umbrella-registered).

`GaloisForLFunctions/HTGeometry/PencilIteratedDerivation.lean`:

- `contDiff_eulerOp_iterate` — iterates of the Euler operator stay smooth;
- `differentiable_linearMap`, `differentiable_phaseComp` — a linear form on `ℂ^d` is differentiable
  (through `LinearMap.toContinuousLinearMap`), hence so is every phase composite;
- `dirDeriv_phaseComp_scaled` — one derivation step on an already scaled composite, obtained from
  the iteration lemma rather than by repeating its computation;
- **`dirDeriv_iterate_sum_phaseComp`** — an `r`-fold derivation of a *finite sum* of phase
  composites is again such a sum, with inner functions `(L_i w)^r · Θ^r`.

`GaloisForLFunctions/HTGeometry/PencilOperatorKernelCore.lean`:

- `iteratedDeriv_finset_sum` — iterated derivatives commute with finite sums;
- **`seedCarrierPoly_eq_sum_phaseComp`** — a pencil carrier *is* a sum of phase composites, one per
  facet, with inner function the dilate combination of the polynomial's operator;
- **`dirDeriv_iterate_seedCarrierPoly`** — hence every iterated derivative of a carrier is again
  such a sum, explicitly;
- `differentiable_dirDeriv_iterate_seedCarrierPoly` — consequently every iterated derivative of a
  carrier is entire.  This is the fact that makes the next step legitimate without any
  several-variable analyticity theory: the iterates are *explicitly* sums of composites, not merely
  abstract derivatives;
- **`dirDeriv_iterate_shiftAlgHom`** — iterated derivations commute with the whole shift algebra.

Together these let the facet isolation of `PencilSRRealization` be applied to an operator
`𝒟 = ∑_r δ^r P_r(T)`: the isolating difference operator can be moved across every `δ^r`, and after
isolation the object is a single phase composite whose inner function is
`∑_r (L_A w)^r · Θ^r (Ψ_{A, D·P_r})`.  Its `m`-th derivative at the origin is
`∑_r ((m·L_A w))^r · symb_A(m, D·P_r)`, which is what `expPolySum_eq_zero` consumes.

## Lean progress — the operator symbol identity

`GaloisForLFunctions/HTGeometry/PencilOperatorSymbol.lean` (axiom-clean, build green,
umbrella-registered) runs the facet isolation with a full operator
`𝒟 = ∑_{r<n} δ^r P_r(T)` and extracts the symbol identity.

- `inner_iteratedDeriv_eq_zero_of_const` — if a phase composite `Ψ ∘ exp ∘ L` is constant and `L` is
  onto, then `exp ∘ L` covers `ℂ∖{0}`, so `Ψ` is constant on the punctured plane, hence entire and
  constant, hence all its Taylor coefficients of positive order vanish.
- **`symbHom_combination_eq_zero`** — if
  `∑_{r<n} δ_w^r (P_r(T) F)` is constant, then for every facet `A` and every `m ≥ 1`

  ```text
  ∑_{r<n} (m · L_A w)^r · symb_A(m, P_r) = 0.
  ```

The proof chains the whole apparatus built above: choose one escaping vertex per other facet
(antichain) and multiply by their product `D`; the shift operator commutes with every `δ^r`
(`dirDeriv_iterate_shiftAlgHom`, whose differentiability side condition is supplied by
`differentiable_dirDeriv_iterate_seedCarrierPoly`), so the shifted operator carrier is still
constant; isolation collapses it to a single phase composite with inner function
`∑_r (L_A w)^r · Θ^r (Ψ_{A, D·P_r})`; the coefficient extraction uses `iteratedDeriv_finset_sum`,
`iteratedDeriv_const_mul'`, `iteratedDeriv_eulerOp_iterate_zero` and
`iteratedDeriv_dilateSumHom_zero`; and finally the symbol of `D` — a product of factors
`exp(m·L_A(ω(sel B))) − 1` with `sel B ∈ A` — is nonzero by `ratio_pow_ne_one`, so it divides out.

This is the `ℂ[δ]`-coefficient analogue of the symbol vanishing that drove `(8)`.  What remains for
the `ℂ[δ]`-kernel is purely polynomial bookkeeping: substitute
`symb_A(m, P_r) = ∑_ν coeff ν (Qt_r) · Z_ν^m` over a common exponent set, so the identity becomes
`∑_ν p_ν(m) Z_ν^m = 0` with `p_ν(X) = ∑_r coeff ν (Qt_r) (L_A w)^r X^r`, and apply
`expPolySum_eq_zero`; with `L_A w ≠ 0` this forces every `coeff ν (Qt_r) = 0`, i.e. every
`P_r ∈ I_Δ`.

## Lean progress — the `C[delta]`-coefficient kernel and the operator matroid

`GaloisForLFunctions/HTGeometry/PencilOperatorKernel.lean` and
`GaloisForLFunctions/HTGeometry/PencilOperatorMatroid.lean` (axiom-clean, build green,
umbrella-registered) close the *operator-coefficient* layer of `(9)`: everything in the
Smith-normal-form step of the card's proof except the differential transcendence of the orbit.

**The kernel with derivation coefficients.**

> **`operatorKernel`.**  Let `S` be a periodic-pencil separation on an antichain of facets, `Lin A`
> the linear form of the facet phase, and `w` a direction with `Lin A w != 0` for every facet.  If
> the operator carrier `sum_r delta^r (P_r(T)F)` is constant, then `P_r in I_Delta` for every `r`.

Mechanism, in the exact shape predicted by the previous two modules.  Isolating one facet `A`
(possible because the facets form an antichain) and reading the constancy through
`inner_iteratedDeriv_eq_zero_of_const` gives, at every level `m >= 1`,

```text
sum_r (m·Lin A w)^r · symb_A(m,P_r) = 0.                    (K1)
```

Restricting each `P_r` to `A` and substituting `Y = X+1` turns `symb_A(m,P_r)` into
`eval_(Z^m)(Qt_r)` (`eval_ratio_pow_bind`), whose node expansion `eval_ratio_pow_eq_sum_node`
rewrites `(K1)` over the common exponent set `T = union_r supp(Qt_r)` as

```text
sum_(nu in T) p_nu(m)·Z_nu^m = 0,
p_nu(X) = sum_r coeff_nu(Qt_r)·(Lin A w)^r·X^r.             (K2)
```

The nodes `Z_nu = prod_v ratio_A(v)^(nu_v)` are pairwise distinct and nonzero on exponents supported
in `A` — this is condition `(3)` — so `expPolySum_eq_zero` forces every `p_nu = 0`.  Reading the
`r`-th coefficient of `p_nu` and using `Lin A w != 0` kills every `coeff_nu(Qt_r)`, hence
`Qt_r = 0`, hence `restrictPoly A (P_r) = 0`; as `A` ranges over the facets, every monomial of
every `P_r` has nonface support.

This is the exact `C[delta]`-analogue of the `C`-coefficient kernel: the annihilator of `F` in the
*operator* ring `C[delta][X_v]` is again `C[delta] ⊗ I_Delta`, and the hypothesis is constancy of
the carrier, not vanishing.

**The matroid over the operator ring.**  `PencilOperatorMatroid.lean` reads this across a family.
`operatorFamily_eq` collects powers of `delta`: for `D_i = sum_r c_(i,r) delta^r`,

```text
sum_i D_i (Q_i(T)F) = sum_r delta^r ((sum_i c_(i,r) Q_i)(T)F),   (K3)
```

which needs only linearity of the carrier assignment (`seedCarrierPoly_sum_smul`) and of the
iterated derivation (`dirDeriv_iterate_const_mul`, `dirDeriv_iterate_sum`, whose side conditions are
supplied by `differentiable_dirDeriv_iterate_seedCarrierPoly`).  Feeding `(K3)` to the kernel gives

- **`operatorFamily_kernel`** — a constant `C[delta]`-combination of carriers has every coefficient
  combination `sum_i c_(i,r) Q_i` in `I_Delta`;
- **`operatorFamily_coeff_eq_zero`** — hence if the Stanley--Reisner classes of `Q_1,...,Q_m` are
  `C`-linearly independent, no nonzero `C[delta]`-combination of their carriers is constant.

Equivalently: the `C[delta]`-module map

```text
C[delta] ⊗_C (C[x_v]/I_Delta) --> {entire functions}/{constants}                (K4)
```

is injective.  Since `R/I_Delta = C[delta] ⊗_C (C[t^(+-1)]/I_Delta)` is `C[delta]`-free, `(K4)` is
exactly the statement that the row rank over `C(delta)` of the coefficient matrix of `(20)` equals
`dim_(C(delta)) span{Pbar_i}` — the Smith-normal-form input of `(9)`.

**What `(9)` still needs, exactly.**  Only the last step of the card's argument: that a nonzero
diagonal differential operator applied to an orbit element preserves differential transcendence.
That is the orbit lemma `(11)`, and it is not a formality for this source: `exp∘exp` is
differentially algebraic, so the explicit seed used for `(8)`, `(K1)`--`(K4)` gives differential
transcendence degree zero.  The `C[delta]`-layer is the exact boundary of what a differentially
algebraic source can prove.

## Lean progress — multi-node separation, and the programme for the orbit lemma `(11)`

`GaloisForLFunctions/HTGeometry/ExponentialPolynomialVandermondeMulti.lean` (axiom-clean, build
green, umbrella-registered) proves the multi-index form of the separation theorem:

> **`expPolySumMulti_eq_zero`.**  Let `Z i : Fin r -> C` be tuples of nonzero nodes, pairwise
> distinct as tuples, and let each coefficient be a polynomial expression
> `sum_e a(i,e) prod_s m_s^(e_s)` in `r` integer parameters.  If
> `sum_i (sum_e a(i,e) prod_s m_s^(e_s)) prod_s Z(i,s)^(m_s) = 0` for every tuple `m` of positive
> integers, then every `a(i,e)` vanishes.

The proof peels the last parameter: for fixed values of the first `r` the identity is a one-variable
exponential sum whose nodes are the last coordinates, so `expPolySum_eq_zero` kills the resulting
polynomial; each of its coefficients is an `r`-parameter identity over the fibre of tuples sharing
that last coordinate, and tuples in one fibre are still distinct in their first `r` coordinates.

### Why the orbit lemma needs exactly this

`(11)` asks for entire `1`-periodic `h_j` whose full translation orbits are jointly differentially
independent.  Writing `h_j(u) = H_j(e^(2 pi i u))` and `Y_(j,alpha)(z) = H_j(q_alpha xi_j)` with
`xi_j = e^(2 pi i u_j(z))` and `q_alpha = e^(2 pi i alpha)`, the derivation `delta = D_w` acts on the
`n`-th Taylor coefficient of `H_j` by multiplication by `2 pi i n u_j(w)` — diagonally, exactly as
`EulerOperatorDiagonal.lean` records.  So a differential monomial of degree `D` in the jets of the
orbit expands, for each choice of `D` Taylor indices `n_1,...,n_D`, into

```text
(prod_s a_(n_s) q_s^(n_s) n_s^(m_s)) · e^(2 pi i sum_s n_s u_(j_s)(z)).      (O1)
```

Two facts are needed to conclude, and they are independent of each other.

1. **Character separation.**  Terms with different frequency vectors must not be allowed to cancel.
   Choosing a direction `b` outside countably many real hyperplanes makes the real parts of the
   frequencies of distinct integer vectors pairwise distinct, and then the corpus's
   `PrimeExpLogFiberRigidity.expPoly_rigidity` — finite exponential-polynomial rigidity for shifts
   with pairwise distinct real parts — separates them.  This also disposes of the polynomial
   coefficients coming from `C(z_1,...,z_d)` after clearing denominators.
2. **Orbit separation.**  Terms with the *same* frequency vector but different translates
   `q_alpha` differ only through the factors `q_alpha^(n_s)`; no growth argument can see them,
   because the profile is `|a_n| = exp(-b_n)` with `b_n` superlinear while `log|q|·n` is linear.
   They must be separated arithmetically, by letting the `D` Taylor indices vary independently.
   That identity is exactly `expPolySumMulti_eq_zero`, with node tuple `(q_(alpha_1),...,q_(alpha_D))`
   and polynomial part `prod_s n_s^(m_s)` recording the jet orders.

### The remaining bricks, and the corpus assets that already cover them

- **The source.**  `HTGeometry/BoundedRelationProfileRealization.lean` already constructs, for every
  positive superlinear profile `g`, a private-prime rational profile whose exponential series
  `boundedRelationExponentialFunction` is entire, has **every** Taylor coefficient nonzero, and is
  hypertranscendental **for every algebraic unit-modulus phase sequence**.  Since `q^n · u_n` is
  again an algebraic unit-modulus phase when `q` is an algebraic unit, each individual orbit element
  of such a source is already hypertranscendental in the corpus.  Full support is what `(11)` needs
  in order that no monomial of the expansion `(O1)` be empty.
- **Diagonality of the derivation** — done (`EulerOperatorDiagonal.lean`,
  `PencilDirectionalDerivation.lean`).
- **What is genuinely open**: the passage from "each orbit element is hypertranscendental" to
  "the whole orbit is jointly differentially independent".  The corpus's dominance capstone
  (`BoundedRelationLogMagnitudeHypertranscendence`, `MagnitudeIntegerDominance`) is written for the
  jets of a *single* series; the joint statement needs the same dominance run on the jet ring of a
  family, with the two separations above supplying the coefficient nonvanishing.  This is the one
  remaining mathematical core of `(11)`, and hence of `(9)`.

Note that a Baire-category proof, as on the paper card, is not the route being formalized: the
explicit private-prime profile source replaces genericity here exactly as the exponential seed
replaced it for `(8)`.

### Lean progress — the generic direction, and the reduction structure for `(11)`

`GaloisForLFunctions/HTGeometry/GenericDirectionRatIndependence.lean` (axiom-clean, build green,
umbrella-registered) supplies the first half of the character separation:

> **`exists_direction_ratIndependent_re`.**  If `v_1,...,v_L` are `Q`-linearly independent
> `C`-linear forms on `C^d`, there is a direction `b` with `Re(v_1 b),...,Re(v_L b)` `Q`-linearly
> independent.

Mechanism: for each nonzero rational vector `c` the obstruction locus is the kernel of the real part
of the nonzero form `sum_l c_l v_l`; `reLm_comp_ne_zero` shows that real part is a nonzero real
functional (test at `b` and at `i·b`), so the locus is a proper real subspace and hence Haar-null.
Countably many rational vectors give a null union, and the ambient space is not null.
`intVector_injective_of_ratIndependent` then records the consequence actually used: distinct integer
frequency vectors have distinct real parts, which is precisely the hypothesis of the corpus's finite
exponential-polynomial rigidity theorem `PrimeExpLogFiberRigidity.expPoly_rigidity`.

**The reduction structure this fixes.**  Three points, none of them evident from the card's Baire
proof, now determine the shape of the remaining work.

1. *The base field collapses to one variable.*  With `delta = D_w`, every coordinate transverse to
   `w` is a `delta`-constant, so `C(z_1,...,z_d)` is `C(transverse)(t)` with `delta t = 1`.
   Restricting to a line `z = z_0 + t w` turns `delta` into `d/dt` and any relation over
   `C(z_1,...,z_d)` into one over `C(t)` for the restricted family — which is again a family of the
   same shape, with the transverse data absorbed into the constants `x_j = e^(2 pi i u_j(z_0))`.
   So `(11)` in `d` variables reduces to `(11)` in one variable.
2. *The corpus's apparatus already carries the base variable.*  `FormalMahlerDescent.formalJets n F
   = Fin.cons X (jets of F)` puts the point slot `X` alongside the jets, so
   `Hypertranscendental` is hypertranscendence over `C(z)`, not over `C`.  Polynomial coefficients
   are therefore not an extra obstacle; what is missing is only the *family* jet vector
   `Fin 1 (+) (iota x Fin (n+1))`.
3. *The two separations are genuinely different problems.*  Distinct frequency vectors are separated
   by growth (dominance) or by `expPoly_rigidity` after choosing `b` as above.  Equal frequency
   vectors with different translates `q_alpha` can **never** be separated by growth: the profile is
   `|a_n| = exp(-b_n)` with `b_n` superlinear while `log|q|·n` is only linear, so all translates of
   one source share a magnitude profile to leading order.  They are separated only by letting the
   Taylor indices vary independently, which is `expPolySumMulti_eq_zero`.

The single remaining core is therefore: run the corpus's magnitude-dominance capstone on the jet
ring of a *family* of dilated sources, with `expPolySumMulti_eq_zero` supplying the nonvanishing of
the surviving coefficient.  Everything else `(11)` needs is now in the tree.

### Lean progress — magnitude survival for a family of dilated sources

Three modules (axiom-clean, build green, umbrella-registered) build the jet apparatus that the joint
orbit lemma needs.  The corpus's magnitude machinery is written for the jets of a *single* series;
these lift it to the dilates `H(q_i X)` of one source, which is exactly the shape of a translation
orbit `h(u(z)+alpha)` after the substitution `xi = e^(2 pi i u(z))`, `q_alpha = e^(2 pi i alpha)`.

**`FamilyJetFlattening.lean`.**  `flatIndex` flattens an exponent profile on *any* finite variable
type, remembering which variable each slot came from — the corpus's `flatOrder` is the case of a
single series, where only the derivative order needs remembering.  `prod_pow_eq_flatIndex` and
`coeff_prod_iterate_deriv_family` (the antidiagonal convolution for a product of derivatives of
*different* series) then give `familyJets` and the shifted coefficient of one of its monomials.

**`FamilyDilatedMagnitude.lean`.**  For `f_i = rescale q_i H` the whole expansion goes through with
the *same* atom keys as the single-series case:

```text
coeff N (aeval (familyJets n f) Q)
  = sum_nu (prod_i (coeff i H)^(nu i)) · famAevalWeight q n N Q nu.              (F1)
```

The reason is structural and is the point of the module: `coeff k (rescale q H) = q^k · coeff k H`,
so a split's dilation data contributes only the scalar `prod_t q_(i_t)^(e_t)`, which lands in the
*weight*, while the valuation still depends on the multiset of `H`-indices alone.  Hence
`famAeval_coeff_ne_zero_of_dominant` — a dominant atom key with nonzero weight defeats the relation
— is proved by feeding `(F1)` to the corpus's `weighted_sum_ne_zero_of_min_valuation_complex`
verbatim, with the profile of the single source `H`.

**`SquareFreeAtomKey.lean`.**  The keys that separate a relation are the square-free ones.
`key_eq_iff_exists_perm`: a slot-order tuple has the key of an *injective* tuple `k` exactly when it
is `k` composed with a permutation.  Consequently, for a monomial with `D` jet slots and any
injective `k : Fin D -> N` with all `k s > n`,

```text
sum over splits with key(k) of famWeight = sum over sigma in Sym(D) of
   prod_s [ descFactorial(k_s, j_(sigma^-1 s)) · q_(i_(sigma^-1 s))^(k_s) ]     (F2)
```

(`sum_famWeight_over_squareFreeKey`, `famWeight_keySplit`), the split attached to `sigma` being
`l_t = k_(sigma t) - j_t`.

`(F2)` is the exact input of `expPolySumMulti_eq_zero`: as a function of the `D` free integer
parameters `k_1,...,k_D` it is a multi-node exponential sum whose node tuple is
`(q_(i_(sigma^-1 1)),...,q_(i_(sigma^-1 D)))` and whose polynomial part is the product of falling
factorials `descFactorial(k_s, j)`.  Since the falling factorials of distinct orders are a basis of
`C[k]`, a vanishing node-tuple coefficient forces each monomial coefficient of `Q` to vanish — this
is the orbit separation that no growth argument can perform.

**What remains for `(11)`.**  (i) assemble `famAevalWeight` at a square-free key as the sum over
pairs `(monomial, permutation)` — the `X`-degree and total derivative order of a monomial enter only
through `m(none) - ord(m)`, so for a fixed degree `N = c + sum_s k_s` exactly the monomials of one
class contribute; (ii) run `expPolySumMulti_eq_zero` on it; (iii) design the profile so that a
prescribed square-free key is strictly dominant with a gap beating both the coefficient mass and the
dilation ratios; (iv) bridge from the formal statement to `DifferentialIndependent` of the analytic
orbit.

### Lean progress — the orbit separation of `(11)`, in abstract form

Step (ii) of the remaining programme is now an unconditional Lean theorem, and the two separations
it composes are each isolated as reusable modules.

**`HTGeometry/DescPochhammerProductBasis.lean`** — the jet-order separation.
`descProdSymbol μ = ∏_s (descPochhammer ℤ (μ s)) ∘ X_s` is the unsummed product the descent needs,
as against the permanent symbol which sums over all assignments.  `coeff_descProdSymbol` factorises
its coefficients over the variables (from the corpus's disjoint-variable factorisation
`coeff_prod_aeval_X`), `coeff_descProdSymbol_self` reads its leading coefficient as one, and
`coeff_descProdSymbol_leading_eq_zero` shows a symbol of total order at most `μ₀`'s charges `μ₀`'s
leading monomial only if it *is* `μ₀`.  Hence **`descProdSymbol_combination_eq_zero`**: over any
characteristic-zero ring, a finite combination of these symbols vanishes only when every
coefficient does — take the maximal total order carrying a nonzero coefficient.  No constant-order
restriction is needed, unlike the permanent-symbol version.  `eval_descProdSymbol_map` evaluates
the symbol at a natural tuple as `∏_s (k_s)_{μ_s}`.

**`HTGeometry/MultiNodePolynomialSeparation.lean`** — the multi-node theorem in the form an orbit
argument produces.  `mvPolynomial_nodeSeparation`: if `∑_i P_i(k) ∏_s Z(i,s)^{k_s} = 0` for every
positive tuple `k`, with the node tuples pairwise distinct and nonzero, then every `P_i` is the
zero *polynomial*.  This is `expPolySumMulti_eq_zero` with the coefficient functions presented as
multivariate polynomials rather than as explicit monomial expansions.

**`HTGeometry/MultiNodeInjectiveParameter.lean`** — the hypothesis is weakened to exactly what a
square-free key supplies.  The card's identities hold only at *injective* parameter tuples above
the jet order, never at all positive tuples.  The gap is closed by the triangular substitution
`k_s = K₀ + 1 + ∑_{t ≥ s} m_t`, which is strictly decreasing — hence injective — and above `K₀`,
for every positive `m`.  Under it the node tuple `Z` becomes the tuple of initial products
`W_t = ∏_{s ≤ t} Z_s`, and `prodIic_injective` shows that replacement is injective (compare the two
node tuples at the smallest index where they differ).  The polynomial coefficients are composed
with the affine substitution, whose linear part `triLinear` is injective — look at the largest
index of the support — hence bijective, so `aeval_triSubstPoly_eq_zero` recovers the original
polynomial.  Result: **`mvPolynomial_nodeSeparation_injective`**.

**`HTGeometry/SlotSequenceSeparation.lean`** — the two separations composed.  A flattened jet
monomial of a dilated family is a *slot sequence* `w : Fin D → ι × ℕ`: for each slot, the dilation
it carries and the jet order it consumes.  Its contribution at a key is
`slotTerm q w k = (∏_s (k_s)_{(w s).2}) · ∏_s q_{(w s).1}^{k_s}`.  Then

> **`slotSequence_coeff_eq_zero`.**  For injective nonvanishing `q`, if
> `∑_{w ∈ T} c_w · slotTerm q w k = 0` for every injective key `k` above the jet order, then
> `c_w = 0` for every `w ∈ T`.

Mechanism: group the slot sequences by their dilation tuple; the node separation kills each fibre's
polynomial; inside a fibre the slot sequence is determined by its jet-order tuple, so the
falling-factorial independence kills each coefficient.  This is exactly the orbit separation the
card identifies as the step no growth argument can perform — all translates of one source share a
magnitude profile to leading order, and only letting the `D` key parameters vary independently
distinguishes them.

**`HTGeometry/FamilySquareFreeNodeForm.lean`** — the bridge to the corpus's family weight.
`sum_famWeight_squareFreeKey_node_form` rewrites `∑_{splits with key k} famWeight` as
`∑_σ famNodeTerm`, the permanent whose `σ`-term is a product of falling factorials of the slot
orders times the `k`-powers of the slot dilations — the `slotTerm` shape, one term per permutation.

All five modules are umbrella-wired, build green, and axiom-clean.  What remains of step (i) is the
bookkeeping that presents `famAevalWeight` at a square-free key as a finite family of slot
sequences with coefficients the monomial coefficients of `Q` — the dependent-arity transport across
monomials of a fixed slot count — after which `slotSequence_coeff_eq_zero` discharges step (ii)
outright.  Steps (iii) and (iv) are unchanged.

### Lean progress — steps (i) and (ii) of `(11)` are closed

The assembly is done, and the coupling that made it delicate is now explicit.  A split realizing the
key of `k` satisfies `∑ l = ∑ k − ord m`, while the truncation forces `∑ l = N − m none`; so a
*fixed* `N` exposes a different family of monomials for every key.  Letting the truncation follow
the key,

```text
keyTrunc n m₀ k = m₀ none + ∑ k − ord m₀ ,
```

exposes instead the fixed class `keyClass` of monomials with the slot count of `m₀` and the same
excess `m none − ord m`.  Over that class the key weight is a sum of slot-sequence contributions
indexed by pairs (monomial, ordering) — an index set independent of `k` — so one separation sees
every key at once.

**`HTGeometry/FlatIndexFiber.lean`** — `card_filter_flatIndex`: the flattening of an exponent
profile has fibres of the prescribed sizes.  This is what lets a slot sequence recover the monomial
it came from.

**`HTGeometry/FamilySlotSequence.lean`** — **`exists_slotSeq_of_key`**: a split realizing the key of
an injective tuple above the jet order *is* a slot sequence — its weight is `slotTerm q w k` and the
multiplicity of each slot label in `w` is the corresponding jet exponent.  Uses the corpus's
`key_total_count` (the key fixes the slot count), `key_comp_equiv` (transport along `finCongr`) and
`key_eq_iff_exists_perm`.

**`HTGeometry/FamilyKeyInnerSum.lean`** — **`sum_famWeight_key_eq_slotSeq`**:

```text
∑_{splits with key k} famWeight = ∑_{σ : Perm (Fin D)} slotTerm q (slotSeqOf n D m σ) k ,
```

with `slotSeqOf n D m σ` the monomial's slot sequence listed in the order `σ`.  Index set and slot
sequences are `k`-independent; only the contribution moves.

**`HTGeometry/FamilyKeySeparation.lean`** — the assembly.  `famAevalWeight_expand` splits the key
weight over monomials; `mem_keyClass_of_contributes` shows a contributing split forces its monomial
into `keyClass` (the key fixes `∑ famOrder = ∑ k`, the antidiagonal fixes `∑ l = N − m none`, and
the two together are the class relation); `famAevalWeight_key_eq_class_sum` is the resulting
identity.  Feeding it to the grouped slot-sequence separation at the slot sequence of `m₀` itself,
and recovering `m₀` from that slot sequence — its label multiplicities give `m₀ ∘ some`, its order
sum plus the class relation gives `m₀ none` — yields

> **`coeff_eq_zero_of_famAevalWeight_key_vanishing`.**  If the square-free key weights vanish at
> every injective key above the jet order, at the truncation following the key, then the coefficient
> of the reference monomial vanishes.

and its contrapositive

> **`exists_key_famAevalWeight_ne_zero`.**  For every nonzero jet polynomial `Q` there are a
> monomial `m₀` and an injective key `k` above the jet order with
> `famAevalWeight q n (keyTrunc n m₀ k) Q (key k) ≠ 0`.

All modules umbrella-wired, build green, axiom-clean.  This is exactly the datum
`famAeval_coeff_ne_zero_of_dominant` consumes as `hw₀`, so what remains of `(11)` is step (iii) — a
*single* profile, independent of `Q`, for which the key produced above is dominant with a gap
beating the coefficient mass — and step (iv), the bridge to `DifferentialIndependent`.
