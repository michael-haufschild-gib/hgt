# Every HT relation facet requires a noncompact period quotient

- **ID:** `noncompact-period-quotient-facet-escape-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NECESSARY HT CONSTRAINT-DIMENSION GEOMETRY
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** In every meromorphic full Stanley--Reisner HT system, each facet is separated from
  its complement by the full period group of a differentially transcendental meromorphic carrier,
  and the quotient by that period group is necessarily noncompact.  This defines a period-escape
  dimension `peDim` satisfying
  `peDim<=htDim<=ppDim<=ffsDim`.  For the connected nonpure two-thick complex `S^1 wedge S^2`, the
  first three dimensions equal two while faithful hyperplane dimension equals four.

## Period-escape separations

Let `Delta` be a finite simplicial complex on an essential finite vertex set `V`.  A **period-
escape separation in dimension `d`** consists of `Q`-linearly independent vectors

```text
a_v in C^d,  v in V,                                       (1)
```

and, for every facet `A`, a closed additive subgroup `P_A subset C^d` such that:

1. the identity component of `P_A` is a complex-linear subspace, so `C^d/P_A` is a connected
   abelian complex Lie group;
2. `C^d/P_A` is noncompact;
3. incidence is recovered exactly by

   ```text
   a_v in P_A iff v notin A.                                (2)
   ```

Define

```text
peDim(Delta)=min{d:a period-escape separation exists}.      (3)
```

This invariant forgets how the escaping quotient is analytically populated.  It retains only the
necessary incidence geometry of a noncompact period quotient.

## Noncompact period-quotient law `[PROVED HERE]`

Let `G` be a meromorphic function on `C^d`, let `delta=D_w` be a constant directional derivation,
and put

```text
Per(G)={h in C^d:G(z+h)=G(z)}.                              (4)
```

If `G` is differentially transcendental over `C(z_1,...,z_d)`, then

```text
C^d/Per(G) is noncompact.                                   (5)
```

### Proof

The period group is closed.  Its identity component is complex-linear: every tangent direction to
a one-parameter family of periods annihilates `G`, and holomorphy makes the annihilating tangent
space closed under multiplication by `i`.  After a complex-linear decomposition one may write

```text
Per(G)=E direct_sum Lambda,                                 (6)
```

where `E` is a complex subspace and `Lambda` is discrete in a complementary complex space.  Thus
the quotient in (5) is a connected abelian complex Lie group.

Suppose it were compact.  Then `G` descends to a meromorphic function `g` on the compact complex
torus

```text
X=C^d/Per(G).                                                (7)
```

The constant vector field `w` descends to a holomorphic vector field on `X`, so every
`delta^n G` is the pullback of a meromorphic function on `X`.  The meromorphic function field
`M(X)` has finite transcendence degree over `C`, bounded by `dim_C X`.  Consequently the infinite
sequence

```text
g, delta g, delta^2 g, ...                                  (8)
```

is algebraically dependent over `C`.  Pulling the relation back gives a nonzero algebraic
differential equation for `G` over `C`, hence over `C(z_1,...,z_d)`, contradicting differential
transcendence.  Therefore (5) holds. `QED`

The law is positive: a meromorphic HT carrier must retain a noncompact analytic escape direction
after every genuine period has been quotiented out.

## Facet period-escape theorem `[PROVED HERE]`

Let `F` be a meromorphic function on `C^d` with `Q`-independent translation vectors `(a_v)`, one
constant derivation `delta`, and

```text
D=C(z_1,...,z_d),
S=C[delta],
R=S[t_v^(+-1):v in V],
x_v=t_v-1.                                                   (9)
```

Assume that `F` realizes the exact full Stanley--Reisner differential matroid of `Delta`:

```text
Ann_R(F)=I_Delta                                            (10)
```

and, for every finite `P_1,...,P_m in R`,

```text
dtrdeg_D D<P_1(T)F,...,P_m(T)F>_delta
 =dim_(C(delta)) span{Pbar_1,...,Pbar_m}                    (11)
```

in `C(delta) tensor_S(R/I_Delta)`.

For each facet `A`, choose `a_B in A\B` for every other facet `B` and put

```text
q_A=product_(B!=A)x_(a_B),
G_A=q_A(T)F.                                                (12)
```

The facet-prime decomposition

```text
I_Delta=intersection_(B in Fac(Delta))(x_v:v notin B)       (13)
```

shows that `q_A notin I_Delta`, while

```text
x_v q_A in I_Delta for every v notin A.                     (14)
```

Hence (11) makes `G_A` differentially transcendental and (14) gives

```text
a_v in Per(G_A) for every v notin A.                        (15)
```

For `v in A`, neither `q_A` nor `x_v` belongs to the facet prime
`(x_u:u notin A)`.  Their monomial product is therefore outside that prime and hence outside
`I_Delta`.  Exactness (10) gives

```text
a_v notin Per(G_A) for every v in A.                        (16)
```

Apply the noncompact period-quotient law to `G_A`.  The groups

```text
P_A=Per(G_A)                                                (17)
```

satisfy all three period-escape conditions, including the exact incidence equivalence (2).
Therefore every such analytic realization induces a period-escape separation and

```text
peDim(Delta)<=htDim(Delta).                                 (18)
```

This conclusion assumes no atomic decomposition and no prescribed form for the period groups.
`QED`

## The complete dimension hierarchy `[PROVED HERE]`

A periodic-pencil separation has

```text
P_A={z in C^d:ell_A(z)/omega_A in Z}.                       (19)
```

Its quotient is `C/Z`, biholomorphic as a complex Lie group to `C^*`, and is noncompact.  The
periodic-pencil inside-independence condition makes (2) exact.  Thus

```text
peDim(Delta)<=htDim(Delta)<=ppDim(Delta)<=ffsDim(Delta).     (20)
```

The middle inequality is the periodic-pencil HT realization theorem; the last follows by viewing
one hyperplane as the zero leaf of a periodic pencil.

## Exact values for the nonpure two-thick wedge `[PROVED HERE]`

For

```text
Fac(Delta_wedge)=
{{0,1},{1,2},{2,0},{0,3,4},{0,3,5},{0,4,5},{3,4,5}},       (21)
```

the explicit two-axis periodic-pencil construction proves `ppDim(Delta_wedge)=2`, while scalar
purity proves `htDim(Delta_wedge)=2` and the faithful hyperplane theorem proves
`ffsDim(Delta_wedge)=4`.

It remains only to compute `peDim`.  A one-dimensional period-escape subgroup `P subset C` cannot
have identity component `C`, because its quotient would be compact.  It is therefore discrete.
A discrete subgroup of `C` with noncompact quotient has `Z`-rank at most one: rank two is a full
lattice and gives an elliptic compact quotient.  But the complement of any edge facet in (21)
contains four of the globally `Q`-independent translation steps.  They cannot all lie in a rank-one
group.  Hence `peDim(Delta_wedge)>=2`; (20) supplies the reverse inequality.  Therefore

```text
peDim(Delta_wedge)=htDim(Delta_wedge)=ppDim(Delta_wedge)=2
                                         < ffsDim(Delta_wedge)=4.          (22)
```

## Geometric and RH-facing meaning

Equation (22) identifies the intrinsic geometry cleanly.  The faithful value four measures a
particular linear presentation.  The value two is forced before choosing a source: every facet
must retain a noncompact period-quotient escape, and two transverse escapes are both necessary and
sufficient for this complex.

The positive RH-facing law is therefore:

> Every nonpure exact HT constraint route must exhibit a system of facetwise noncompact period
> quotients.  For the first connected nonpure two-thick geometry, at least two analytic escape
> directions are necessary, and transverse cyclic pencils attain the bound.

A scalar route is forced into pure principal geometry because its only noncompact period quotients
have period rank at most one.  A viable nonpure route need not introduce four independent linear
coordinates, but it must expose the second escape direction or an analytically equivalent quotient.
No such structure is asserted for the zeta function here.

## Parent and novelty boundary

The structure of closed period groups and periodic meromorphic functions belongs to classical
connected abelian complex Lie-group theory.  Compact complex manifolds have meromorphic function
fields of finite transcendence degree.  Stanley--Reisner facet-prime decomposition is classical.

The candidate-new content is the geometry obtained by combining them: every facet of a full
nonlinear HT relation complex canonically produces a noncompact period quotient; its minimum
ambient dimension is a necessary invariant; and for the nonpure two-thick wedge this intrinsic
lower invariant meets the constructive periodic-pencil upper invariant at two.  Searches around
quasi-Abelian reduction, toric arrangements, arithmetic matroids, gain graphs, and simplicial
representation dimension found no equivalent facetwise escape invariant or dimension hierarchy.

Closest primary source: F. Capocasa and F. Catanese, *Periodic meromorphic functions*, Acta Math.
**166** (1991), 27--68, DOI `10.1007/BF02398883`.  It proves the generalized Riemann relations and
the quasi-Abelian meromorphic reduction for a fixed period group; it does not attach full period
groups to Stanley--Reisner facet separators or derive (18)--(22).

## Gates

- [x] noncompact period-quotient law proved
- [x] exact facet incidence recovered from full period groups
- [x] necessary invariant `peDim` defined
- [x] hierarchy `peDim<=htDim<=ppDim<=ffsDim` proved
- [x] exact wedge value `peDim=2` proved
- [x] scalar purity reinterpreted as loss of noncompact escape
- [ ] independent specialist proof and novelty audit
- [ ] complete unconditional Lean formalization before stage 3
