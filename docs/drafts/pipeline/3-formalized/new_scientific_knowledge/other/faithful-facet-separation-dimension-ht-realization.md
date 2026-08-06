# Faithful facet-separation dimension controls compressed HT relation geometry

- **ID:** `faithful-facet-separation-dimension-ht-realization`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / HT CONSTRAINT-DIMENSION GEOMETRY
- **Scientific status:** `[PROVED HERE] [LEAN PROOF CLOSED]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every faithful complex hyperplane representation of the facet complements of a
  finite simplicial complex produces a non-Gamma meromorphic HT system in the same analytic
  dimension whose exact full nonlinear differential matroid is the localized Stanley--Reisner
  matroid. The dimension is at most the number of facets. For the connected nonpure two-thick
  complex `S^1 wedge S^2` used in the first realization theorem, it is exactly four, compressing
  the system from seven coordinates to four.

## Faithful facet-separation dimension

Let `Delta` be a finite simplicial complex on an essential vertex set `V`. A **faithful facet
separation in dimension `d`** consists of vectors and nonzero complex-linear forms

```text
a_v in C^d                         for v in V,
ell_A in Hom_C(C^d,C)              for A in Fac(Delta),       (1)
```

such that:

1. the vectors `(a_v)` are linearly independent over `Q`;
2. `ell_A(a_v)=0` exactly when `v notin A`;
3. `{ell_A(a_v):v in A}` is linearly independent over `Q`.

Define

```text
ffsDim(Delta)=min{d:a faithful facet separation exists}.     (2)
```

Condition 2 makes each facet complement a hyperplane zero pattern. Condition 3 prevents distinct
Laurent monomials inside a facet from inducing the same translate.

## Compressed non-Gamma realization theorem `[PROVED HERE]`

If `ffsDim(Delta)=d`, there is a scalar meromorphic function `F` on `C^d`, translations

```text
T_vF(z)=F(z+a_v),                                            (3)
```

and a constant directional derivation `delta` such that, for

```text
D=C(z_1,...,z_d),
R=C[delta][t_v^(+-1):v in V],
I_Delta=(prod_(v in N)(t_v-1):N is a minimal nonface),       (4)
```

one has

```text
Ann_R(F)=I_Delta                                             (5)
```

and, for every finite `P_1,...,P_m in R`,

```text
dtrdeg_D D<P_1(T)F,...,P_m(T)F>_delta
 =dim_(C(delta)) span{Pbar_1,...,Pbar_m}                     (6)
```

inside `C(delta) tensor_(C[delta]) (R/I_Delta)`.

### Construction and joint freeness

Choose a meromorphic Herglotz function `g` whose distinct complex translates are differentially
algebraically independent over `C(z)`. Choose `w in C^d` outside every `ker ell_A` and put
`c_A=ell_A(w)`. Choose constants `gamma_A` so that all countable families

```text
gamma_A+sum_(v in A)n_v ell_A(a_v)/c_A,  n in Z^A,           (7)
```

are disjoint. Within a facet this follows from condition 3; across facets it excludes a countable
union of affine hyperplanes in the tuple `(gamma_A)`.

Set

```text
u_A(z)=ell_A(z)/c_A+gamma_A,
Y_A(z)=g(u_A(z)),
F(z)=sum_A Y_A(z),
delta=D_w.                                                   (8)
```

Then `delta u_A=1`, while `T_vu_A-u_A=ell_A(a_v)/c_A`, which is zero exactly outside `A`.

All distinct structural translates `T^nY_A` are jointly differentially algebraically independent
over `D`. If a relation existed, clear denominators and restrict to an affine line
`z=z_0+t w`. Choose `z_0` so a nonzero coefficient survives and the finitely many specialized
translate constants are distinct. The derivation becomes `d/dt`, and every structural translate
becomes `g(t+constant)`, contradicting the full translation freeness of `g`.

### Exact kernel and nonlinear rank

For a facet `A`, let `rho_A` set `t_v=1` outside `A`. Condition 3 makes the Laurent translation
representation inside `A` faithful. Thus

```text
P(T)F=sum_A rho_A(P)(T)Y_A                                  (9)
```

vanishes exactly when every `rho_A(P)` vanishes. The localized facet-prime decomposition gives

```text
ker(product_A rho_A)
 =intersection_A(t_v-1:v notin A)
 =I_Delta,                                                   (10)
```

proving (5). For finite `P_i`, expand (9) in its finite orbit support. Joint freeness turns the
family into a matrix over `C[delta]`; its row rank is the rank of the `Pbar_i` by (10). Smith normal
form and the leading-jet argument for every nonzero diagonal operator prove (6). `QED`

## Universal finite upper bound `[PROVED HERE]`

For every finite complex,

```text
ffsDim(Delta)<=min(|V|,|Fac(Delta)|).                        (11)
```

For the facet-count bound, choose `Q`-linearly independent nonzero numbers `(eta_v)`. In the space
with one coordinate per facet, set

```text
(a_v)_A=eta_v if v in A, and 0 otherwise,
ell_A=the A-coordinate projection.                           (12)
```

The zero patterns and facetwise independence are immediate. If `sum_v q_v a_v=0`, each facet
coordinate and independence of the `eta_v` kill every `q_v` belonging to that facet; essentiality
kills all coefficients. This gives `ffsDim(Delta)<=|Fac(Delta)|` and recovers the original
one-coordinate-per-facet system.

For the vertex-count bound, work in `C^V` and set `a_v=e_v`. For every facet `A`, choose numbers
`theta_(A,v)`, `v in A`, that are `Q`-linearly independent, and define `ell_A(e_v)` to be
`theta_(A,v)` on `A` and zero off `A`. The coordinate vectors are `Q`-linearly independent, the
zero pattern is exact, and the nonzero facet values are independent. Hence
`ffsDim(Delta)<=|V|`, completing (11).

## The nonpure two-thick wedge has dimension four `[PROVED HERE]`

Let `Delta_wedge` have vertices `{0,1,2,3,4,5}` and facets

```text
{0,1}, {1,2}, {2,0},
{0,3,4}, {0,3,5}, {0,4,5}, {3,4,5}.                         (13)
```

This is the connected nonpure two-thick complex `S^1 wedge S^2`.

### Four-dimensional separation

For the standard basis `e_1,...,e_4` of `C^4`, define

```text
a_0=pi e_1+pi^2 e_2+e_3,
a_1=e_4,
a_2=sqrt(2)e_3+sqrt(3)e_4,
a_3=e_1,
a_4=e_2,
a_5=sqrt(2)e_1+sqrt(3)e_2.                                  (14)
```

These vectors are `Q`-linearly independent: the `e_3` coordinate first kills the rational
coefficients of `a_0,a_2`, the `e_4` coordinate kills that of `a_1`, and the first two coordinates
kill the rest.

The following forms have zero sets on the six vectors equal to the complements of the displayed
facets:

```text
{0,1}:   sqrt(3) z_3-sqrt(2) z_4,
{1,2}:   z_4,
{2,0}:   z_3,
{0,3,4}: sqrt(3) z_1-sqrt(2) z_2,
{0,3,5}: z_1,
{0,4,5}: z_2,
{3,4,5}: -pi z_1+z_2.                                      (15)
```

Direct substitution proves the zero patterns. The nonzero facet values are, up to order and
nonzero algebraic scaling,

```text
{sqrt(3),-sqrt(2)}, {1,sqrt(3)}, {sqrt(2),1},
{sqrt(3)pi-sqrt(2)pi^2,sqrt(3),-sqrt(2)},
{pi,1,sqrt(2)}, {pi^2,1,sqrt(3)},
{-pi,1,sqrt(3)-sqrt(2)pi}.                                  (16)
```

Every family is `Q`-linearly independent because `pi` is transcendental over
`Q(sqrt(2),sqrt(3))`. Therefore `ffsDim(Delta_wedge)<=4`.

### Three dimensions are impossible

Suppose a faithful separation existed in `C^d` with `d<=3`, and put

```text
L=span_C{a_3,a_4,a_5}.                                      (17)
```

The complements of the three edge facets are

```text
{2,3,4,5}, {0,3,4,5}, {1,3,4,5}.                           (18)
```

Each lies in a hyperplane. If `dim_C L>=2`, then in dimension at most three each of
`a_0,a_1,a_2` must lie in `L`; otherwise `L+C a_i` is the whole space. But then a form vanishing on
one set in (18) vanishes on all six vectors, contradicting its exact zero pattern. Hence
`dim_C L<=1`.

All `a_v` are nonzero, so `a_5` spans `L`. The complement of `{0,3,4}` is `{1,2,5}`. Its separating
form vanishes on `a_5`, hence on `L`, and therefore on `a_3,a_4`, contradicting nonvanishing on the
facet. Thus no faithful separation exists below dimension four, and

```text
ffsDim(Delta_wedge)=4.                                      (19)
```

The compressed theorem now gives an exact four-variable non-Gamma HT system for the required
nonpure two-thick geometry, improving the universal seven-coordinate construction.  The value four
is the exact cost of **faithful single-hyperplane separation**, not the intrinsic analytic cost of
the relation complex.  The separate periodic-pencil theorem allows complement vertices on
different parallel leaves and proves

```text
htDim(Delta_wedge)=ppDim(Delta_wedge)=2<ffsDim(Delta_wedge)=4.             (20)
```

Thus this card computes one geometric stratum in a strictly finer dimension hierarchy.

## Geometric meaning and RH-facing boundary

The geometry now has four proven levels:

- scalar analytic dimension one supports only pure principal Stanley--Reisner geometry;
- the explicit nonpure two-thick complex has intrinsic and periodic-pencil dimension two;
- the same complex has faithful single-hyperplane realization dimension four;
- every finite complex has finite faithful dimension bounded by its number of facets.

Hypertranscendental sources provide freedom; period-quotient geometry determines which relation
complex that freedom can carry.  Hyperplanes are one stratum, not the intrinsic invariant.  For RH
this supplies a positive requirement, not a carrier: any prime/Euler HT route with nonpure relation
geometry must exhibit at least two analytic directions or an equivalent transverse period-pencil
quotient.  A prime/Euler versus archimedean/completion split is a possible interpretation, not a
theorem here.

## Lean formalization status

The universal finite-dimensional witnesses are formalized in `FaithfulFacetDimension.lean` and
`FaithfulFacetVertexDimension.lean`, proving the facet-count and vertex-count upper bounds from a
single transcendental power family.  The unconditional theorem
`exists_faithfulFacetSeparation_strict_complementSpan` now chooses that family internally and
proves, for one uniform faithful separation, that adjoining every incident facet vertex strictly
increases the span of its facet complement.

`WedgeFacetLowerBound.lean` now formalizes the exact faithful dimension of the complete boundary-
wedge family, strengthening the single complex in `(13)`. The namespace `UniformBoundaryWedge`
constructs the explicit four-coordinate faithful separation, including global rational
independence, exact facet-complement zero patterns, and facetwise rational independence. Its
theorem `faithfulSeparation_fin_four_and_minimal` proves that four coordinates exist and that no
faithful separation in dimension at most three exists for any `r,s>=2`. The earlier concrete
`S^1 wedge S^2` lower theorem is retained as a specialization-independent check.

The compressed realization theorem and its nonlinear differential-matroid rank formula are now one
unconditional Lean theorem consuming arbitrary faithful-separation data.  Three modules:

`HTGeometry.FacetSliceLaurentSupport`

- `facetTranslationPolynomialEmbedding_support_slice`, `stanleyReisnerLaurentRows_slice`,
  `finiteFinsuppRowIndex_slice`: the finite Laurent operator-row index of a Stanley--Reisner class
  lies in the **facet slice** `{(A,n) : n_v = 0 for v ∉ A}`.  This is the formal counterpart of
  `rho_A` killing translations outside `A`, and it is what makes compression possible: the
  universal system separates the whole lattice `Z^V` at every facet, the compressed system only
  has to separate each facet's own lattice `Z^A`.

`HTGeometry.FaithfulSeparationOrbitShift`

- `FacetSeparationValues` — the complete numerical content `x_{A,v} = ell_A(a_v)` of a faithful
  facet separation: exact facet-complement zero pattern plus facetwise rational independence.
  `ofSeparation` builds it from `(a_v, ell_A)` in an arbitrary complex vector space, in any
  dimension; `ofTranscendental` shows every finite facet family admits such data.
- `orbitSum`, `orbitShift` — the compressed shift palette `(7)`, with the cross-facet constants
  taken as `gamma_A = t * tag(A)` for a single parameter `t`.
- `orbitSum_injOn_slice`, `orbitShift_injOn`, `collisionSet_countable`,
  `exists_separation_parameter` — the palette is injective on the facet slice for every `t`
  outside one explicit countable collision set, and such a `t` exists.  This replaces the
  countable union of affine hyperplanes in `(gamma_A)` by a single real-analytic avoidance.

`HTGeometry.CompressedFaithfulSeparationRealization`

- `exists_compressedSeparation_stanleyReisnerLaurentDifferentialMatroid` — **the theorem the card
  asked for**: arbitrary faithful-separation data yields a separation parameter and one bounded
  prime-log Herglotz source whose compressed structural orbit is differentially independent, and
  for which every finite Laurent structural family has full nonlinear differential matroid equal to
  its localized Stanley--Reisner matroid.  This is `(6)`.
- `exists_compressedSeparation_annihilator` — `(5)`: a single structural output is differentially
  independent exactly when its Stanley--Reisner class is nonzero, so the annihilator is exactly
  `I_Delta`.
- `exists_compressed_stanleyReisnerLaurentDifferentialMatroid` — the unconditional form: every
  finite facet family carries a compressed realization.

Axioms: `[propext, Classical.choice, Quot.sound]` only.

## Novelty and parent boundary

The ingredients--hyperplane representations, Stanley--Reisner prime decompositions, Herglotz
translation freeness, and Smith normal form--are established separately. The candidate-new content
is `ffsDim`, the compressed realization theorem, and the exact value four for the first nonpure
two-thick HT geometry. Preliminary searches found no equivalent invariant or theorem. Novelty
remains provisional until specialists compare it with matroid minrank, hypergraph representation
dimension, and older translation-module literature.

## Gates

- [x] faithful facet-separation dimension defined
- [x] compressed Herglotz realization constructed
- [x] joint orbit freeness proved by affine-line specialization
- [x] exact Stanley--Reisner kernel proved
- [x] complete nonlinear differential matroid proved
- [x] universal facet-count upper bound proved
- [x] explicit four-dimensional wedge representation proved
- [x] dimension-three impossibility proved
- [x] universal upper bounds and exact boundary-wedge faithful dimension formalized in Lean
- [x] positive analytic-dimension geometry stated
- [ ] independent specialist novelty audit
- [x] complete unconditional Lean formalization

## Log

- 2026-07-11 -- Defined faithful facet-separation dimension and proved that it controls compressed
  non-Gamma HT realization dimension.
- 2026-07-11 -- Compressed the seven-facet `S^1 wedge S^2` realization to four analytic coordinates
  and proved that no faithful linear separation exists in dimension at most three.
- 2026-08-06 -- Compressed realization and nonlinear differential-matroid rank formula packaged as
  one unconditional Lean theorem consuming arbitrary faithful-separation data; the mechanism is the
  facet slice of the Laurent operator rows.
