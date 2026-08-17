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

## Lean status

The invariant, the constructive half of the hierarchy, and the exact wedge value are formalized
unconditionally.

`formal/GaloisForLFunctions/HTGeometry/EscapeSubgroup.lean` defines the three period-escape
conditions and proves the periodic-pencil instance:

```text
idComponentSet
IsEscapeSubgroup
not_compactSpace_quotient_of_realSurjection
subsingleton_of_isPreconnected_subset_intCast
pencilForm, pencilSubgroup
isClosed_pencilSubgroup
idComponentSet_pencilSubgroup
noncompact_quotient_pencilSubgroup
isEscapeSubgroup_pencilSubgroup
DimOne.compactSpace_quotient_of_lattice
DimOne.exists_rat_relation_of_isEscapeSubgroup
```

`idComponentSet_pencilSubgroup` is the exact identity-component computation `(19)` asks for: the
component is the kernel of the pencil form, because the form is continuous and integer valued on
the period group, so it is constant on the component, while every kernel vector is joined to the
origin by the real ray through it.  `DimOne.exists_rat_relation_of_isEscapeSubgroup` is the exact
one-dimensional escape bound used in `(22)`: two `ℝ`-independent members would tile `ℂ` by a
compact box and make the quotient compact, and an irrational real ratio would put a whole real line
inside the closed subgroup, forcing the complex-linear identity component to be everything.

`formal/GaloisForLFunctions/HTGeometry/PeriodEscapeDimension.lean` defines the invariant `(1)-(3)`
and proves the constructive half of `(20)`:

```text
PeriodEscapeSeparation
peDim
periodEscapeSeparationOfPencil
peDim_le_ppDim
isEmpty_periodEscapeSeparation_zero
isEmpty_periodEscapeSeparation_one
two_le_peDim
```

`formal/GaloisForLFunctions/HTGeometry/BoundaryWedgePeriodEscape.lean` closes `(22)` for the whole
nondegenerate two-parameter wedge family:

```text
boundaryWedgeFacet_nonempty
boundaryWedge_peDim_eq_two
```

`formal/GaloisForLFunctions/HTGeometry/MeroPeriodQuotient.lean` proves the noncompact
period-quotient law `(4)-(5)` in one complex variable, with no hypothesis:

```text
exists_real_mul_of_not_linearIndependent
exists_rIndependent_of_compactSpace_quotient
meroPeriodSubgroup
not_compactSpace_quotient_meroPeriodSubgroup
```

A compact quotient of `ℂ` by any subgroup forces two `ℝ`-independent periods, and the corpus's
unconditional theorem `differentialAlgebraicOver_of_translation_fixed` makes a doubly periodic
global meromorphic germ differentially algebraic.  This is the exact scalar case of `(5)` and the
formal content of the card's scalar-purity remark.

`formal/GaloisForLFunctions/HTGeometry/ClosedSubgroupIdentityComponent.lean` proves the general
structural input behind condition 1 of a period-escape separation, in every dimension:

```text
lineSubmodule
exists_line_of_not_discrete
idComponentSet_eq_lineSubmodule
complexLineSubmodule
isEscapeSubgroup_of_isClosed
```

`idComponentSet_eq_lineSubmodule` is the exact statement that the identity component of a closed
additive subgroup of a finite-dimensional real vector space is the largest real subspace it
contains: a closed subgroup with arbitrarily small nonzero members contains a whole real line
(normalize a null sequence to the unit sphere, take a convergent subsequence, and approximate an
arbitrary real multiple by integer multiples), so splitting off a linear complement makes the
subgroup discrete transverse to that subspace, which is therefore clopen inside it.
`isEscapeSubgroup_of_isClosed` packages the criterion the card's law produces: closed, maximal real
subspace stable under multiplication by `i`, noncompact quotient.

`formal/GaloisForLFunctions/HTGeometry/MeroPeriodEscape.lean` verifies all three conditions for the
period group of a hypertranscendental germ in one complex variable:

```text
mem_meroPeriodSubgroup_iff
isClosed_meroPeriodSubgroup
linearIndependent_one_I
lineSubmodule_meroPeriodSubgroup_eq_bot
isEscapeSubgroup_meroPeriodSubgroup
```

The translation identity `x(· + h) = x` cross-multiplies to the pointwise identity
`A(z+h) B(z) = A(z) B(z+h)`, so `Per(x)` is an intersection of closed conditions.  A whole real
line of periods would make the entire function `A - c B` vanish along that line for the value `c`
at a regular point of `B`, hence vanish identically, hence make *every* complex number a period —
in particular two `ℝ`-independent ones, contradicting hypertranscendence.  So
`isEscapeSubgroup_meroPeriodSubgroup` is `(4)`, `(5)` and both structural conditions of a
period-escape separation, unconditionally, for `d = 1`.

All six modules are wired into `formal/GaloisForLFunctions/HTGeometry.lean`.  Direct
`lake env lean` checks and targeted builds pass; `#print axioms` on every capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`.

`formal/GaloisForLFunctions/HTGeometry/SeveralVariableTranslation.lean` carries the whole
period-group layer to `ℂ^d`, for an arbitrary complex normed space:

```text
addTranslationGen, addTranslationAnalyticEquivGen, addTranslationMeroEquivGen
addTranslationMeroEquivGen_add, addTranslationMeroEquivGen_zero
meroPeriodSubgroupGen
mem_meroPeriodSubgroupGen_iff
isClosed_meroPeriodSubgroupGen
dense_ne_zero_of_analyticOnNhd
complex_smul_mem_meroPeriodSubgroupGen
lineSubmodule_meroPeriodSubgroupGen_smul_I
isEscapeSubgroup_meroPeriodSubgroupGen
```

The several-variable analytic germ ring and its meromorphic fraction field were already
corpus-owned (`Bottcher.analyticSubringGen`, `Bottcher.meroFieldGen`,
`Bottcher.precompAnalyticEquivGen`, `Bottcher.precompMeroEquivGen`); this module instantiates them
at `g = (· + h)`.  `complex_smul_mem_meroPeriodSubgroupGen` is the exact statement that a real line
of periods is a complex line of periods: along the complex line through a period direction the
numerator minus the regular value times the denominator is analytic in one variable and vanishes on
the real axis, hence identically, and the resulting identity extends from the dense regular locus
of the denominator by continuity.  Hence `isEscapeSubgroup_meroPeriodSubgroupGen`: in every
dimension, the period group of a global meromorphic germ is closed and has complex-linear identity
component, so **noncompactness of the quotient is the only remaining period-escape condition**.

### What remains

**Finite transcendence degree of the meromorphic field of a compact complex torus.**  The proof of
`(5)` for `d >= 2` uses `trdeg_C M(X) <= dim_C X`.  In complex dimension one this is the elliptic
differential-algebraicity theorem already owned here, which is why the scalar case is closed; for
`d >= 2` it is Siegel's theorem and has no Lean proof yet.  This is now the only missing
mathematics on this card: with it, `isEscapeSubgroup_meroPeriodSubgroupGen` closes the noncompact
period-quotient law in every dimension, and the facet theorem `(13)-(18)` is the Stanley--Reisner
facet-prime computation on top of it.

## Gates

- [x] noncompact period-quotient law proved
- [x] exact facet incidence recovered from full period groups
- [x] necessary invariant `peDim` defined
- [x] hierarchy `peDim<=htDim<=ppDim<=ffsDim` proved
- [x] exact wedge value `peDim=2` proved
- [x] scalar purity reinterpreted as loss of noncompact escape
- [x] `peDim` and the period-escape conditions formalized unconditionally
- [x] `peDim<=ppDim` formalized unconditionally
- [x] `peDim(Delta_wedge)=2` formalized unconditionally
- [x] noncompact period-quotient law formalized unconditionally in one complex variable
- [x] identity component of a closed subgroup identified with its maximal real subspace, in every
  dimension, formalized unconditionally
- [x] all three period-escape conditions verified for the period group of a hypertranscendental
  germ in one complex variable
- [x] several-variable meromorphic period groups formalized: closed, with complex-linear identity
  component, in every dimension
- [ ] Siegel bound for compact complex tori formalized, giving `(5)` for `d>=2` and hence
  `peDim<=htDim`
- [ ] independent specialist proof and novelty audit
- [ ] complete unconditional Lean formalization before stage 3

### Progress on the Siegel gate

The gap is *not* the counting step.  With a global presentation `G = A/B` the Schwarz-lemma count
over charts cannot close, because translating `Q = B^m·P(G, δG, …)` by a period multiplies it by
`(B(·+λ)/B)^m`, a meromorphic factor unbounded exactly on the zeros `A` and `B` share.  The chart
comparison constant exists only for *reduced* local fractions, whose transition ratios are
nonvanishing.  So the missing input is Weierstrass preparation and the resulting factoriality of
the local ring of germs — not a sharper estimate.  (With the comparison constant `C₀^m` in hand the
count needs only `N ~ c·m`, well inside the `N ≲ m^{1+1/d}` that the multi-index count allows.)

Weierstrass' preparation theorem is now formalized here, unconditionally:
`GaloisForLFunctions.HTGeometry.weierstrass_preparation`, together with the layer it required —
the weighted argument principle on a disc (`circleIntegral_weighted_logDeriv_eq_powerSum`), which
mathlib does not contain in any form, the holomorphy of the moving root multiset's symmetric
functions (`differentiableOn_esymm_sliceRoots`), and the local constancy of the root count.

Remaining: Weierstrass division, factoriality of the germ ring, local reduced fractions, and then
the Siegel assembly itself.

### The Weierstrass polynomial is monic

`HTGeometry.multisetLinearProd_eq_monic`, unconditional and axiom-clean:

```text
∏_{r ∈ M} (z − r) = z^{card M} + ∑_{j < card M} (−1)^{card M − j} · e_{card M − j}(M) · z^j
```

Monicity is what makes the Weierstrass polynomial a *distinguished* polynomial and is the input to
the uniqueness half of the division theorem: a remainder of degree below `card M` that is divisible
by a monic polynomial of degree `card M` must vanish.  It falls out of the expansion by splitting
the top term, whose coefficient is the zeroth elementary symmetric function, namely `1`.

### The roots are exactly the zeros

`HTGeometry.multisetLinearProd_eq_zero_iff` — `∏_{r ∈ M}(z − r) = 0 ↔ z ∈ M` — and its consequence

**`HTGeometry.slice_eq_zero_iff_mem_sliceRoots`**: for an admissible slice and `‖z‖ < t`,

```text
f (cons z y) = 0  ↔  z ∈ sliceRoots f t y.
```

Both unconditional and axiom-clean.  This closes the identification the preparation theorem is
about: `sliceRoots` is not merely a multiset with the right power sums, it is the zero set of the
slice inside the circle.  Recall that `sliceRoots` is produced by `Classical.choose` from the
argument principle and records only power sums, so this had to be proved, not assumed — via
`multiset_eq_of_powerSum_eq` and the factorization.

### Weierstrass division

`formal/GaloisForLFunctions/HTGeometry/SliceWeierstrassDivision.lean`, unconditional and
axiom-clean, closes the next step of the Siegel programme.

```text
GaloisForLFunctions.HTGeometry.dividedDifferenceCoeff
GaloisForLFunctions.HTGeometry.poly_sub_eq_mul_dividedDifference
HTGeometry.sliceWeierstrassCoeff, HTGeometry.sliceWeierstrass_eq_sum
HTGeometry.divIntegrand, HTGeometry.sliceDivQuotient, HTGeometry.sliceDivRemainder
HTGeometry.sliceDivRemainderCoeff
HTGeometry.circleIntegrable_finsetSum, HTGeometry.circleIntegral_finsetSum
HTGeometry.sliceDivRemainder_eq_sum
HTGeometry.weierstrass_division
```

The quotient is the Cauchy integral of `g/W` against the kernel `(ζ − z)^{-1}`, exactly as the unit
factor of the preparation theorem is the Cauchy integral of `f/W`.  Subtracting it from Cauchy's
formula for `g` leaves the contour integral of

```text
g(ζ) · (W(ζ) − W(z)) / (W(ζ)(ζ − z)),
```

and `poly_sub_eq_mul_dividedDifference` — the statement that `P(ζ) − P(z)` is `(ζ − z)` times a
polynomial of degree below `deg P` in `z` whose coefficients are polynomials in `ζ` — turns the
kernel into a finite sum.  Interchanging that finite sum with the contour integral
(`circleIntegral_finsetSum`, proved here because mathlib has no finite-sum lemma for
`circleIntegral`) exhibits the remainder as

```text
r(z, y) = Σ_{k < d} a_k(y) z^k,   a_k(y) = (2πi)^{-1} ∮ g(ζ,y)·c_k(ζ,y)/W(ζ,y) dζ,
```

with `d = card (sliceRoots f t y)`.  This is Weierstrass' division theorem for one fixed parameter
value.

Remaining on the Siegel gate: joint holomorphy of the quotient and of the remainder coefficients
(the same contour-integral argument as `differentiableOn_sliceUnit`, whose parametric machinery
`CircleIntegralParamOpen` is already owned), uniqueness of the division, factoriality of the germ
ring by induction on the dimension through division and Gauss' lemma, local reduced fractions, and
then the Siegel counting assembly.

### The division is holomorphic in all the variables

The same module adds the parametric half, so Weierstrass division is now available as an identity
between *holomorphic* objects, not only slicewise:

```text
HTGeometry.differentiableOn_sliceDivQuotient
HTGeometry.divRemIntegrand, HTGeometry.sliceDivRemainderCoeff_eq_integral
HTGeometry.differentiableOn_divRemIntegrand
HTGeometry.differentiableAt_sliceDivRemainderCoeff
```

`differentiableOn_sliceDivQuotient` is the preparation-theorem argument with the numerator replaced:
the integrand is holomorphic on the open set where the contour variable avoids the evaluation point
and the zeros of the distinguished polynomial, so the corpus's parametric contour theorem
(`differentiableAt_circleIntegral_slice_open`) applies.  For the remainder coefficients the root
count is constant on a connected parameter set (`card_sliceRoots_const_of_isPreconnected`) and the
coefficients of the distinguished polynomial are holomorphic
(`differentiableOn_esymm_sliceRoots`), so the integrand of `a_k` is holomorphic in the parameters as
well, and the same parametric theorem gives holomorphy of `a_k`.

Remaining on the Siegel gate: uniqueness of the division, factoriality of the germ ring by induction
on the dimension through division and Gauss' lemma, local reduced fractions, and the Siegel counting
assembly.

## Siegel programme — step 4 (uniqueness of the Weierstrass division) is closed

`HTGeometry/WeierstrassDivisionUniqueness.lean` (unconditional, axiom-clean, umbrella-wired):

- `eqOn_of_continuousOn_of_finite_diff` — two continuous functions on an open subset of `C` that
  agree off a finite set agree everywhere.  This is the only topological input the uniqueness needs,
  and it is what encodes root multiplicities without any order arithmetic.
- `eq_zero_of_degree_lt_of_continuous_multiple` — if `P` is a polynomial of degree below
  `card(rhos)`, all the `rhos` lie in the disc of radius `t`, `q` is continuous on that disc and
  `P(z) = q(z)·prod_{rho}(z - rho)` there, then `P = 0`.  The proof peels one root at a time: `P`
  vanishes at `rho`, so `X - rho` divides it; cancelling the factor is legitimate off `rho` and
  extends to `rho` by the lemma above; the degree drops by one and the induction runs on the
  multiset.
- `weierstrass_division_unique` — the quotient and the low-degree remainder of a division by a monic
  polynomial with prescribed roots inside a disc are determined: `P_1 = P_2` on the nose, and
  `q_1 = q_2` on the whole disc (the roots are handled by the same finite-set continuity lemma).

Programme state: steps 1 (preparation), 2 (division), 3 (joint holomorphy of the quotient and of the
remainder coefficients — `differentiableOn_sliceDivQuotient`,
`differentiableAt_sliceDivRemainderCoeff` in `SliceWeierstrassDivision.lean`) and now 4 are closed.
Remaining: 5 factoriality of the analytic germ ring by induction on dimension (preparation reduces
divisibility to `C{z'}[z_n]`, then Gauss), 6 local reduced fractions for meromorphic germs, 7 the
Siegel counting assembly.  The geometric half of 7 is already Lean-owned:
`HTGeometry/SiegelVanishingCriterion.lean` proves `exists_finite_centres_forcing_vanishing` — for a
subgroup with compact quotient and a Schwarz gain below one, jets of order below `N` vanishing at
finitely many prescribed centres force a periodic function to vanish identically.

## Siegel programme — the germ interface

Four further modules, all unconditional, axiom-clean and umbrella-wired, lift the slice-level
Weierstrass machinery to statements about germs, which is the form the factorization theory needs.

- `HTGeometry/AnalyticGermDomain.lean` — `exists_ball_analyticOnNhd`,
  `exists_ne_zero_of_not_eventuallyEq_zero`, `eventuallyEq_zero_of_mul_eventuallyEq_zero`, the
  instances `Nontrivial (AnalyticGerm p)` and `NoZeroDivisors (AnalyticGerm p)`, and
  `exists_regular_direction`: every nonzero germ has a direction `v` along which the one-variable
  restriction `t ↦ f (p + t·v)` is not identically zero.  A representative is nonzero somewhere on
  a ball, and the segment through that point is a disc on which the one-variable identity theorem
  applies — no polarization of the Taylor coefficients is needed.
- `HTGeometry/GermSliceAdmissible.lean` — `exists_sliceAdmissible_nhds`: a holomorphic function
  whose slice in the distinguished variable is not identically zero near the origin admits, for a
  small enough radius `t` and all parameters in a ball, the entire admissibility package that the
  preparation and division theorems consume — the closed disc of radius `2t` inside the domain, the
  slice nonvanishing on the circle of radius `t`, `SliceAdmissible` at every parameter, and the
  isolation of the origin as the only zero of the central slice in the closed disc.  Two
  applications of the tube lemma over the compact disc and the compact circle.
- `HTGeometry/GermWeierstrassPreparation.lean` — `germ_weierstrass_preparation`: on a polydisc

  ```text
  f(z,y) = (z^d + sum_(j<d) a_j(y) z^j) · u(z,y),   u nowhere zero,
  ```

  with the `a_j` holomorphic on the parameter ball and `a_j(0) = 0` — the polynomial is
  *distinguished*.  The vanishing at the origin comes from `sliceRoots_eq_zero_of_isolated` (every
  root of the central slice is the origin) together with `esymm_eq_zero_of_forall_eq_zero`.
- `HTGeometry/GermWeierstrassDivision.lean` — `germ_weierstrass_division`: for a second holomorphic
  `g`,

  ```text
  g(z,y) = q(z,y) · (z^d + sum_(j<d) a_j(y) z^j) + sum_(j<d) b_j(y) z^j
  ```

  on the same polydisc, with `q` holomorphic in all variables and the `b_j` holomorphic in the
  parameters.

With `weierstrass_division_unique` these say that the local ring is a free module of rank `d` over
the ring in the remaining variables, modulo the distinguished polynomial.  That is the interface
step 5 (factoriality) consumes.

## Siegel programme — the assembly for locally holomorphic charts

The chartwise assembly built earlier assumed entire chart data.  That is the wrong hypothesis: a
local presentation of a meromorphic function is holomorphic on a polydisc around its centre and
nowhere else.  Three modules put the machine on the correct hypothesis, all unconditional,
axiom-clean and umbrella-wired.

- `HTGeometry/PolydiscCoeffVanishing.lean` — `norm_le_of_polydiscCoeff_vanish_of_hasSum`: the
  multi-index Schwarz estimate with the polydisc expansion taken as a hypothesis rather than derived
  from global holomorphy.  The previous statement is now a corollary.
- `HTGeometry/PolydiscLocalSchwarz.lean` — `polydiscSeries_hasSum_of_differentiableOn` and
  `norm_le_of_polydiscCoeff_vanish_of_differentiableOn`: the expansion and the estimate for a
  function holomorphic on `polydiscSet c (fun _ => R₁)` with `R < R₁`.  The expansion is the
  corpus's own local Cauchy formula `polydiscCauchyFormula_of_differentiableOn` fed into the
  expansion criterion `polydiscSeries_hasSum_of_cauchy`, whose hypotheses were already local.
- `HTGeometry/SiegelLocalCharts.lean` — the chartwise Taylor-condition map, the gain, the vanishing
  and the algebraic relation, all for chart data holomorphic only on polydiscs:

  ```text
  exists_ne_zero_poly_eval_eq_zero_local :
    A i k, B i k holomorphic on the polydisc of radius R₁ around c i,
    card ι · N^n < (m+1)^(n+1),   C · Schwarz factor < 1,   transition structure
      ==>  ∃ P ≠ 0 in C[X_0,…,X_n],  P(A i 0 / B i 0, …) = 0
           at every point of every small polydisc where that chart's denominators do not vanish.
  ```

  `SiegelGainVanishing.eqOn_zero_of_family_siegel_gain` was generalized in passing: it needs
  continuity only of the local representatives on the small closed polydiscs.

### What the instantiation still needs

The corpus's meromorphic field `Bottcher.meroFieldGen (Set.univ)` is the fraction field of the ring
of *entire* functions, so a global presentation `f = A/B` comes for free and the Poincaré problem
does not arise.  What a global presentation does not give is the transition bound: for a torus point
`w` and a period `p` the transition factor is `∏_k (B_k w / B_k (w − p))^m`, and `B_k` is not
periodic, so the ratio is unbounded along the zero divisor.  The bound requires *reduced* local
presentations at the centres — `GermReducedFraction` and `GermRatioBound`, both owned and now
available at every point through `GermTranslationFactorial` — compared at a point of the overlap
rather than at the centre.  The missing ingredient is therefore the propagation of coprimality of
analytic germs to nearby points, i.e. that the common zero set of two coprime germs has codimension
at least two.  Above that one statement the whole analytic machine is unconditional and correctly
hypothesized.

## Siegel programme — step 5': coprimality of analytic germs is an open condition

The ingredient the previous section named as the only missing one is now formalized,
unconditionally and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), and wired into the
`HTGeometry` umbrella.

```text
GaloisForLFunctions.HTGeometry.eventually_isRelPrime_germ :
  f, g holomorphic near p in C^(n+1),  IsRelPrime (germ_p f) (germ_p g)
    ==>  for all q in a neighbourhood of p,  IsRelPrime (germ_q f) (germ_q g).
```

Equivalently: the common zero set of two coprime germs contains no hypersurface through any nearby
point, which is the codimension-two statement in the form the transition bound consumes.  No
dimension theory of analytic sets is used; the proof replaces it by a Bézout constant.

### The route

`HTGeometry/MonicBezoutConstant.lean` — the algebraic half.  Over a unique factorization domain `A`,
two monic polynomials with no common monic factor of positive degree satisfy

```text
alpha*F + beta*G = C c,   c in A,  c != 0.
```

The descent is Gauss' lemma in its integrally closed form: a monic greatest common divisor computed
in `K[X]`, `K = Frac A`, is the image of a monic divisor in `A[X]`
(`IsIntegrallyClosed.eq_map_mul_C_of_dvd` plus `Monic.dvd_of_fraction_map_dvd_fraction_map`), so a
common factor over `K` would descend.  Coprimality over `K` then gives a Bézout identity whose
denominators are cleared by `IsLocalization.integerNormalization`.  Declarations:
`exists_preimage_monic_of_map_dvd`, `isCoprime_map_of_no_common_monic_factor`,
`smul_eq_C_mul_of_fraction`, `exists_bezout_const`.

`HTGeometry/GermZeroProjection.lean` — the projection statement.  A germ that vanishes at a point
and is regular in the distinguished coordinate there has, over *every* nearby parameter value, a
zero inside any prescribed neighbourhood:

```text
eventually_exists_slice_zero_zero,  eventually_exists_slice_zero :
  h(w0) = 0,  slice of h regular at w0,  W in nhds w0
    ==>  eventually in y near tail w0,  exists z,  cons z y in W  and  h (cons z y) = 0.
```

The proof is the corpus's own root count of a slice: `card_sliceRoots_const_of_isPreconnected` makes
it locally constant in the parameters, `slice_eq_zero_iff_mem_sliceRoots` makes it at least one at
the base parameter, and `sliceRoots_norm_lt` keeps the root inside the circle.  The arbitrary-point
version is the origin version conjugated by a translation (`cons_add`).

`HTGeometry/GermSliceNonvanishing.lean` — regularity spreads.  `exists_polydisc_slice_ne_zero`: on
the preparation polydisc of a regular germ, the slice at *every* parameter is nonzero near *every*
point of the disc, because the Weierstrass factor is a monic — hence nonzero — polynomial and the
unit does not vanish.  This is what allows a divisor of `f` at a point of the polydisc to be
prepared in the *same* coordinates that were chosen at the centre.

`HTGeometry/GermCoprimeOpen.lean` — the assembly.

* `IsRelPrime.ringEquiv`, `isRelPrime_analyticGermOf_pullback_iff` — relative primality of germs is
  invariant under an analytic change of coordinates.
* `eventually_isRelPrime_germ_of_regular` — the theorem in coordinates where both germs are regular.
  Weierstrass preparation gives `germ f = germEval (distPoly d alpha) * unit`; a common monic factor
  of positive degree of the two distinguished polynomials would be distinguished
  (`coeff_eq_zero_of_monic_mul_eq_distPoly`) and so a non-unit common germ divisor
  (`not_isUnit_germEval_distPoly`), which coprimality forbids.  The Bézout constant then reads, on a
  polydisc, as an identity of holomorphic functions

  ```text
  p*f + q*g = c o tail,   c a nonzero germ of the parameters alone.
  ```

  A common non-unit divisor `h` of `f` and `g` at a point `w` of the polydisc is regular in the same
  distinguished coordinate (it divides `f`, whose slices are nowhere identically zero), so its zero
  set meets every nearby parameter fibre; every such zero is a common zero of `f` and `g`, so `c`
  vanishes on a whole neighbourhood of the parameter of `w`, hence identically by the identity
  theorem — contradicting `c != 0`.
* `eventually_isRelPrime_germ_zero` — the regularity hypotheses removed by a linear change of
  coordinates (`exists_regular_coordinate_change` applied to the product), with the two degenerate
  cases (one germ identically zero, so the other is a unit) handled separately.
* `eventually_isRelPrime_germ` — the statement at an arbitrary centre, by translation.

### The transition bound, which is what the count consumes

`HTGeometry/GermReducedTransition.lean`:

```text
associated_den_of_reduced_at            -- reduced presentations at a point have associated denominators
exists_two_sided_ratio_bound_of_reduced_at
eventually_ratio_bound_of_reduced_centres :
  (A1,B1) reduced at c1,  (A2,B2) reduced at c2
    ==>  eventually in w in nhds c1 inf nhds c2,  wherever A1*B2 = A2*B1 near w,
         there are r, C > 0 with  |B2| <= C|B1|  and  |B1| <= C|B2|  on ball w r.
```

This is exactly the comparison the chartwise count needs on the overlaps, and the exact statement
the previous section listed as unavailable: reducedness is a condition at the centre, the comparison
happens away from it, and the two are joined by the openness of coprimality.

Remaining on the Siegel gate: the counting assembly — feeding these local reduced presentations and
their transition constants into `SiegelLocalCharts.exists_ne_zero_poly_eval_eq_zero_local` and
`SiegelGainVanishing.eqOn_zero_of_family_siegel_gain` for a compact complex torus.

## Siegel programme — the counting assembly, and the theorem

The Siegel bound is now a theorem here, unconditionally and axiom-clean.

```text
GaloisForLFunctions.HTGeometry.exists_ne_zero_poly_of_periodic_meromorphic :
  P <= C^(n+1) with compact quotient,  A_k, B_k entire (k in Fin (n+2)), B_k not identically 0,
  A_k(z+p) B_k(z) = A_k(z) B_k(z+p) for every p in P
    ==>  exists Q != 0 in C[X_0,...,X_(n+1)] with
         Q(A_0/B_0, ..., A_(n+1)/B_(n+1)) = 0 at every point where no denominator vanishes.
```

That is `trdeg_C M(X) <= dim_C X` for a compact complex torus `X = C^(n+1)/P`, in the corpus's
meromorphic field (fractions of entire functions).  The cleared form,
`exists_ne_zero_siegelHomCombination_of_periodic_meromorphic`, produces a nonzero coefficient vector
whose denominator-cleared combination vanishes at *every* point of `C^(n+1)`; that is the form a
differential-algebra argument consumes, since it is an identity of entire functions.

### What the assembly needed on top of the openness of coprimality

* `HTGeometry/GermReducedPresentation.lean` — `exists_reduced_presentation_at` (every germ fraction
  reduces, at any point), `exists_unit_factor_of_reduced_at` (two reduced presentations of the same
  fraction differ by *one* unit factor: associated denominators give it, and cancelling the nonzero
  denominator in the cross identity carries it to the numerators), and
  `siegelHomCombination_of_unit_factors` — a denominator-cleared combination transforms by the
  `m`-th power of the product of those unit factors.  This is division-free: no hypothesis on where
  the denominators vanish, which is what makes the transition an identity rather than an estimate.
* `HTGeometry/UniformLocalBound.lean` — `exists_uniform_bound_of_local`: a monotone property that
  holds with some bound near every point of a compact set holds with one bound on the whole set.
* `HTGeometry/SiegelUniformTransition.lean` — `SiegelTransitionAt`, its existence with a local bound
  near every point of a chart (`eventually_siegelTransitionAt`), its uniformisation over the closed
  polydisc of a chart and then over the finitely many charts (`exists_uniform_siegelTransition`),
  and `htrans_of_uniform_siegelTransition`, the transition structure with comparison constant
  `C^((n+2)m)` — *independent of the degree* except through that power, which is the point.
* `HTGeometry/SiegelCountParameters.lean` — `exists_siegel_count_params`: the counting inequality
  `card ι · N^n < (m+1)^(n+1)` and the gain inequality `D^m · (N+1)^n · q^N · S < 1` hold together
  with `N = κ·m`, where `κ` is chosen so that `D·q^κ <= 1/2`; the counting side then needs only
  `m >= card ι · κ^n`, because `(m+1)^(n+1) >= (m+1)·m^n`.
* `HTGeometry/SiegelChartConstruction.lean` — `eqOn_zero_of_mul_eq_zero` (cancel a nonzero
  holomorphic factor on a connected domain), `exists_reduced_chart`, `ChartPackage` and
  `exists_chartPackage_at`, `exists_uniform_chartPackage` (one radius for every centre of a compact
  set, by a Lebesgue-number argument), `chartPackage_translate` (translate a chart by a period) and
  `exists_uniform_chartPackage_everywhere`, and `chartPackage_cross` — two charts of the same family
  present the same fraction across a period, proved by clearing `B_k(z)·B_k(z-p)` twice.
* `HTGeometry/SiegelTorusTranscendence.lean` — the assembly, ending with the globalisation: the
  cleared combination of the *global* presentations is entire and vanishes on a nonempty open subset
  of one small polydisc, hence identically.

### Gate

- [x] Siegel bound for compact complex tori formalized

What remains on this card is the instantiation of `(5)`: the corpus's several-variable meromorphic
field `meroFieldGen (Set.univ)` and its period group `meroPeriodSubgroupGen` must be fed to the
theorem above, together with a constant directional derivation, to turn "the quotient is compact"
into an algebraic differential equation for the carrier.  The analytic content is closed; the
remaining step is the differential-field interface.

## The noncompact period-quotient law `(5)` is now a theorem in every dimension

```text
GaloisForLFunctions.HTGeometry.not_compactSpace_quotient_of_hypertranscendental_gen :
  w a constant direction,  P a group of periods of x in meroFieldGen (Set.univ : Set (C^(n+1))),
  x hypertranscendental over C for the directional derivation
    ==>  the quotient of C^(n+1) by P is noncompact.

GaloisForLFunctions.HTGeometry.isEscapeSubgroup_meroPeriodSubgroupGen_of_hypertranscendental :
  the period group of such an x is an escape subgroup.
```

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`, umbrella-wired.  This is exactly
`(4)`–`(5)` for `d >= 2`, i.e. the clause `isEscapeSubgroup_meroPeriodSubgroupGen` was missing.

Route: a constant directional derivation commutes with every translation
(`addTranslationAnalyticEquivGen_dirDeriv` on the germ ring,
`addTranslationMeroEquivGen_dirDeriv` on the field, proved through the Leibniz rule on a fraction
presentation rather than the quotient rule, to stay inside one `Algebra Z` instance path), so every
jet of a `P`-invariant element is `P`-invariant.  If the quotient were compact, Siegel's bound would
make the first `n + 2` jets algebraically dependent over `C`, i.e. would make `x` differentially
algebraic.

The same law is proved in the entire-fraction-field model in
`HTGeometry/EntirePeriodSiegel.lean` (`not_compactSpace_quotient_of_hypertranscendental`), together
with the cross-multiplied invariance criterion `fieldTranslateEquiv_fix_iff`; and Siegel's bound is
transported to the corpus's meromorphic field in `HTGeometry/SiegelMeroFieldDependence.lean`
(`exists_ne_zero_poly_aeval_of_compactSpace_quotient`).

### Gate

- [x] noncompact period-quotient law `(5)` formalized in every dimension

What remains is the facet theorem `(13)`–`(18)`: the Stanley--Reisner facet-prime computation that
turns an `HTRealizableDim` datum into a `PeriodEscapeSeparation`, giving `peDim <= htDim`.  Both
end points are already defined in the tree (`PencilHTDimension.htDim`,
`PeriodEscapeDimension.PeriodEscapeSeparation`), and the analytic input of that computation is the
law above.
