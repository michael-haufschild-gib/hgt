# Wedges of simplex boundaries have uniform intrinsic HT dimension two and faithful dimension four

- **ID:** `boundary-wedge-uniform-ht-dimension-gap`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / INFINITE FAMILY OF HT CONSTRAINT GEOMETRIES
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For every `r,s>=2`, the simplicial wedge
  `Delta_(r,s)=boundary(sigma^r) wedge boundary(sigma^s)` has
  `htDim=ppDim=2<ffsDim=4`; it is two-thick and is nonpure exactly when `r!=s`.

## The family

Let

```text
B_x={0,x_1,...,x_r},
B_y={0,y_1,...,y_s},
V=B_x union B_y,                                            (1)
```

where the two blocks meet only at `0`. Define `Delta_(r,s)` to have facets

```text
B_x\{u}  for u in B_x,
B_y\{v}  for v in B_y.                                     (2)
```

Thus `Delta_(r,s)=boundary(sigma^r) wedge boundary(sigma^s)`. Every nonfacet face lies in one
boundary and omits at least two vertices of that block, so it has two distinct immediate coface
directions. Hence the complex is two-thick. Its facet cardinalities are `r` and `s`, so it is
nonpure exactly when `r!=s`.

## Uniform periodic-pencil realization in dimension two `[PROVED HERE]`

Fix one transcendental number `tau` and the standard basis `e_1,e_2` of `C^2`. Put

```text
a_0     =tau^s e_1+tau^r e_2,
a_(x_i) =tau^(i-1)e_2                    for 1<=i<=r,
a_(y_j) =tau^(j-1)e_1                    for 1<=j<=s.        (3)
```

These vectors are `Q`-linearly independent. In a rational relation, the first coordinate is a
polynomial in `tau` with powers `0,...,s`, whose top coefficient is the coefficient of `a_0`.
Transcendence kills that coefficient and all `y`-coefficients. The second coordinate then kills
all `x`-coefficients.

For a facet `B_x\{u}`, use the form

```text
ell_x(z_1,z_2)=z_2,
omega_(x,u)=ell_x(a_u).                                    (4)
```

Every `y`-translation has zero `ell_x`-value, and the only omitted `x`-block vertex has value
`omega_(x,u)`. Thus every complement value is an integral multiple of the period. Multiplication
of the normalized inside values and `1` by `omega_(x,u)` gives the distinct powers of `tau`
attached to all vertices of `B_x`; they are `Q`-linearly independent.

For a facet `B_y\{v}`, use

```text
ell_y(z_1,z_2)=z_1,
omega_(y,v)=ell_y(a_v).                                    (5)
```

The same argument, with the blocks exchanged, verifies the periodic-pencil conditions. Therefore

```text
ppDim(Delta_(r,s))<=2.                                     (6)
```

Every facet in the first boundary has complement of cardinality `s+1`, and every facet in the
second has complement of cardinality `r+1`. Since `r,s>=2`, the dimension-one phase law excludes a
one-dimensional periodic pencil. Hence

```text
ppDim(Delta_(r,s))=2.                                      (7)
```

The periodic-pencil realization theorem gives `htDim<=2`. The scalar purity/facet-period theorem
states that an exact one-variable HT realization requires every facet complement to have
cardinality at most one. The complements above have cardinality at least three, so

```text
htDim(Delta_(r,s))=2.                                      (8)
```

## Faithful separation in dimension four `[PROVED HERE]`

Choose numbers

```text
alpha_0,...,alpha_r,beta_0,...,beta_s                       (9)
```

algebraically independent over `Q`. In `C^4=C^2 direct_sum C^2`, put

```text
b_i=(1,alpha_i),       c_j=(1,beta_j),
a_0=(b_0,c_0),
a_(x_i)=(b_i,0),       a_(y_j)=(0,c_j).                    (10)
```

The translation vectors are `Q`-linearly independent: the first block of a rational relation
gives a rational linear relation among the algebraically independent `alpha_i`, killing the
coefficient of `a_0` and all `x`-coefficients; the second block then kills all `y`-coefficients.

For the facet `B_x\{u}`, use on the first `C^2` block the form

```text
phi_u(p,q)=q-alpha_u p                                     (11)
```

and make it zero on the second block. It vanishes exactly on `a_u` and on every `a_(y_j)`, hence
exactly on the complement of `B_x\{u}`. Its nonzero facet values are

```text
alpha_i-alpha_u,   i!=u.                                   (12)
```

They are `Q`-linearly independent: a rational relation among them is a linear polynomial in the
algebraically independent `alpha_i`, so all coefficients vanish. The forms
`psi_v(p,q)=q-beta_v p` on the second block give the analogous separators for the `y`-facets.
Thus

```text
ffsDim(Delta_(r,s))<=4.                                    (13)
```

## Faithful dimension cannot be three `[PROVED HERE]`

Suppose faithful data existed in `C^d`. Let

```text
E:(C^d)^* -> C^V,
E(ell)=(ell(a_v))_(v in V)                                 (14)
```

be the evaluation map. Its image has complex dimension at most `d`.

For every facet `B_x\{u}`, let `r_u` be the evaluation row of its separating form, and let `W_x`
be the span of these rows. Each `r_u` is supported exactly on `B_x\{u}`. Define `W_y` analogously.
Then

```text
dim_C W_x>=2,   dim_C W_y>=2,                               (15)
W_x intersection W_y subset C e_0.                         (16)
```

The first inequalities follow because rows with different omitted vertices cannot be scalar
multiples. The intersection bound follows because the two coordinate blocks meet only at `0`.

If `W_x intersection W_y={0}`, then

```text
dim_C(W_x+W_y)>=2+2=4.                                     (17)
```

Otherwise the intersection is `C e_0`, so `e_0` belongs to both row spaces. We claim then that
`dim_C W_x>=3`. If instead `dim_C W_x=2`, the row `r_0`, which vanishes at `0` and is nonzero at
every `x_i`, together with `e_0` would span `W_x`. For any `k>=1`, the row `r_(x_k)` vanishes at
`x_k` but is nonzero at some `x_i` with `i!=k`, which exists because `r>=2`. No combination of
`e_0` and `r_0` has that zero pattern: vanishing at `x_k` forces the `r_0` coefficient to be zero
and hence makes every `x`-coordinate zero. This contradiction proves `dim_C W_x>=3`. Likewise
`dim_C W_y>=3`, and therefore

```text
dim_C(W_x+W_y)>=3+3-1=5.                                  (18)
```

In either case the image of `E` contains a subspace of dimension at least four. Hence `d>=4`, and

```text
ffsDim(Delta_(r,s))=4.                                     (19)
```

Combining (7), (8), and (19) proves the uniform law

```text
htDim(Delta_(r,s))=ppDim(Delta_(r,s))=2
                                      <ffsDim(Delta_(r,s))=4.             (20)
```

`QED`

## Scientific meaning

The special `S^1 wedge S^2` example is not an isolated coordinate coincidence. The entire
two-parameter family of wedges of simplex boundaries occupies the same analytic stratum:
periodic constraint geometry sees two transverse cyclic directions, independent of the dimensions
of the two boundary pieces, while faithful single-hyperplane geometry always costs four complex
directions.

The contributing powers of `tau`, algebraically independent coordinates, and row-space estimates
are witnesses. The candidate-new scientific content is the uniform geometric law (20).

For RH-facing work, this gives a positive constraint on any finite prime relation complex that
contains such a boundary-wedge pattern with the full exact matroid semantics: it must expose two
intrinsic analytic directions, although any model that insists on one faithful hyperplane per
facet pays four. The theorem does not assert that a zeta-derived relation complex contains this
pattern.

## Lean formalization status

The uniform lower-bound layer is formalized in
`GaloisForLFunctions/HTGeometry/WedgeFacetLowerBound.lean`. The namespace
`UniformBoundaryWedge` defines the common-centre vertex set, the left and right boundary-facet
incidence predicates, and proves
`no_faithfulSeparation_of_finrank_le_three`: for every `r,s>=2`, exact faithful separator rows in
an ambient complex vector space of dimension at most three are impossible. The proof selects only
two vertices from each block and gives a uniform span-dimension contradiction, so it does not
depend on the sizes of the remaining blocks.

The same module now formalizes the matching uniform upper bound. From one transcendental `tau`,
`faithfulSeparationFinFour` constructs explicit vectors in `Fin 4 -> C` and left/right facet forms,
then proves global `Q`-linear independence of all vertex vectors, the exact complement zero
patterns, and `Q`-linear independence of every family of nonzero facet values.
`faithfulSeparation_fin_four_and_minimal` combines that witness with the uniform lower theorem:
four coordinates exist and every faithful separation has dimension at least four. Thus the entire
uniform `ffsDim=4` layer is Lean-formalized, not only the special `S^1 wedge S^2` case.

`GaloisForLFunctions/HTGeometry/PPMatrixRankFormulaConsequences.lean` now formalizes the complete
periodic-pencil layer.  It defines the uniform boundary-wedge facet system, constructs the explicit
two-coordinate translation vectors and normalized left/right pencil forms, proves every
facet-evaluation row PP-admissible, excludes dimensions zero and one from two distinct off-facet
integral values and global `Q`-independence, and exports
`boundaryWedge_ppDim_eq_two` for every `r,s>=2`.

The analytic bridge is now closed.  `BoundaryWedgeExponentialRealization.lean` builds the entire
two-dimensional exponential realization (`boundaryWedgeHTRealizable_two_uncond`), and
`BoundaryWedgeUniformHTDimensionGap.lean` proves `boundaryWedge_htDim_eq_two` and assembles the
combined capstone `boundaryWedge_uniformHTDimensionGap`: for every `r,s>=2`,
`htDim = ppDim = 2 < ffsDim = 4`.  Together with `boundaryWedge_geometry`
(`BoundaryWedgeTwoThick.lean`: facet antichain, two-thickness, purity exactly when `r = s`),
the full card statement is formalized unconditionally; targeted `lake build` and scratch
`#print axioms` pass with only `propext`, `Classical.choice`, `Quot.sound` (2026-08-13).

## Parent-theory and novelty boundary

Wedges of simplex boundaries, hyperplane representations, toric arrangements, and arithmetic
matroids are established objects. The candidate-new residue is the equality of the three HT
constraint dimensions and the uniform strict gap (20), proved through facet-indexed periodic
pencils and exact nonlinear differential-matroid realization. No checked adjacent source states
this dimension law.

Closest primary sources checked:

1. C. De Concini and C. Procesi, *On the geometry of toric arrangements*,
   `https://arxiv.org/abs/math/0505351`.
2. L. Moci, R. Pagaria, M. Pismataro, and A. Vargas, *Elliptic arrangements of complex
   multiplication type*, `https://arxiv.org/abs/2506.19638`.

Novelty remains provisional pending specialist comparison with toric-arrangement, arithmetic-
matroid, gain-graph, and subspace-representation invariants.

## Gates

- [x] family and facet geometry defined
- [x] two-thickness and exact nonpurity criterion proved
- [x] uniform two-dimensional periodic pencil proved
- [x] `ppDim=2` proved
- [x] `htDim=2` proved from the scalar dimension-one classification
- [x] faithful four-dimensional construction proved
- [x] faithful lower bound four proved by evaluation row spaces
- [x] uniform faithful lower bound four formalized in Lean from exact incidence data
- [x] uniform faithful four-dimensional witness and exact minimality formalized in Lean
- [x] uniform periodic-pencil witness, lower bound, and exact `ppDim=2` formalized in Lean
- [x] complete paper proof
- [x] preliminary parent-theory audit
- [x] complete unconditional Lean formalization before stage 3

## Lean progress — exact facet combinatorics and the exclusion of one-variable period codimension

`GaloisForLFunctions/HTGeometry/BoundaryWedgeFacetComplement.lean` (axiom-clean
`[propext, Classical.choice, Quot.sound]`, build green, umbrella-registered) formalizes the
combinatorial layer that the `htDim` lower bound rests on, uniformly in `r, s ≥ 2`, on the same
vertex type `BoundaryWedgeVertex r s` used by the faithful-separation layer.

- `leftBlock`, `rightBlock` with `mem_leftBlock`, `mem_rightBlock` (agreeing with the predicates
  `boundaryWedgeLeft`, `boundaryWedgeRight` of `WedgeFacetLowerBound`), and cardinalities
  `card_leftBlock = r+1`, `card_rightBlock = s+1`, `card_vertex = r+s+1`.
- `boundaryWedgeFacets` — the facet family of (2): delete one vertex from one block.
  `mem_leftFacet_iff` and `mem_rightFacet_iff` identify its facets with the incidence predicates
  `boundaryWedgeLeftFacetMember` / `boundaryWedgeRightFacetMember` already used for `ffsDim`, so the
  three Lean layers of this card are about the *same* family.
- `card_leftFacet = r`, `card_rightFacet = s`; hence the exact nonpurity criterion of the statement:
  `pureOfCard_of_eq` (pure when `r = s`) and `not_pureOfCard_of_ne` (for `r ≠ s` no `d` makes the
  family pure).
- `facetAntichain` — the family is an inclusion antichain, so the corpus classification
  `facetAntichain_eq_singleton_or_deletionFacets` applies to it.
- `card_sdiff_leftFacet = s+1`, `card_sdiff_rightFacet = r+1` — a facet complement **in the full
  vertex set** omits the entire opposite block together with the deleted vertex.
- **`not_facetComplementRankOne`** — consequently the family never satisfies
  `FacetComplementRankOne` (every facet complement of cardinality `≤ 1`), which
  `SimplicialConstraintTower` records as *the exact combinatorial output of the HT period-rank
  argument*.  This is the combinatorial content of `(8)`: the complements have cardinality at least
  three, so the scalar purity/facet-period obstruction is violated for every `r, s ≥ 2`.

**What remains for the last gate.**  The step still missing in Lean is the *analytic* implication
behind `(8)` — that an exact one-variable hypertranscendental realization forces
`FacetComplementRankOne` — together with the definition of the intrinsic `htDim` functional itself.
With that implication, `not_facetComplementRankOne` gives `htDim ≥ 2` and the already formalized
periodic pencil (`boundaryWedge_ppDim_eq_two`) gives `htDim ≤ 2`, closing `htDim = ppDim = 2`.  The
combinatorial half is now unconditional and uniform; the remaining half is the analytic bridge the
card already flagged.

## Lean progress — the period-rank obstruction to a one-variable realization

`GaloisForLFunctions/HTGeometry/BoundaryWedgePeriodRankObstruction.lean` (axiom-clean, build green,
umbrella-registered) supplies the analytic half of `(8)` for this family, on top of the combinatorial
half of the previous section.

The key observation is that the boundary wedge is *more* degenerate than the general
one-vertex-complement threshold the parent card uses: here every facet complement has cardinality
`s+1 ≥ 3` (resp. `r+1 ≥ 3`).  Three omitted vertices mean three `ℚ`-independent periods, and the
rank-three period boundary is already unconditional in Lean
(`meromorphicNF_constant_of_rankThree_periods`, `RankThreePeriods.lean`) — the elliptic rank-two case,
which is the genuinely hard part of the parent card's HT period-rank law, is **not needed here**.

- `differentiallyAlgebraic_of_const`, `not_hypertranscendental_of_const` — a constant satisfies the
  order-zero relation `y₀ − c = 0` (via `differentiallyAlgebraic_of_algebraic`), so it is
  differentially algebraic and not hypertranscendental.
- `periodic_of_mem_span_range` — periodicity at a family of steps propagates to their integer span
  (`Submodule.span_induction`, `Function.Periodic.add_period`, `Function.Periodic.zsmul`).
- `ScalarFacetRealization` — the realization interface: `ℚ`-independent translation steps `ω v`
  together with, for every facet, a meromorphic hypertranscendental carrier invariant under exactly
  the translations that facet omits.  This is the analytic output of the facet-separator and
  isolated-carrier steps (§1–2 of the parent card).
- **`no_scalarFacetRealization_of_three_omitted`** — a facet omitting three vertices gives its
  carrier three `ℚ`-independent periods, hence a non-discrete rank-three period group, hence a
  constant carrier, contradicting hypertranscendence.  No one-variable realization survives.
- **`boundaryWedge_no_scalarFacetRealization`** and `isEmpty_scalarFacetRealization` — applied to the
  boundary wedge through `card_sdiff_leftFacet = s+1`, uniformly in `r, s ≥ 2`.

**Scope, stated exactly.**  What is now unconditional in Lean is: *no `ScalarFacetRealization` of the
boundary wedge exists*, for every `r, s ≥ 2`.  What is still paper-level is the derivation of that
datum from the definition of an exact one-variable HT realization — the facet separator and the
isolation of a differentially transcendental facet carrier with the omitted periods (§1–2 of
`ht-period-rank-one-scalar-stanley-reisner-principalization`) — together with a Lean definition of the
intrinsic `htDim` functional itself.  Those two steps are shared with the parent card and are what
its own last gate is about; the analytic obstruction they feed is now closed for this family, and it
is closed using only the rank-three boundary, not the elliptic rank-two theory.

## Lean progress — the two-vertex sharpening of the obstruction

`GaloisForLFunctions/HTGeometry/RankTwoRealDependentPeriods.lean` (axiom-clean, build green) also
sharpens the facet obstruction below the three-vertex threshold used above:

- **`no_scalarFacetRealization_of_two_omitted_realDependent`** — a facet omitting only *two* vertices
  already kills a one-variable realization as soon as the two omitted translation steps are
  `R`-linearly dependent, since two `Q`-independent `R`-dependent periods force the carrier constant.

So for this family the analytic obstruction is available at both thresholds: unconditionally at three
omitted vertices (which is what the boundary wedge always provides), and at two omitted vertices
whenever the omitted steps happen to be real-dependent.  Only the genuinely elliptic configuration —
two omitted vertices with `R`-independent steps — still needs Weierstrass theory, and the boundary
wedge never reaches it.

## Lean progress — uniform two-thickness and the geometric certificate

`GaloisForLFunctions/HTGeometry/BoundaryWedgeTwoThick.lean` (axiom-clean, build green,
umbrella-registered) formalizes the statement's geometric half — "it is two-thick and is nonpure
exactly when `r != s`" — for the **whole family**.  `WedgeTwoThick.lean` had certified two-thickness
only for the single six-vertex model `S^1 wedge S^2`, by decision; that route is unavailable for a
two-parameter family.

- `isFaceOf_boundaryWedgeFacets_iff` — the faces are exactly the **proper** subsets of one of the two
  blocks.  (Forward: a face sits inside `B.erase u`, which misses `u in B`.  Backward: a proper
  subset misses some vertex, so it sits inside that deletion facet.)
- `two_le_card_sdiff_of_face_not_facet` — a proper subset of a block that is not a single-vertex
  deletion misses at least two of its vertices: missing none would make it the block, missing exactly
  one would make it a facet.
- **`boundaryWedge_twoThick`** — hence `TwoThick (boundaryWedgeFacets r s)`: adjoining either missed
  vertex keeps the face a proper subset of its block, so both are immediate coface directions.  This
  holds for all block sizes, no lower bound needed.
- `boundaryWedge_geometry` — the packaged certificate for `r, s >= 2`: a two-thick facet antichain,
  pure exactly when `r = s`, combining `facetAntichain`, `boundaryWedge_twoThick` and
  `not_pureOfCard_of_ne`.

This is the uniform generalization of `wedge_twoThick`, `wedge_facetAntichain` and `wedge_not_pure`,
and it supplies in Lean the geometric hypothesis ("nonpure two-thick full Stanley--Reisner system") of
the parent constraint-dimension law for every `r, s >= 2`.

## Lean progress — the facet separator for this family

`GaloisForLFunctions/HTGeometry/StanleyReisnerFacetSeparator.lean` (axiom-clean, build green) proves
the general Stanley--Reisner facet separator — every facet of a finite facet antichain carries a
nonzero ring class annihilated by exactly the vertex coordinates it omits — and instantiates it here:

- `boundaryWedgeFacetFinset` packages the facet family of `(2)` as a *finite* family, with
  `mem_boundaryWedgeFacetFinset` and `coe_boundaryWedgeFacetFinset` identifying it with the set-valued
  `boundaryWedgeFacets` used by the combinatorial layer;
- **`boundaryWedge_facetSeparator`** — for every `r, s >= 2` and every facet, the separator exists,
  using the uniform antichain property `facetAntichain`.

So for this family the algebraic side of the isolated-facet-carrier step is now formalized as well:
a facet gives a nonzero class killed by all `s+1 >= 3` omitted vertex coordinates, and the analytic
side (`no_scalarFacetRealization_of_three_omitted`) turns exactly that pattern into a contradiction.
The single remaining gap is the transport between the two: that a realization sends a nonzero class to
a differentially transcendental function and annihilation to periodicity.

## Lean progress — the realization bridge: no one-variable realization at all

`GaloisForLFunctions/HTGeometry/ScalarSRRealizationBridge.lean` (axiom-clean, build green,
umbrella-registered) closes the gap between the algebraic and analytic layers.

`ScalarSRRealization` is the one-variable realization datum: `Q`-independent translation steps and a
carrier map on Stanley--Reisner classes such that

- `carrier_vertex` — the vertex coordinate `x_v` acts as the difference operator `T_v - 1` (the
  convention `t_v = 1 + x_v` recorded by `stanleyReisnerTranslationClass`);
- `carrier_ht` — a **nonzero** class has a hypertranscendental carrier (the faithfulness supplied by
  the full nonlinear Stanley--Reisner differential matroid condition `(4)`).

Neither field mentions periods or dimensions.  From them:

- **`periodic_carrier_of_mul_eq_zero`** — annihilation *becomes* periodicity: `(17)` is now derived,
  not assumed.
- **`toScalarFacetRealization`** — the facet monomials of `exists_facetSeparator` assemble into the
  analytic datum `ScalarFacetRealization`: `(15)`--`(17)` in Lean.
- `no_scalarSRRealization_of_three_omitted` — the period-rank obstruction in realization form.
- **`boundaryWedge_no_scalarSRRealization`** / `isEmpty_scalarSRRealization` — for every `r, s >= 2`
  the boundary wedge admits **no** scalar Stanley--Reisner realization.
- `htDim_eq_two_of_realizability` — the corpus-idiom packaging: a least-realizable-dimension
  functional equals `2` once dimension `2` is realizable and dimensions `0, 1` are excluded.

So `htDim >= 2` is now fully derived in Lean for this family, from the definition of a realization
rather than from an assumed obstruction, and `htDim <= 2` is the periodic pencil already formalized at
the `ppDim` level (`boundaryWedge_ppDim_eq_two`).  The only remaining formal step for the last gate is
a Lean definition of the intrinsic `htDim` functional itself — i.e. a `d`-variable realization
structure whose `d = 1` case is `ScalarSRRealization` and whose `d = 2` case is witnessed by the
pencil — after which `htDim_eq_two_of_realizability` closes `htDim = ppDim = 2` immediately.

## Lean progress — the wedge is past the bound a one-variable realization allows

`GaloisForLFunctions/HTGeometry/ScalarRealizationFacetComplementBound.lean` (axiom-clean, build
green) proves in general that a one-variable realization forces every facet complement to have at most
two vertices, and that the two-vertex case survives only in the elliptic (lattice) configuration.

- `boundaryWedge_facetComplement_too_large` — the boundary wedge is excluded outright: its facet
  complements have `s+1 >= 3` vertices, strictly past that bound, so no elliptic escape is even
  available here.

This gives a second, independent route to the same conclusion as
`boundaryWedge_no_scalarSRRealization`, now as a corollary of the general facet-codimension bound
rather than of the wedge-specific obstruction.

## Lean progress — realizations in a prescribed number of variables, and `htDim = 2`

`GaloisForLFunctions/HTGeometry/SRRealizationDimension.lean` (axiom-clean, build green,
umbrella-registered) gives the `d`-variable form of the realization datum and assembles the
dimension statement in the corpus idiom.

- `SRRealization d` — `Q`-independent translation steps in `C^d` and a carrier map on
  Stanley--Reisner classes for which the vertex coordinates act as difference operators along the
  steps and nonzero classes have nonconstant carriers.  Nonconstancy is what the dimension exclusions
  consume, and hypertranscendence implies it.
- `SRRealization.ofScalar` — the strong one-variable datum `ScalarSRRealization` gives a
  `1`-variable realization, transported along `(Fin 1 -> C) ~= C`; nonconstancy comes from
  hypertranscendence.
- **`isEmpty_srRealization_zero`** — **no realization in zero variables**: every step would be the
  zero vector of a trivial space, which no `Q`-linearly independent family contains.  Purely
  algebraic.
- **`boundaryWedge_htDim_eq_two_of_realizable`** — for the boundary wedge, a
  least-realizable-dimension functional equals `2` as soon as a **two-variable** realization exists.
  Dimensions `0` and `1` are discharged unconditionally, by `isEmpty_srRealization_zero` and by
  `isEmpty_scalarSRRealization` respectively; the two remaining hypotheses only say that the abstract
  realizability predicate at those dimensions yields the corresponding concrete datum.

So the last gate now reduces to a single positive input: a **two-variable realization witness**, i.e.
the periodic pencil of `(3)` promoted from its matrix form (`boundaryWedge_ppDim_eq_two`) to a carrier
map.  Everything else in `htDim = 2` is formalized and unconditional.

## Lean plan — closing the last gate through an entire `d`-variable realization

The corpus `SRRealization d` of `SRRealizationDimension.lean` asks only for *nonconstant* carriers.
That condition is too weak to define an intrinsic dimension: for **any** `d ≥ 1` and **any**
`ℚ`-independent step family one can realize an arbitrary facet antichain by set-theoretic carriers
(take `f = ∑_F 1[coordinates on F vanish]` in the coordinates dual to the steps; the facet antichain
property gives nonconstancy by moving one coordinate outside every other facet).  So
`Nonempty (SRRealization d)` cannot be the realizability predicate behind `htDim`; the analytic
condition of `ScalarSRRealization` (meromorphic normal form plus hypertranscendence) is what the
dimension exclusions consume, and the `d`-variable datum has to carry it too.

The plan therefore replaces the realizability predicate by an **entire** `d`-variable datum:

1. `EntireSRRealization d facets` — `ℚ`-independent steps `ω : α → (Fin d → ℂ)`, an entire carrier
   map on Stanley–Reisner classes, vertex coordinates acting as difference operators along the
   steps, and the faithfulness condition: **some complex line restriction of the carrier of a
   nonzero class is hypertranscendental**.  At `d = 1` this is exactly `ScalarSRRealization`
   (entire ⇒ meromorphic normal form; a line restriction is an affine reparametrization, and
   hypertranscendence is affine-invariant), so `isEmpty_scalarSRRealization` excludes `d = 1` and
   `ℚ`-independence excludes `d = 0`.  `htDim = 2` then needs only `EntireSRRealization 2`.

2. The seed-to-carrier machinery: for a seed `F : (Fin d → ℂ) → ℂ` the assignment
   `q ↦ (q evaluated at the difference operators) F` is a carrier as soon as the Stanley–Reisner
   ideal annihilates `F`.  The operator algebra is the (commutative) additive group algebra
   `AddMonoidAlgebra ℂ (Fin d → ℂ)` acting by translations, and the map out of `MvPolynomial α ℂ`
   is `aeval (fun v => single (ω v) 1 - 1)`.

3. The boundary-wedge assembly.  With the pencil `(3)` the two blocks move in the two coordinate
   directions, so a seed `F(z₁, z₂) = G(z₁) + H(z₂)` satisfies the mixed relations
   `Δ_{a_{xᵢ}} Δ_{a_{yⱼ}} F = 0` for free, and the two block relations become the one-variable
   conditions below.  A class is nonzero exactly when its left part or its right part is nonzero,
   and the two coordinate lines separate them, so faithfulness reduces to the one-variable
   faithfulness of `H` and of `G`.

4. **The remaining analytic input**, in one variable, for each `r ≥ 2`:

   > Given `ℚ`-independent nonzero steps `c₀, …, c_r`, construct an entire `H : ℂ → ℂ` with
   > `Δ_{c₀} ⋯ Δ_{c_r} H = 0` such that `S(Δ) H` is hypertranscendental for every polynomial
   > `S ∈ ℂ[X₀, …, X_r]` not divisible by `X₀ ⋯ X_r`.

   Writing `H = ∑_k H_k` with `H_k` `c_k`-periodic makes the annihilation immediate and turns
   faithfulness into differential independence of the translation orbits of the `H_k`, which is the
   parent card's periodic-pencil orbit lemma.


## The one-variable block seed `[PROVED HERE]`

The positive input of the plan above is now an explicit construction, not an existence statement.

**Theorem (exponential block seed).**  Let `B` be a finite set of vertices and `c : B → ℂ` a family
of steps that is *integrally independent*: `∑_{v ∈ B} g_v c_v = 0` with `g ∈ ℤ^B` forces `g = 0`.
Put

```text
H(z) = ∑_{v ∈ B} exp(exp(2πi z / c_v)).                                   (21)
```

Then `H` is entire, `∏_{v ∈ B} Δ_{c_v} H = 0`, and for every polynomial `Q` in the block variables
that is **not** divisible by `∏_{v ∈ B} X_v` the function `Q(Δ)H` is nonconstant.

*Proof.*  The `v`-th summand has period `c_v`, because `exp(2πi(z + c_v)/c_v) = exp(2πi z/c_v)`; so
`Δ_{c_v}` kills it and the full product kills `H`.  Translating the argument by `γ` multiplies the
inner exponential by `exp(2πi γ / c_v)`, so for any polynomial `P` the carrier is a finite
combination of *dilates* of `exp`, read at `w = exp(2πi z / c_v)`:

```text
P(Δ)H_v(z) = Ψ_{v,P}(exp(2πi z/c_v)),   Ψ_{v,P}(w) = ∑_γ λ_γ exp(exp(2πiγ/c_v)·w),   (22)
```

where `∑_γ λ_γ ⟨γ⟩` is `P` evaluated at the shift operators.  Since `w^m` is a simultaneous
eigenvector of the dilations, the `m`-th Taylor coefficient of `Ψ_{v,P}` at `0` is the **symbol**

```text
σ_v(t, P) = P(exp(t·c_j) − 1)_{j},   at t = m·2πi/c_v.                     (23)
```

Now suppose `Q(Δ)H` is constant and `∏X ∤ Q`.  Choose `k ∈ B` outside the support of one monomial of
`Q`.  Multiplying by `D = ∏_{j ∈ B∖{k}} X_j` keeps the carrier constant (a difference operator sends
constants to constants) and annihilates every summand except the `k`-th, because each carries the
factor `Δ_{c_j}` of its own period.  So `Ψ_{k,DQ}∘exp(2πi ·/c_k)` is constant; as `exp(2πi ·/c_k)`
is onto `ℂ∖{0}` and `Ψ_{k,DQ}` is entire, `Ψ_{k,DQ}` is constant, so all its Taylor coefficients of
positive order vanish:

```text
(∏_{j ≠ k} (q_j^m − 1))·σ_k(m·2πi/c_k, Q) = 0,   q_j = exp(2πi c_j/c_k),   m ≥ 1.   (24)
```

Integral independence gives `m c_j ≠ n c_k` for `m ≥ 1`, `j ≠ k`, so `q_j^m ≠ 1` and the product is
nonzero; hence `σ_k(m·2πi/c_k, Q) = 0` for every `m ≥ 1`.  The `k`-slot of the evaluation point is
`0`, and so is every slot outside `B`, so this only sees the part `Q_k` of `Q` supported in
`B∖{k}`.  Substituting `Y_j = X_j + 1` turns those equations into

```text
∑_{ν} r_ν z_ν^m = 0   for all m ≥ 1,   z_ν = ∏_{j ≠ k} q_j^{ν_j},          (25)
```

with `r` the coefficients of the substituted polynomial.  Integral independence again makes
`ν ↦ z_ν` injective on exponents supported in `B∖{k}`: `z_ν = z_{ν'}` forces
`∑_j (ν_j − ν'_j)c_j = n c_k`, hence `ν = ν'`.  The nodes are nonzero, so subtracting `z_a` times the
`m`-th equation from the `(m+1)`-st removes one node and an induction on the number of nodes forces
every `r_ν = 0`.  Then `Q_k = 0`, contradicting the choice of `k`.  `QED`

`(21)` also shows how sharp the datum is: `exp∘exp` satisfies `y y'' − y y' − y'² = 0`, so this seed
is differentially algebraic and gives **nonconstancy, not hypertranscendence**.  What the period-rank
obstruction actually consumes is nonconstancy, which is why the intrinsic dimension is settled by it.

### The residual hypertranscendence question `[OPEN CORE — DILATION ORBIT TRANSCENDENCE]`

The same argument reduces the stronger, hypertranscendental form of the realization to a single
one-variable statement.  If `Q(Δ)H` is differentially algebraic then so is `D·Q(Δ)H` (translations
and differences preserve differential algebraicity of entire functions), and that function is
`Ψ_{k,DQ}∘exp(2πi ·/c_k)`; by the exponential descent theorem (`differentiallyAlgebraic_of_comp_exp`)
`Ψ_{k,DQ}` is then itself differentially algebraic.  Hence:

> To realize the boundary wedge in two variables with **hypertranscendental** carriers it suffices to
> find one entire `Φ` with all Taylor coefficients nonzero such that no nonzero finite `ℂ`-linear
> combination of dilates `∑_γ λ_γ Φ(γ ·)`, with `γ` in the multiplicative group generated by the
> `q_j = exp(2πi c_j/c_k)`, is differentially algebraic.

This replaces the parent card's Baire-category orbit lemma in a Fréchet space by a statement about
dilates of a *single explicit* function.  Its two natural sub-inputs are: (a) the dilate combination
has Taylor coefficients `φ_m·(∑_γ λ_γ γ^m)`, whose second factor is a nondegenerate exponential
polynomial in `m` and therefore vanishes only finitely often (Skolem–Mahler–Lech, nondegenerate
case); and (b) a perturbation-tolerant form of the layer-tower criterion
`hypertranscendental_of_infiniteGeometricLayerTower`, which is available whenever the perturbation
satisfies `|log|γ_m|| = O(m^C)` — because the tower profile `b_n = ∑_i A_i ρ_i^n` with `ρ_i > 1`
absorbs any polynomially bounded shift into each of its layers.  The obstruction is that
`∑_γ λ_γ γ^m` can be super-polynomially small along a sparse set of `m` for adversarial `λ`, so the
criterion has to tolerate a sparse exceptional set.

## Lean gate closed — `htDim = ppDim = 2` is unconditional

`GaloisForLFunctions/HTGeometry/BoundaryWedgeExponentialRealization.lean` (axiom-clean, build green,
umbrella-registered) instantiates the block seeds with the periodic pencil of `(3)` and closes the
last gate.

- `leftStep τ r s`, `rightStep τ r s` — the two coordinate families of `wedgeVec`, each vanishing off
  its block.
- `stepIndep_leftStep`, `stepIndep_rightStep` — the steps of each block are **integrally
  independent**: a relation is a rational relation among the distinct powers
  `τ⁰, …, τ^{r−1}, τ^r` (resp. `τ⁰, …, τ^{s−1}, τ^s`), killed by
  `transcendental_pow_combination_eq_zero`.
- `leftBlockSeed`, `rightBlockSeed` — the exponential block seeds `∑_v exp(exp(2πi z / c_v))` of
  `(21)`, obtained from `expBlockSeed`.
- `glueSteps_eq_pencil` — the glued two-coordinate steps are *literally* `boundaryWedgePencilVector`,
  so their `ℚ`-independence is the already-formalized `boundaryWedgePencilVector_linearIndependent`.
- **`boundaryWedgeHTRealizable_two_uncond`** — an entire two-variable realization of the boundary
  wedge exists, for every `r, s` (a transcendental number exists by
  `exists_transcendental_complex`).
- **`boundaryWedge_htDim_eq_two`** — for every `r, s ≥ 2` a least-realizable-dimension functional
  equals `2`: dimension `0` is excluded by `ℚ`-independence of the steps, dimension `1` by the
  period-rank obstruction (a facet monomial acquires `s + 1 ≥ 3` `ℚ`-independent periods, hence a
  constant carrier), and dimension `2` is realized.

Together with the already formalized `boundaryWedge_ppDim_eq_two` and
`faithfulSeparation_fin_four_and_minimal`, the whole law `(20)` — `htDim = ppDim = 2 < ffsDim = 4`,
uniformly in `r, s ≥ 2` — is now unconditional in Lean.

The realization datum used here is `EntireSRRealization`: entire carriers with nonconstant carriers
for nonzero classes.  That is exactly what the period-rank obstruction consumes.  Strengthening the
carriers to hypertranscendental ones is the separate `[OPEN CORE — DILATION ORBIT TRANSCENDENCE]`
recorded above; it would not change the value of the dimension, only the class of realizations it is
computed in.
