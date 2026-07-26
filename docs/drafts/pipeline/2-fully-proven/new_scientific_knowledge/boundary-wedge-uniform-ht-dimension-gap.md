# Wedges of simplex boundaries have uniform intrinsic HT dimension two and faithful dimension four

- **ID:** `boundary-wedge-uniform-ht-dimension-gap`
- **Stage:** 2-fully-proven
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

The remaining Lean work before stage 3 is therefore only the analytic bridge defining the full
intrinsic `htDim` realization and proving its equality with the already formalized `ppDim=2` value.

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
- [ ] complete unconditional Lean formalization before stage 3

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
