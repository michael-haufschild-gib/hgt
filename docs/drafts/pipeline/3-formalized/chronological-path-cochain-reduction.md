# Path cochains: an explicit three-vertex reduction

**Status:** formalized in Lean 4, unconditionally and in full (200 declarations across four modules; see the Lean section below). This is an elementary proof of the classical path-independence-complex suspension law, not a novelty claim. It supports the spectrum branch in `../1-in-progress/chronological-topological-spectrum.md`.

## Actual face complex and grading

Let P_n have vertices 0,…,n−1 and edges between consecutive integers. Faces are all nonadjacent subsets, including the empty face. Reduced cochains are functions on these faces. A cochain in occupation degree j is supported on faces of cardinality j; its topological degree is j−1. The coboundary is the usual alternating sum over vertex deletions. Thus the empty-face slot is included and the differential raises j by one.

The corpus already proves the incidence-sign identities, δ²=0, and full-simplex cone contraction in `SimplicialCochainComplex.lean` and `SimplexConeContraction.lean`. These are suitable algebraic primitives. Existing `HochsterCohomologyEquiv.lean` defines actual reduced-cohomology quotients, but its codimension indexing needs care; do not replace graded cohomology with an Euler-count recurrence.

## Explicit reduction for n≥3

Write B for the tail path on vertices 3,…,n−1. Define maps on face cochains:

`(Kf)(σ) = 0` if 0 or 1 belongs to σ; otherwise `(Kf)(σ)=f({0}∪σ)`.

`(qf)(τ)=f({1}∪τ)−f({0}∪τ)` for tail faces τ.

`(Jg)(σ)=g(σ\{1})` if 1 belongs to σ; otherwise `(Jg)(σ)=0`.

All faces in these evaluations are legitimate. If 1∈σ, the path condition excludes 0 and 2, so σ\{1} lies in B. If 1∉σ, adjoining 0 is legitimate. K and q lower occupation degree by one; J raises it by one.

The exact identities on path faces are

`δK+Kδ = id−Jq`, `qJ=id`, `qδ=−δq`, `δJ=−Jδ`.

For σ containing 0, the sole nonzero contribution in δK removes 0, giving f(σ), and Jq and Kδ vanish. For σ containing 1, the sole nonzero contribution in δK removes 1 and equals f({0}∪(σ\{1})); Kδ vanishes, so the residual is qf. For σ containing neither 0 nor 1, the ordinary cone identity applies and Jq vanishes. The minus signs in the chain-map laws arise because the inserted vertex precedes every tail vertex; terms deleting that inserted vertex cancel in qδ. Also qJ=id follows directly since Jg vanishes on faces containing 0.

Consequently q and J induce inverse cohomology isomorphisms with a shift of one in occupation degree: every cocycle differs from Jqf by the explicit coboundary δKf, and q detects exactly when this residual is a coboundary. This proves `H̃^(j−1)(Ind(P_n)) ≅ H̃^(j−2)(Ind(P_(n−3)))` with the augmentation slots retained.

For natural-number indexing in Lean, state the shift as occupation `j+1` on P_(n+3) versus occupation j on P_n. Treat occupation zero on nonempty paths separately as zero. Do not let truncated natural subtraction turn a negative-degree group into the augmentation slot.

## Base cases and actual multiplicities

- n=0: only the empty face; one class in occupation degree 0.
- n=1: the two-term augmented simplex complex is exact.
- n=2: faces ∅,{0},{1}; the differential sends a scalar to the two equal singleton values. The difference of singleton values identifies one class in occupation degree 1; all other degrees vanish.

Induction gives one class in occupation j for n=3j or n=3j−1 (where the length is nonnegative), and none for n=3j+1. For the physical pairing paths n=2d−1, d≥1, this gives exactly one class at every occupation j≥1 across the whole degree tower. More explicitly, d=3k+2 supplies occupation 2k+1 and d=3k+3 supplies occupation 2k+2; d=3k+1 contributes nothing.

This is the grading needed for the eta trace. The coefficients must be obtained from this actual cohomology reduction in Lean; a function defined to equal these multiplicities would not establish the geometric spectrum.

## Implementation order

Define finite path faces and their relation to nonnegative separated-support probes. Prove the local maps and identities on actual face evaluations, reusing the existing sign and cone lemmas. Construct or connect the graded quotient and induced inverse maps. Then prove the base cases, the all-degree multiplicity classification, and the paired trace. Relabeling the tail by subtracting three requires an order-preserving bijection so that incidence signs transport correctly.

## Lean formalization (complete, unconditional)

Four modules, 200 declarations, all wired into `GaloisForLFunctions/HTGeometry.lean` and all
depending only on `propext`, `Classical.choice`, `Quot.sound`.

| Module | Declarations | Content |
|---|---:|---|
| `HTGeometry/PathIndependenceProbe.lean` | 10 | `pathProbeSupport`, `isPathFace_pathProbeSupport`, `pathFaceProbe`, `isPathFace_iff_exists_nonneg_probe`, `mem_cubicFaces_iff_isPathFace` |
| `HTGeometry/PathIndependenceCochain.lean` | 103 | `IsPathFace`, `IsTailFace`, the face-restricted differentials, the occupation grading, the four identities, and `pathCohomologyEquiv` |
| `HTGeometry/PathIndependenceShift.lean` | 38 | the `v ↦ v+3` relabeling, `shiftCochain`/`unshiftCochain`, `tailCohomologyEquiv`, `pathCohomologyShiftEquiv` |
| `HTGeometry/PathIndependenceMultiplicity.lean` | 49 | the three base cases, `pathCohomology_nonempty_equiv`, `pathCohomology_subsingleton`, `pathCohomology_finrank`, and the paired tower |

### Faces and separated-support probes

`IsPathFace n σ` is `(∀ v ∈ σ, v < n) ∧ ∀ v ∈ σ, v + 1 ∉ σ`, with the empty face included.
`isPathFace_iff_exists_nonneg_probe` proves that these are exactly the supports of the
nonnegative probes on `{0,…,n−1}` whose adjacent coordinates never activate together, and
`mem_cubicFaces_iff_isPathFace` identifies the corpus's `cubicFaces` (the physical cubic norming
complex, facets `{0,2,4}`, `{0,3}`, `{1,3}`, `{1,4}`) with the faces of `P_5`.

### The four identities

The differentials are the corpus's `simplicialCoboundary` **evaluated only at faces**
(`pathCoboundary`, `tailCoboundary`); the support model of the occupation grading
(`pathSupported`, `tailSupported`) works only with the face-restricted differential, because a
non-face can have all its facets be faces. The guarded maps `pathConeFace`, `pathTailMapFace`,
`pathInclFace` satisfy, as equalities of cochains,

* `pathTailMapFace_pathInclFace_eq` — `qJ = id` (needs `1 < n`),
* `tailCoboundary_pathTailMapFace` — `qδ = −δq` (needs `1 < n`),
* `pathCoboundary_pathInclFace_eq` — `δJ = −Jδ`,
* `pathCoboundary_pathConeFace_add_eq` — `δK + Kδ = id − Jq` (needs `0 < n`),

and `pathCocycles_sub_pathInclFace_pathTailMapFace` is the card's displayed conclusion at cochain
level: every path cocycle differs from `Jqf` by the explicit coboundary `δKf`. These give
`pathCohomologyEquiv F n j (hn : 1 < n) : pathCohomology F n (j+1) ≃ₗ[F] tailCohomology F n j`.

### The relabeling and the shift

`shiftCochain`/`unshiftCochain` transport cochains along `v ↦ v+3`. Because the relabeling is
order preserving, `faceSign_shiftSet` shows the incidence signs transport unchanged and
`shiftCochain_simplicialCoboundary` is a chain map with no sign. Hence
`tailCohomologyEquiv F n j : tailCohomology F (n+3) j ≃ₗ[F] pathCohomology F n j` and, composing,

```
pathCohomologyShiftEquiv F n j : pathCohomology F (n+3) (j+1) ≃ₗ[F] pathCohomology F n j
```

which is the card's displayed shift in natural-number indexing.

### Base cases

* `pathCohomologyZeroEquiv : pathCohomology F 0 0 ≃ₗ[F] F` — the only face is `∅`,
  `pathCoboundary_zero_path` shows the differential vanishes identically, and
  `emptyEval_bijective` identifies the cocycles with `F` by evaluation at `∅`.
* `pathCohomology_one_one_subsingleton` — for `n = 1` the augmented two-term complex is exact;
  `mem_pathCoboundaries_one` writes every occupation-one cochain as `δ` of a multiple of the
  empty-face indicator.
* `pathCohomologyTwoEquiv : pathCohomology F 2 1 ≃ₗ[F] F` — `pairDiff` (the difference of the two
  singleton values) kills the coboundaries by `pathCoboundary_singleton_zero` and
  `pathCoboundary_singleton_one`, and `pathCohomologyPairMap_bijective` proves it is an
  isomorphism.
* `pathCohomology_occupation_zero_subsingleton` — occupation zero on a nonempty path vanishes
  (`pathCocycles_zero_eq_bot`), so truncated natural subtraction never turns a negative-degree
  group into the augmentation slot.

### The classification

By induction on the occupation degree with `pathCohomologyShiftEquiv` as the step:

```
pathCohomology_nonempty_equiv : (n = 3*j ∨ n+1 = 3*j) → Nonempty (pathCohomology F n j ≃ₗ[F] F)
pathCohomology_subsingleton   : ¬(n = 3*j ∨ n+1 = 3*j) → Subsingleton (pathCohomology F n j)
pathCohomology_finrank (F : Field) :
    Module.finrank F (pathCohomology F n j) = if n = 3*j ∨ n+1 = 3*j then 1 else 0
```

so there is exactly one class in occupation `j` for `n = 3j` and for `n = 3j−1`, and none for
`n = 3j+1`. The multiplicities are the actual rank of the reduced cohomology subquotient, not a
function defined to equal them.

### The paired trace

For the pairing paths `n = 2e+1`:

* `pathCohomology_pairedPath_odd` — `e = 3k+1` gives `n = 6k+3` with its single class in
  occupation `2k+1`, and `pathCohomology_pairedPath_odd_unique` shows every other occupation
  vanishes;
* `pathCohomology_pairedPath_even` — `e = 3k+2` gives `n = 6k+5` with its single class in
  occupation `2k+2`, with `pathCohomology_pairedPath_even_unique`;
* `pathCohomology_pairedPath_void` — `e = 3k` gives `n = 6k+1`, which carries no class in any
  occupation;
* `pathCohomology_pairedPath_covers` and `pathCohomology_pairedPath_length_unique` — every
  occupation `j ≥ 1` is realised by exactly one pairing length.

In the card's `d`-indexing (`n = 2d−1`, `d = e+1`) this is exactly `d = 3k+2 ↦ 2k+1`,
`d = 3k+3 ↦ 2k+2`, `d = 3k+1 ↦ nothing`.

### Note on the presentation

The two cohomology types are `abbrev`s rather than `def`s: as `def`s, `Submodule.mapQ_apply`
cannot be rewritten through them. The relabeling instances `instDecidableIsTailSet`,
`instDecidableIsPathFace`, `instDecidableIsTailFace` must be declared before the first `if`
guard that uses them.
