# Borsuk–Ulam theorem (unconditional Lean proof, all dimensions)

- **ID:** borsuk-ulam
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** goal directive 2026-08-21 (user)
- **Statement:** For every `n` and every map `f : ℝ^{n+1} → ℝ^n` continuous on the unit sphere
  there is a point `x` of the sphere with `f x = f (-x)`.

## Goal
Give the corpus an unconditional Lean 4 proof of Borsuk–Ulam in **every** dimension.  Mathlib has
no Borsuk–Ulam, no Tucker/Sperner lemma, no antipodal degree theory and no simplicial subdivision
(verified 2026-08-21: the only `Borsuk` hit in mathlib is a bibliography reference to the
Borsuk–Mazurkiewicz counterexample in `Topology/Homotopy/LocallyContractible.lean`).  The corpus
owned Brouwer's fixed point theorem (`HTGeometry/BrouwerFixedPoint.lean`, via the C¹ volume
argument of `SmoothNoRetraction.lean`) but nothing antipodal: Brouwer is strictly weaker and gives
no route to Borsuk–Ulam.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete proof, no open dependency
- [x] 2 → 3  formalized: `borsuk_ulam`, `lake build` green,
      `#print axioms` = `[propext, Classical.choice, Quot.sound]` only, `formal lint passed`
- [ ] 3 → 4  publication-ready

## Capstone
`GaloisForLFunctions.BorsukUlam.borsuk_ulam`
(`formal/GaloisForLFunctions/HTGeometry/BorsukUlam/Theorem.lean`)

```lean
theorem borsuk_ulam {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f (Metric.sphere 0 1)) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x)
```

Companions: `borsuk_ulam_sphere` (the sphere as a subtype, with mathlib's antipodal `Neg`
instance), `no_odd_map_to_smaller_sphere`, `no_odd_nonvanishing`, and the combinatorial capstone
`FlagComplex.tucker`.

## Lean modules
| Module | Content |
|---|---|
| `HTGeometry/BorsukUlam/Parity.lean` | `freeInvolution_sum_odd_parity` (orbit pairing of a degree function under a free involution) and `card_four_dvd_of_klein` (a free Klein-four action forces `4 ∣ card`), both with hypotheses localised to the finset |
| `HTGeometry/BorsukUlam/Alternating.lean` | the label combinatorics: rank `rk`, successor relation `Consec`, `alt`/`AltSet`/`almostAlt`, the defect characterisation `altSet_erase_iff`, and the two facet-count theorems `exists_unique_alt_erase_of_alt` and `exists_pair_alt_erase_of_almostAlt` |
| `HTGeometry/BorsukUlam/FlagComplex.lean` | the structure `FlagComplex n`: an antipodally symmetric complex aligned with a flag of hemispheres, with carrier dimension `cdim`, carrier sign `csgn` and the two facet-counting axioms |
| `HTGeometry/BorsukUlam/Tucker.lean` | the Fan graph (`IsNode`, `Cov`, `Adj`), the degree computations `deg_T1`, `deg_T2`, `deg_T3_bottom/mid/top`, the antipodal automorphism, and **`FlagComplex.tucker`** |
| `HTGeometry/BorsukUlam/Subdivision.lean` | barycentric subdivision `sd : FlagComplex n → FlagComplex n` (vertices = faces, faces = chains) with every axiom inherited, notably `sd_facets_two` (top / middle extension) and `sd_facets_one` |
| `HTGeometry/BorsukUlam/CrossPolytope.lean` | the octahedral complex `cross n` (faces = sign vectors) as a `FlagComplex n` |
| `HTGeometry/BorsukUlam/Realization.lean` | `GeoFlag n` (a flag complex realized on the ℓ¹-sphere), the barycentre estimates, `sdGeo` (mesh `↦ n/(n+1) · mesh`), the `tower`, and `crossGeo` |
| `HTGeometry/BorsukUlam/Theorem.lean` | ℓ¹-sphere geometry, the coordinate bounds, `no_odd_nonvanishing`, `borsuk_ulam` and companions |

## Proof architecture

**1. Combinatorial core — Fan's path argument (Prescott–Su form), Lean-ified.**
A `FlagComplex n` abstracts an antipodally symmetric triangulation of `Sⁿ` aligned with a flag of
hemispheres `H₀ ⊂ ⋯ ⊂ H_n`: each vertex has a level `lev v ≤ n` and a sign `sgn v`, `neg`
preserves the level and flips the sign, the carrier of a face `σ` is `± H_{cdim σ}` with
`cdim σ = σ.sup lev`, and

* `card_le`: `|σ| ≤ cdim σ + 1`;
* `facets_two`: a face with `|σ| = cdim σ` lies in exactly two faces of the same carrier
  dimension with one more vertex;
* `facets_one`: a face with `|σ| = cdim σ + 1` lies in exactly one face of carrier dimension
  `cdim σ + 1` of each sign;
* `lev_zero`: the only level-`0` vertices are `base` and `neg base`.

Given an antisymmetric labelling by nonzero integers of absolute value `≤ n` and **assuming no
complementary edge**, the nodes of the Fan graph are the agreeable alternating faces with
`card = cdim` (T1), the agreeable almost-alternating faces with `card = cdim + 1` (T2) and the
alternating faces with `card = cdim + 1` (T3); `σ` and `τ` are adjacent when one is a facet of the
other, the smaller is alternating, **the larger satisfies `card = cdim + 1`**, and the sign of the
smaller equals the carrier sign of the larger.

> The last clause is an addition to the published adjacency definition, which as literally stated
> also makes a `T1` node adjacent to a facet of it lying one hemisphere down, breaking the degree
> count.  Requiring the larger simplex to be a *top* face of its own carrier removes exactly those
> spurious edges and leaves every degree computation of the paper intact.

Degrees: T1 = 2 (`facets_two`), T2 = 2 (its two alternating facets — the label lemma
`exists_pair_alt_erase_of_almostAlt`), T3 = 1 below + 1 above, so `2` except at `cdim = 0`
(the two vertices of `H₀`) and at `cdim = n`.  With labels in `{±1, …, ±n}` an alternating
`n`-face would need `n+1` distinct magnitudes in `{1, …, n}`, so the odd-degree nodes are exactly
`{base}` and `{neg base}` — **two** of them.  The antipodal map is a graph automorphism, free on
nodes and moving every edge, so `Prod.swap` and `negF × negF` generate a free Klein-four action on
the set of ordered adjacent pairs; hence `4 ∣ Σ deg`, and the orbit pairing gives
`4 ∣ #{odd-degree nodes} = 2`.  Contradiction.

**2. Label combinatorics.**  A set of labels is *alternating* when the absolute values are
pairwise distinct and, sorted by absolute value, the signs alternate.  Working with the rank
`rk σ v = #{w ∈ σ : |lab w| < |lab v|}` and the successor relation, alternation is exactly the
absence of a *defect* (two consecutive labels of equal sign).  This gives uniform proofs of both
facet counts: an alternating face has exactly two alternating facets (delete the smallest or the
largest, of opposite signs), and an almost-alternating face without a complementary pair has
exactly one defect, hence exactly two alternating facets, both of the same sign — either because
its unique repeated label can be dropped in two ways, or by deleting either end of the defect.

**3. Geometry.**  The octahedral complex `cross n` (a face = a set of signed coordinate indices
with distinct indices) satisfies the axioms with `lev (i, ε) = i`, `sgn (i, ε) = ε`.  Barycentric
subdivision has the faces as vertices and the chains as faces; all axioms are inherited, the two
facet counts becoming (i) "extend a chain of maximal length above its top face" (reduces to
`facets_two` for the top face) and (ii) "insert the one missing cardinality into the chain"
(exactly two intermediate sets between `A ⊆ B` with `|B| = |A| + 2`).  Realizing a vertex by the
barycentre of its face keeps every vertex on the ℓ¹-sphere (a face lies in one closed orthant,
where `‖·‖₁` is linear) and multiplies the mesh by at most `n/(n+1)`, since for `τ ⊆ σ`,
`‖b(τ) − b(σ)‖ ≤ (1 − 1/|σ|)·mesh`.

**4. Limit.**  If `f x ≠ f (-x)` everywhere, `g = f(·) − f(−·)` is odd, continuous and
nonvanishing on the sphere; `G = g ∘ (radial projection)` is odd, continuous and nonvanishing on
the compact ℓ¹-sphere, so `‖G‖ ≥ ε > 0` there and `G` is uniformly continuous.  Label a vertex `v`
by `±(i+1)`, where `i` is the (canonically chosen) index of a largest coordinate of `G (φ v)` and
the sign is that coordinate's sign; the labelling is antisymmetric because the choice depends only
on `j ↦ |G (φ v) j|`.  Take a subdivision of mesh `< δ`.  Tucker's lemma gives an edge `{u, v}`
with opposite labels, so at one common index `i` the coordinates of `G (φ u)` and `G (φ v)` have
opposite signs and each has absolute value `≥ ε/n` (from `‖z‖ ≤ n·max_j |z j|`), whence
`|G(φu)_i − G(φv)_i| ≥ 2ε/n`, contradicting `‖G(φu) − G(φv)‖ < 2ε/n`.

## Novelty audit
Mathlib: nothing.  Corpus (searched `Borsuk`, `Tucker`, `Sperner`, `antipodal`, `Ham sandwich`,
`Lusternik`): nothing antipodal; `BrouwerFixedPoint`/`SmoothNoRetraction` are the only fixed-point
assets and are strictly weaker.  The Lean development is new, and the fix to the adjacency
definition (requiring the larger simplex to be a top face of its carrier) is an independent
mathematical correction of the Prescott–Su presentation.

## Log
- 2026-08-21 — created directly at 3-formalized: paper proof and Lean formalization completed in
  one pass; `lake build` green, axioms clean, `formal lint passed`.
