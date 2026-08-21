# The Poincaré–Hopf index theorem

- **ID:** poincare-hopf
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean target)
- **Source:** user goal, 2026-08-21
- **Statement:** For a compact smooth manifold `M` without boundary and a smooth vector field `v`
  on `M` whose zero set is finite (isolated zeros), the sum of the local indices of `v` at its
  zeros equals the Euler characteristic of `M`.

## Goal
Mathlib does **not** contain this theorem, nor any of its main prerequisites:
- no Brouwer degree (`grep -ri Brouwer Mathlib` returns only lattice-theoretic hits);
- no Sard theorem file;
- no Euler characteristic of a topological space (only `Algebra/Homology/EulerCharacteristic.lean`,
  the alternating rank sum of a homological complex);
- no hairy-ball theorem, no local index of a vector field.
So the whole tower has to be built inside the corpus.

## Architecture (bottom-up layers)

**Stage I — Brouwer degree in `ℝⁿ = (Fin n → ℝ)`, analytic construction.**
The mollified-determinant (Heinz) definition
  `D(f, Ω, y, φ) = ∫_Ω φ (f x - y) · det (Df x) dx`,
`φ` a bump with `∫ φ = 1` supported in `B_ρ(0)`, `ρ < dist (y, f '' frontier Ω)`.

- I.1 `CofactorPermutation` — permutation-sum formula for the cofactor matrix, identification with
  `Matrix.adjugate`, and the row/column contraction identities.
- I.2 `PiolaIdentity` — for `u` of class `C²`, `∑ j, ∂_j (cof (Du))_{i j} = 0`
  (rows of the cofactor matrix are divergence free).  Proof: a sign-reversing involution
  `(j, l, σ) ↦ (l, j, σ ∘ swap j l)` on the permutation index set, using symmetry of second
  derivatives.
- I.3 `CompactSupportDivergence` — `∫_{ℝⁿ} div V = 0` for `C¹` compactly supported `V`
  (mathlib's box divergence theorem with the faces pushed outside the support).
- I.4 `DivergenceForm` — `(div W)(u x) · det (Du x) = div_x (x ↦ cof(Du x)ᵀ · W (u x))`.
- I.5 `DegreeIntegral` — definition, independence of the bump `φ`, homotopy invariance.
- I.6 `RegularValueCount` — at a regular value the integral equals `∑ sign det Df`.
- I.7 `DegreeContinuous` — extension to continuous maps, excision/additivity, normalization.

**Stage II — local index of a vector field.**
- II.1 `LocalIndex` — `ind_p v = deg (v, B_ε p, 0)`, independence of `ε`.
- II.2 invariance under diffeomorphisms of the chart (so the index is chart independent).

**Stage III — manifold layer.**  Index sum for a compact manifold; independence of the field.

**Stage IV — Euler characteristic.**  Homological `χ` and the identification.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  full paper proof, dependency closed
- [ ] 2 → 3  Lean theorem, unconditional, umbrella wired
- [ ] 3 → 4  preprint

## Landed Lean modules (all unconditional, umbrella-wired)

All under `formal/GaloisForLFunctions/HTGeometry/PoincareHopf/`, namespace
`GaloisForLFunctions.HTGeometry.PoincareHopf`.

| Module | Main declarations |
|---|---|
| `CofactorPermutation` | `cofSum`, `cofSum_eq_adjugate`, `sum_cofSum_mul` |
| `PiolaIdentity` | `jac`, `hess`, `hess_symm`, `cofD`, `hasFDerivAt_cofSum`, `piola` |
| `CompactSupportDivergence` | `fieldDivergence`, `integral_fieldDivergence_eq_zero` (wraps the corpus' `HTGeometry.integral_divergence_eq_zero_of_hasCompactSupport`, all dimensions) |
| `DivergenceForm` | `piolaField`, `hasFDerivAt_piolaField`, `fieldDivergence_piolaField`, `contDiff_piolaField`, `clm_apply_eq_sum` |
| `VanishingLemma` | `integral_divergence_comp_det_eq_zero` |
| `TranslationInvariance` | `degIntegral`, `transField`, `transDeriv`, `continuous_det_jac`, `integrableOn_of_continuous`, `degIntegral_translate` |
| `MollifierIndependence` | `integrable_uncurry_of_continuous`, `degIntegral_convolution`, `degIntegral_eq_of_mass_one` |
| `Degree` | `bumpWeight`, `AdmissibleRadius`, `degree`, `exists_admissibleRadius`, `degree_eq_degIntegral` |

Key design decisions that made this work:
- ambient space `Fin n → ℝ` with the sup norm, so `volume` is the pi measure and mathlib's box
  divergence theorem applies directly;
- the **mollifier independence** proof avoids the compactly supported Poincaré lemma entirely: it
  goes through translation invariance plus Fubini on a convolution;
- **translation invariance** avoids differentiation under the integral sign: the `t`-derivative of
  `φ (w - t z)` is the divergence of the explicit field `-φ (w - t z) · z`, so the fundamental
  vanishing lemma applies slicewise and FTC + Fubini finish.

### Stage I completion (all landed)

| Module | Main declarations |
|---|---|
| `GeneralDivergenceForm` | `cofField`, `fieldDivergence_cofField`, `integral_cofSum_mul_jac_eq_zero` |
| `JacobiFormula` | `hasDerivAt_det` (Jacobi's formula) |
| `HomotopyDerivative` | `linPath`, `homField`, `homDeriv`, `sum_cofSum_mul_apply_col`, `jac_smul_field`, `hasDerivAt_homIntegrand`, `homDeriv_eq_cofPairing` |
| `HomotopyInvariance` | `continuous_matrix_det`, `continuous_cofSum`, `degIntegral_linPath_eq` |
| `DegreeProperties` | `degree_eq_of_linPath`, `degree_eq_of_subset` (excision), `degree_id` (normalization) |
| `DegreeLinear` | `AdmissibleRadius.mono`, `exists_eq_of_degree_ne_zero`, `matVec`, `degree_matVec` (degree of an invertible matrix is the sign of its determinant) |

Design note: **general homotopy invariance is reduced to the affine path**, whose Jacobian is a
*linear* matrix path, so Jacobi's formula is the plain matrix statement and no mixed `(t,x)` partial
derivatives are needed.  A general smooth homotopy will be handled by subdividing `[0,1]` and
chaining affine paths between nearby maps.

### Stage II (landed)

| Module | Main declarations |
|---|---|
| `LocalIndex` | `IsolatingRadius`, `index`, `degree_ball_eq_of_le`, `index_eq_degree`, `clm_eq_mulVec`, `fderiv_eq_matVec`, `frontier_ball_norm`, `index_eq_sign_det` |
| `DegreeAdditivity` | `exists_pos_two_lt_of_isCompact`, `degree_eq_sum_of_disjoint` |
| `DegreeIndexSum` | `exists_separating_radius`, `degree_eq_sum_index` |

`degree_eq_sum_index` is the Poincaré–Hopf statement for a flat domain: for a `C²` field on a
bounded open `Ω` whose zeros in `closure Ω` form a finite subset of `Ω`, the degree at `0` is the
sum of the local indices.  `index_eq_sign_det` computes the index at a nondegenerate zero.

Axiom audit: every declaration above depends only on `propext`, `Classical.choice`, `Quot.sound`.

### Integrality (landed)

| Module | Main declarations |
|---|---|
| `RegularValue` | `finite_zeros`, `exists_int_degree_of_nondegenerate` |
| `DegreeInteger` | `jac_sub_const`, `det_fderiv_eq_det_jac`, `admissibleRadius_sub_const`, `degree_sub_const`, `degree_eq_of_close`, `exists_regular_value_near`, `exists_int_degree` |

`exists_int_degree` : for a `C²` map on a bounded open set and a value off the image of the
boundary, `degree f Ω y` is an integer.  The chain is: local constancy in `y` (from translation
invariance) → density of regular values (mathlib's
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) → finiteness of a nondegenerate zero set →
`degree = ∑ ±1`.

Axiom audit: every capstone depends only on `propext`, `Classical.choice`, `Quot.sound`.

### Linear change of coordinates (landed)

| Module | Main declarations |
|---|---|
| `DegreeConjugation` | `matVecEquiv`, `matVec_inv_left/right`, `det_jac_conj`, `degIntegral_conj`, `degIntegral_sub_zero`, `exists_lower_bound_matVec`, `integral_comp_matVec`, `degree_conj` |

`degree_conj` : for an invertible matrix `A`, `degree (A ∘ v ∘ A⁻¹) (A '' Ω) 0 = degree v Ω 0`.
The change of variables `y = A x` contributes `|det A|`, the conjugated Jacobian has the same
determinant, so the net effect is to replace the weight `φ` by `z ↦ |det A| · φ (A z)`, still of
mass one and still supported in a small ball.

### Stage III gate: chart independence (landed)

| Module | Main declarations |
|---|---|
| `DegreeLocality` | `jac_congr`, `degIntegral_congr`, `admissibleRadius_congr`, `degree_congr` |
| `DegreeDomainChange` | `det_jac_comp`, `frontier_image_subset`, `degree_domain_change`, `degree_domain_change_neg` |
| `IndexNeighborhood` | `index_eq_degree_of_isolating` |
| `IndexPushforward` | `norm_mulVec_le`, `exists_pos_two_lt_on_compact`, `jacGap`, `norm_path_mulVec_ge`, `path_det_ne_zero`, `det_jac_pos_iff`, `mulVec_path`, **`index_pushforward`** |

`index_pushforward` : if `ψ` is injective and open near an isolated zero `p` of `v`, `det (Dψ p) ≠ 0`
and `w ∘ ψ = Dψ · v` near `p`, then `index w (ψ p) = index v p`.  Two sign changes cancel:
transporting the domain by `ψ` multiplies the degree by `sign (det Dψ)`
(`degree_domain_change`/`degree_domain_change_neg`), and replacing the varying matrix `Dψ x` by the
constant `Dψ p` — legitimate because the affine matrix path stays bounded below near `p`, by
`norm_path_mulVec_ge` — and pulling it out multiplies by the same sign again
(`degree_leftComp_matVec`).  The same-sign statement `det_jac_pos_iff` comes from the intermediate
value theorem applied to the determinant along that path.

This is exactly the transformation law a vector field obeys under a change of chart, so the index of
a zero of a vector field on a manifold is well defined.

### Germ-level index (landed)

| Module | Main declarations |
|---|---|
| `SmoothExtension` | `exists_contDiff_extension`, `index_congr`, `HasIndex`, `HasIndex.unique`, `localIndex`, `localIndex_eq`, `hasIndex_of_contDiffOn`, `localIndex_eq_index`, `localIndex_pushforward` |

Degree theory is stated for globally `C²` maps, but a chart supplies a field only on an open set.
`exists_contDiff_extension` multiplies by a `ContDiffBump` equal to one on a closed ball and
supported in the open set, and extends by zero, which is globally `C²` by the same three-open-set
gluing used in the vanishing lemma.  `localIndex v p` is then the index of any such representative;
`HasIndex.unique` (via `index_congr`) makes it independent of the choice, and
`localIndex_pushforward` transports it along a chart change.

### III.1 the manifold index (landed)

| Module | Main declarations |
|---|---|
| `ManifoldIndex` | `chartRep`, **`mindex`**, `contDiffWithinAt_chartRep`, `exists_contDiffOn_chartRep`, `chartRep_eq_zero_iff`, `IsIsolatedZero`, `exists_hasIndex_chartRep`, `isClosed_zeroSet`, **`finite_zeroSet`** |

For `M` modelled on `Fin d → ℝ`, `chartRep V p` is mathlib's
`VectorField.mpullbackWithin 𝓘(ℝ,E) I (extChartAt I p).symm V (range I)`, and
`mindex V p := localIndex (chartRep V p) (extChartAt I p p)`.  Two mathlib lemmas do the work:
`contMDiffWithinAt_mpullbackWithin_extChartAt_symm` (the chart representative of a `C²` field is
`C²`) and `contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt` (manifold smoothness of a field on a
vector space is ordinary smoothness).  `chartRep_eq_zero_iff` transfers isolation of the zero
through the invertible chart derivative, so `exists_hasIndex_chartRep` shows `mindex` really is the
index of a `C²` germ with an isolated zero.

Since `mindex` is defined through the distinguished chart at `p`, it needs no choices; computing it
in another chart is `localIndex_pushforward`, because two chart representatives are related by the
pushforward law along the transition map.

## Next layers
- III.2 independence of the index sum from the field.  `finite_zeroSet` already makes the sum
  `∑ p ∈ (finite_zeroSet …).toFinset, mindex V p` well posed on a compact manifold; what is missing
  is that it does not depend on `V`.  Mathlib supplies the Whitney embedding for compact manifolds;
  the missing analytic input for Milnor's route is the tubular neighbourhood theorem.  The
  alternative is transversality/intersection theory for sections of the tangent bundle.
### Stage IV inventory and plan

The corpus already owns more of this than expected.  Existing assets:

| Module | What it gives |
|---|---|
| `CoproductMayerVietoris`, `CoproductMayerVietorisSup` | `subCoproduct`, `inclFull`, `restrFull`, `inclCop`, `restr`, and the split short complex of a coproduct over two subsets |
| `SimplicialMayerVietoris`, `…Sup`, `…Family`, `…Mono` | `mvChainShortExact`: two subcomplexes covering a simplicial set give a degreewise split short exact sequence of chain complexes, plus Mayer–Vietoris vanishing corollaries |
| `SingularHomologyContractible` | higher singular homology of a contractible space vanishes; `H₀` is the coefficient object |
| `RelativeSimplicialHomology` (**new**) | `relChainComplex`, `relChainShortExact`, `relConnecting`, `rel_homology_exact₁/₂/₃`: the long exact sequence of a pair |

`SimplicialMayerVietoris` is Mayer–Vietoris for *subcomplexes of a simplicial set*.  Applied to
`A = Sing A`, `B = Sing B` inside `Sing X`, the union subcomplex is exactly the subcomplex of
simplices small with respect to `{A, B}`, so that theorem already delivers

  `… → Hₙ(A ∩ B) → Hₙ(A) ⊕ Hₙ(B) → Hₙ(Sing^{A,B} X) → …`

and the **only** missing input for topological Mayer–Vietoris is

  **(IV.★) the small simplices theorem**: the inclusion `C^𝒰(X) → C(X)` is a homology isomorphism
  when the interiors of `𝒰` cover `X`.

That is the gate for the whole of Stage IV.  Its proof needs, in order:

- IV.1 **(landed)** `AffineChainComplex`: `affSimplicial` (the free `R`-module simplicial object on
  the codiscrete simplicial set of a type), `affChainComplex` (its alternating face map complex, so
  `∂² = 0` is free), `affSimplicial_δ` and `d_single` (the boundary is the alternating sum of the
  vertex-omitting faces), `coneMap` (prepend a fixed point), `cons_comp_succAbove_zero` and
  `cons_comp_succAbove_succ` (the zeroth face of a cone is the simplex, the higher faces are the
  cones of the faces), and **`d_coneMap_single`**: `∂ (b ∗ v) + b ∗ (∂ v) = v`.
  Note mathlib's topological simplex is `stdSimplex ℝ (Fin (n+1))`, a convex subset of a real
  vector space, so affine simplices in it are exactly tuples of points and the cone is prepending a
  vertex — no continuity argument at the apex is needed;
- IV.2 **(started)** `BarycentricSubdivision`: `bary` (barycenter of a tuple), `d_coneMap_single_zero`
  (`∂ (b ∗ v) = v − [b]` in the lowest degree), **`sd`** (the subdivision operator, defined by the
  recursion `Sd v = b(v) ∗ Sd (∂ v)` with `Sd = id` in degree zero), `sd_single` (its recursion
  equation), and **`d_coneMap_add`** (the cone identity for arbitrary chains, obtained from the
  basis case by `Finsupp.lhom_ext'`).
  Also landed: `sd_zero_apply`, `aug` (the augmentation of a `0`-chain), `aug_single`,
  **`aug_d`** (the augmentation of a boundary vanishes), `d_coneMap_zero`
  (`∂ (b ∗ c) = c − ε(c)·[b]` in degree zero), and **`d_sd`: `∂ ∘ Sd = Sd ∘ ∂`** — the subdivision
  operator is a chain map, by induction on the degree: in degree zero the cone identity contributes
  the augmentation term, which vanishes on a boundary; in higher degree `∂ Sd v = ∂ (b ∗ X)
  = X − b ∗ (∂ X)` with `X = Sd (∂ v)`, and `∂ X = Sd (∂∂ v) = 0` by the inductive hypothesis.
  **IV.2 is complete.**  `affBd`, `affCone`, `affSd`, `affT` name the boundary, cone, subdivision
  and homotopy as honest linear maps between the `Finsupp` modules (all definitional), which removes
  the `ModuleCat` carrier coercion that otherwise blocks elaborating differences of chains.  On top
  of them: `affBd_affCone` (cone identity), `affBd_affSd` (`Sd` is a chain map), `affBd_affBd`
  (`∂∂ = 0`), `affT` (the homotopy `T v = b(v) ∗ (Sd v − v − T (∂ v))`, zero in degree zero),
  `affT_single`, and **`affBd_affT`: `∂T + T∂ = Sd − 1`** — the subdivision is chain homotopic to
  the identity.
- IV.3 iterated subdivision plus the Lebesgue number lemma, giving IV.★.
  **Started**: `SubdivisionDiameter` proves the shrinking estimate — `norm_bary_sub_vertex_le`
  (`‖b(v) − vᵢ‖ ≤ n/(n+1) · D` when all vertex distances are at most `D`, since `b(v) − vᵢ` is the
  average of the `n` nonzero differences `vⱼ − vᵢ`) and `norm_bary_sub_combination_le` (the same
  bound against every convex combination of the vertices, hence against every point of the
  simplex).  Mathlib supplies the Lebesgue number lemma (`lebesgue_number_lemma_of_emetric`).
  `SubdivisionSupport` adds the support bookkeeping: the predicates `VerticesIn` (all vertices of
  every simplex occurring in a chain lie in a set) and `DiamLe` (all those simplices have diameter
  at most `D`), with `VerticesIn.mono`, `DiamLe.mono`, `support_affCone_subset` (the simplices of a
  cone are cones of the original simplices), `VerticesIn.affCone`, `affBd_single`, and
  `support_affBd_single_subset` (the simplices of a boundary are the faces).
  It also proves `support_linear_apply_subset` (the simplices of a linear image of a chain come
  from the simplices of the chain), `norm_bary_sub_mem_hull_le` (the barycenter is within
  `n/(n+1)·D` of the whole convex hull, since a closed ball is convex and contains the vertices),
  `bary_mem_hull`, and the mesh estimate itself:

  **`sd_mesh`** : every simplex occurring in `Sd v` has its vertices in `convexHull ℝ (range v)`
  and diameter at most `n/(n+1)` times the diameter of `v`.  The induction is exactly the classical
  one: the simplices of `Sd v = b(v) ∗ Sd (∂ v)` are cones on simplices of the subdivisions of the
  faces, whose vertices stay in the hull, and the new vertex `b(v)` is within `(n+1)/(n+2)·D` of
  that hull.

  Iteration is also done: `sd_mesh_chain` (the mesh estimate for an arbitrary chain contained in a
  convex set), `sdIter` (iterated subdivision), and **`sdIter_mesh`**: inside a convex set, the
  simplices of `Sd^k c` still lie in it and have diameter at most `(n/(n+1))^k · D`.
  **IV.3 is complete.**  Five further modules carry the subdivision to singular chains.

  `TopologicalSingularChains` builds the concrete singular chain complex: the singular `n`-simplices
  are `C(topSimplex n, X)` with `topSimplex n = stdSimplex ℝ (Fin (n+1))`, the free `R`-module
  simplicial object on them has the alternating face map complex as its chain complex, and
  `sing_d_single` / `singBd` name the boundary concretely.  `∂∘∂ = 0` is inherited.

  `AffineToSingular` builds the bridge.  Its device is a **continuous retraction of the ambient
  space onto the standard simplex**: take positive parts, add a defect term `max 0 (1 − M)/(n+1)`
  spread over the coordinates and divide by `M + max 0 (1 − M) ≥ 1`.  It is the identity on the
  simplex, so the pushforward `affSing σ v = σ ∘ retr ∘ affComb v` of an affine simplex is total —
  defined for every tuple of ambient points, not only for tuples inside the simplex — and
  `singBd_comp_affToSing` is a chain map identity with no side conditions.

  `AffineNaturality` proves that a linear map of the ambient space commutes with everything:
  `affPush_affBd`, `affPush_affCone` (via `bary_map`), and by induction on the degree
  **`affPush_affSd`** and **`affPush_affT`**.  It also proves that all these operators keep the
  vertices of a chain inside a fixed convex set (`verticesIn_affSd`, `verticesIn_affT`).

  `SingularSubdivision` defines `singSd` and `singT` by pushing the affine subdivision of the
  standard simplex forward along each singular simplex, and proves
  **`singBd_singSd`** (subdivision is a chain map) and **`singBd_singT`**
  (`∂T + T∂ = Sd − 1`) by transporting the affine identities: the faces of the standard simplex are
  the images of the standard simplex one dimension lower under `ambMap`, so naturality converts the
  face terms exactly into the affine boundary.

  `SmallSimplices` closes IV.3.  `ambComb` is the linear extension of an affine simplex, and
  `affSing_ambComb` shows that pushing forward along an affine simplex of the standard simplex is
  the same as pushing forward along the singular simplex it determines — with no hypothesis on the
  affine simplex, because the retraction is applied on the outside in both readings.  Hence
  **`singSd_iterate`** : `Sd^N σ = σ_*(Sd^N Δ)`, and combining the geometric mesh decay with the
  Lebesgue number of the cover pulled back along `σ ∘ retr` over the compact `stdSimplex`:

  **`exists_iterate_small`** : for every open cover `𝒰` of `X` and every singular simplex `σ`
  there is an `N` such that every simplex of `Sd^N σ` has image inside a member of `𝒰`.
- IV.4 **the small-simplices quasi-isomorphism is proved.**  Six further modules.

  `SmallChains` defines `SmallSimplex`/`SmallChain` (image inside a member of a family) and proves
  that `Sd`, `T` and `∂` never enlarge the image of a simplex, hence preserve smallness; `singSdPow`
  is the iterated subdivision as a linear map, and **`exists_singSdPow_small`** says one number of
  subdivisions makes a whole chain small — the finite support means no per-simplex bookkeeping is
  ever needed.

  `SubdivisionHomotopy` builds `D_N = ∑_{i<N} T ∘ Sd^i` and proves **`singBd_singD`**:
  `∂D_N + D_N∂ = Sd^N − 1`.  Two consequences, stated for a cover `𝒰` refining a family `𝒱`:
  `exists_small_cycle_homologous` (every cycle is homologous to a small cycle) and
  `exists_small_bounding` (a small cycle that bounds, bounds a small chain).

  `SubspaceChains` identifies the chains supported in a subset with the chains of the subspace
  (`range_subChainIncl`), and records `subChains_inter` and `smallChain_pair_iff` — the two
  decompositions Mayer–Vietoris needs.

  `ChainSubcomplex` turns a boundary-stable degreewise submodule into a `ChainComplex (ModuleCat R)`
  with its inclusion; `RelativeSingularHomology` builds the quotient complex, the short exact
  sequence `0 → P → C(X) → C(X)/P → 0` (**`ChainSubmodule.shortExact`**) and its homology long exact
  sequence.

  `SmallQuasiIso` closes IV.4's core: the quotient of the singular chains by the small chains is
  acyclic — degree `0` because every `0`-simplex is small, higher degrees because
  `c = Sd^N c − ∂D_N c − D_N ∂c` with the two outer terms small whenever `∂c` already is — whence

  **`isIso_homologyMap_smallIncl`** : for an open cover, the inclusion of the small chains induces
  an isomorphism on homology in every degree.

- IV.4 remaining: excision (second isomorphism theorem for the pair `C(X∖Z)/C(A∖Z) ≅ C^𝒰/C(A)`
  plus the five lemma) and topological Mayer–Vietoris (the submodule sequence
  `0 → C(A∩B) → C(A) ⊕ C(B) → C(A)+C(B) → 0`);
- IV.5 `H_*(Sⁿ)` and `H_*(Dⁿ, Sⁿ⁻¹)`;
- IV.6 Morse theory: sublevel sets, handle attachment, gradient flow retractions, and
  `χ(M) = ∑ (−1)^λ`.
- III manifolds: charts, vector fields, index sum, independence of the field.  Mathlib supplies
  `IsManifold`, the tangent bundle, `ContMDiffSection`, partitions of unity and the **Whitney
  embedding theorem for compact manifolds** (`Geometry/Manifold/WhitneyEmbedding.lean`), so
  Milnor's route (embed, tubular neighbourhood, Gauss map) has its first step available.
- IV Euler characteristic.  Mathlib has singular homology but no excision, no Mayer–Vietoris and no
  long exact sequence of a pair, so `χ` of a space has to be built from scratch; that is the largest
  remaining block.

## Log
- 2026-08-21 — created; mathlib audit done (no Poincaré–Hopf, no degree, no Sard, no χ of a space);
  corpus audit done (`BrouwerFixedPoint`, `SmoothNoRetraction`, `DeterminantPolynomialIntegral`
  exist; no degree theory).  Architecture frozen as above.
- 2026-08-21 — Stage I core complete through the definition of the Brouwer degree and the theorem
  that it equals the integral against every admissible weight.
- 2026-08-21 — Stage I finished (homotopy invariance, excision, normalization, degree of an
  invertible affine map), Stage II finished (local index, index at a nondegenerate zero, additivity,
  `degree = ∑ index`), and integrality of the degree proved.  19 modules, all umbrella-wired, all
  building warning-free, all axiom-clean.
