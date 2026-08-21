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

- IV.1 affine singular simplices in a convex subset of a real vector space, and the cone operator,
  with `∂(b ∗ c) + b ∗ (∂ c) = c − ε(c)·b`;
- IV.2 the barycentric subdivision operator `S` on singular chains and a chain homotopy `T` with
  `∂T + T∂ = 1 − S`;
- IV.3 iterated subdivision plus the Lebesgue number lemma, giving IV.★;
- IV.4 topological Mayer–Vietoris and excision from IV.★ plus `mvChainShortExact`;
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
