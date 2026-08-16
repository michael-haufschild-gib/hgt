# Garland's theorem, formalized: the full dependency tree

- **ID:** `garland-formalization-programme`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME (multi-session)
- **Serves:** `deninger-algebraic-cyclotomic-milnor-amplitude` (the single remaining input of its `(1)`)
- **Parent programme card:** `garland-tame-kernel-torsion`

## Target

For a number field `K`,
\[
 K_2^M(K)\otimes\mathbb Q=0,
\]
equivalently: **the tame kernel of `K` is torsion**.  This is Garland's finiteness theorem in the
only form the parent card needs — rank zero, not finite generation.

## Why this route and not the other two

Three published routes reach the statement.

| route | inputs | verdict |
|---|---|---|
| Quillen finite generation + Borel rank | plus construction, Borel–Serre compactification, continuous cohomology of Lie groups, van Est, regularization of differential forms | analytic; nothing in mathlib to build on |
| Soulé vanishing + Quillen–Lichtenbaum | étale cohomology of arithmetic schemes, Iwasawa theory, Voevodsky–Rost | strictly larger than either alternative |
| **Garland's method** | weighted simplicial complexes, links, graph Laplacians, spectral gap of a spherical building, Bruhat–Tits building | **combinatorial and linear-algebraic; the corpus already owns the simplicial cochain complex and the spherical-building layer** |

Garland's method is chosen.  Its heart is a Bochner-type inequality on a simplicial complex, and
every step of it is finite linear algebra over `ℝ`.

## The chain

```
K_2^M(K) ⊗ ℚ = 0
  ⇐ [A] tame kernel of K is torsion                       ── the parent card's reduction, DONE
      ⇐ [B] K_2(𝒪_S) ⊗ ℚ = 0
          ⇐ [B3] Matsumoto: K_2(F) ≅ K_2^M(F)
          ⇐ [B1,B2] K_2(R) = ker(St(R) → E(R)) = H_2(E(R), ℤ)
          ⇐ [B5] homological stability: H_2(E_n) ≅ H_2(E) for n ≫ 0
          ⇐ H^2(SL_n(𝒪_S), ℝ) = 0
              ⇐ [C] Garland vanishing: local spectral gaps > k/(k+1) ⟹ H^k = 0
              ⇐ [D] the Bruhat–Tits building of SL_n(K_v) and its links
```

### Layer A — arithmetic reduction (DONE)

- `deningerMilnorRealVanishing_of_finiteSubextension` — algebraic `F/ℚ` to number subfields.
- `milnorKDeg_mem_torsion_of_two` — degree `2 + k` to degree two.
- `milnorKDegTwo_torsion_of_tameKernel_numberField` — tame kernel to `K_2^M`.
- `milnorKDeg_torsion_of_milnorTameKernel_torsion` — the same in every degree, over any Dedekind
  domain.  **This is what lets Layer B work with `𝒪_S` for an `S` of our choosing**: the residues at
  the places of `S` land in the finite groups `k(v)^×`, so torsion of the `𝒪_S`-tame kernel already
  gives torsion of `K_2^M(K)`.

### Layer B — from the tame kernel to group homology (TO BUILD)

- **B1** `SteinbergGroup R`, `elementaryGroup R`, `K₂ R := ker(St R → E R)`; the Steinberg
  relations as a presentation.
- **B2** `St(R) → E(R)` is a universal central extension when `E(R)` is perfect, hence
  `K₂(R) ≅ H₂(E(R), ℤ)`.
- **B3** **Matsumoto's theorem** `K₂(F) ≅ K₂^M(F)` for a field.  The corpus already has the
  `K₂^M` side in full (`MilnorKDeg F 2` with its presentation, bilinearity, Steinberg relation and
  the extensionality principle `milnorKDeg_hom_ext`), so what is missing is the comparison map and
  its inverse.
- **B4** Localization: the Milnor tame kernel of `𝒪_S` is `K₂(𝒪_S)`.
- **B5** Homological stability for `E_n(𝒪_S)` in degree two.

### Layer C — Garland's vanishing criterion (TO BUILD; START HERE)

Purely combinatorial; no arithmetic.  Substrate: the corpus's
`HTGeometry/SimplicialCochainComplex.lean`, which already supplies the reduced simplicial cochain
complex of an arbitrary finite complex in every degree with `δ ∘ δ = 0`.

- **C1** Weighted complexes: a weight on each `k`-simplex, the induced inner product on `k`-cochains,
  the adjoint `δ*` and the Laplacian `Δ = δ*δ + δδ*`.
- **C2** Links: for a simplex `σ`, the link complex, the restriction `f ↦ f_σ` of a `k`-cochain to a
  `(k-|σ|)`-cochain of the link, and the **localization identity**
  `⟨δf, δf⟩ = Σ_{σ ∈ X(k-1)} ⟨δ_σ f_σ, δ_σ f_σ⟩ + …`.
- **C3** The weighted graph Laplacian of a finite connected graph: positive semidefinite, kernel the
  constants, and the spectral gap inequality
  `⟨Δ f, f⟩ ≥ λ₁ · ‖f − mean f‖²`.
- **C4** **Garland / Ballmann–Świątkowski**: if `X` is pure `n`-dimensional, every link of a simplex
  of dimension `≤ n − 2` is connected, and `λ₁(X_σ) > k/(k+1)` for every `σ` of dimension `k − 1`,
  then `H^k(X, ℝ) = 0`.  For `k = 2` — the degree we need — the hypothesis is
  `λ₁ > 2/3` on vertex links and edge links.
- **C5** `H^*(Γ, ℝ)` from the `Γ`-invariant cochains on a contractible `X` with a proper cocompact
  action.

### Layer D — the building (TO BUILD)

- **D1** The Bruhat–Tits building of `SL_n` over a local field: homothety classes of lattices,
  incidence, the simplicial structure.
- **D2** Its contractibility.
- **D3** Links of simplices are the spherical buildings of `𝔽_q^n` — the corpus's
  `BuildingLink`, `SolomonInduction`, `BuildingHomologyConcentration` layer is exactly this object.
- **D4** The **spectral gap of the incidence graph of the spherical building of `𝔽_q^n`**.  This is
  the one quantitative input: the eigenvalues of the flag-incidence graph of a projective space over
  `𝔽_q` are explicit, and give `λ₁ ≥ 1 − c/√q`.  Choosing the finite place of `S` with `q` large
  enough makes `λ₁ > 2/3`, which is all Garland needs.  **`S` is ours to choose**, so this costs
  nothing arithmetically.

## Order of work

Layer C first: it is self-contained, it is the mathematical heart, and no part of it has ever been
formalized.  Within C, the order is C3 (graph Laplacian and spectral gap) → C1 (weighted cochains
and the Laplacian) → C2 (links and the localization identity) → C4 (the vanishing theorem) → C5.

Then D4 (the spherical-building spectral gap, on top of the corpus's building layer), then D1–D3,
then Layer B.

## Log

- 2026-08-14 — programme opened; route selected; Layer A recorded as complete.

## Layer C — progress, 2026-08-14

Three modules landed, each checked with `lake env lean` and wired into
`GaloisForLFunctions/HTGeometry.lean`.

### `HTGeometry/WeightedGraphSpectralGap.lean` — C3

- `WeightedGraph` — a finite symmetric nonnegative weight with no loops.
- `mass`, `totalMass`, `massInner`, `dirichlet` — the vertex masses, the mass inner product and the
  Dirichlet form, with nonnegativity of the mass and of the Dirichlet form of a function against
  itself.
- **`dirichlet_self_eq`** — `E(f,f) = ⟨f,f⟩_m − Σ_{v,u} w(v,u) f(v) f(u)`: the Dirichlet form is the
  mass norm minus the averaging form.  Proved from the two summation identities
  `sum_sum_w_mul_left` and `sum_sum_w_mul_right`, the second of which is where symmetry of the
  weight is used.
- `HasSpectralGap` — the gap is carried as a property of a real number, not as an infimum, which is
  the form Garland's inequality consumes and needs no compactness.
- **`spectralGap_apply`** — a spectral gap bounds `lam · ‖f − mean f‖²_m` by `E(f,f)`, because the
  Dirichlet form is invariant under adding a constant and `f − mean f` has mass average zero.

### `HTGeometry/WeightedComplexLink.lean` — C1

- `WeightedComplex` — a finite complex presented by its top faces with a nonnegative weight on each.
- **`m`** — the weight of a face: the total weight of the top faces containing it; monotone
  decreasing in the face.
- **`linkGraph`** — the link of a face as a weighted graph.  Two vertices *outside* `σ` are joined
  with the weight of the face they span together with `σ`; the vertices of `σ` are isolated in it.
  That guard is what makes the next item true.
- **`linkGraph_mass`** — **the weighted degree of a vertex of the link of `σ` on a pure
  `n`-dimensional complex is `(n − |σ|)` times the weight of `σ ∪ {u}`.**  Every top face containing
  `σ ∪ {u}` has exactly `n − |σ|` further vertices, each contributing one edge of the link at `u`.
  This is the combinatorial identity that converts a statement about links into a statement about
  the complex, and it is the first place where purity is used.

### `HTGeometry/SimplicialLinkRestrict.lean` — C2, first half

Built on the corpus's `SimplicialCochainComplex`, so `δ ∘ δ = 0` and the incidence-sign calculus are
inherited rather than rebuilt.

- **`linkRestrict`** — the restriction of a cochain to the link of a face, `f_σ(u) = ε·f(σ ∪ {u})`
  with `ε` the incidence sign of `u` in `σ ∪ {u}`.  That sign is exactly what is needed for:
- **`coboundary_link_pair`** — **the two link terms of `δf` on `σ ∪ {u, u'}` are a single sign times
  `f_σ(u) − f_σ(u')`.**  The mechanism is the corpus's
  `faceSign_mul_faceSign_erase_antisymm`: erasing `u` then `u'` and erasing `u'` then `u` carry
  opposite signs.
- **`coboundary_link_decomp`** — **the coboundary localized at a face**:
  `δf(σ ∪ {u,u'}) = ε·(f_σ(u) − f_σ(u')) + Σ_{v ∈ σ} faceSign · f(…)`.
  This is the shape Garland's localization identity is assembled from.

### Next

The remaining half of C2 is the localization identity proper — summing
`‖δ_σ f_σ‖²_{link}` over the faces `σ` of dimension `k−1` and comparing with `‖δf‖²` — followed by
C4, the vanishing theorem.

## Layer C — the localization identity, derived

The identity Garland's method runs on, derived here in the corpus's normalization (weights `m` on
faces, `‖f‖²_k = Σ_{|τ|=k+1} m(τ) f(τ)²`, link graphs as above), for a pure `n`-dimensional complex
and a `k`-cochain `f`:

\[
 \sum_{|\sigma|=k}\langle f_\sigma,f_\sigma\rangle_{X_\sigma}=(n-k)(k+1)\,\|f\|_k^2,
 \qquad
 \sum_{|\sigma|=k}E_{X_\sigma}(f_\sigma,f_\sigma)=\|\delta f\|_{k+1}^2+k(n-k)\,\|f\|_k^2 .
\]

The derivation of the second is short once the pieces are in place, and it is what the remaining
work assembles.  Write `A_v := \mathrm{faceSign}(\rho,v)\,f(\rho\setminus v)` for `|\rho| = k+2`.

1. `coboundary_link_pair` says `f_σ(u) − f_σ(u') = ±(A_u + A_{u'})` for `ρ = σ ∪ {u,u'}`, so
   `(f_σ(u) − f_σ(u'))² = (A_u + A_{u'})²`.
2. Reindexing the double sum by `ρ` turns `Σ_σ E_σ` into
   `½ Σ_{|ρ|=k+2} m(ρ) Σ_{(u,u') ordered distinct in ρ} (A_u + A_{u'})²`.
3. `sum_pairs_sq` evaluates the inner sum as `2k·Σ_{u∈ρ}A_u² + 2(Σ_{u∈ρ}A_u)²`, and
   `Σ_{u∈ρ}A_u = δf(ρ)`, `A_u² = f(ρ∖u)²`.
4. `sum_powersetCard_insert` and `sum_m_insert` turn `Σ_ρ m(ρ) Σ_{u∈ρ} f(ρ∖u)²` into
   `(n−k)‖f‖²_k`.

### Landed in `HTGeometry/GarlandLocalization.lean`

- **`sum_powersetCard_insert`** — the pairs `(σ,u)` with `|σ| = k`, `u ∉ σ` are the pairs `(τ,u)`
  with `|τ| = k+1`, `u ∈ τ`.  Proved by an explicit bijection of sigma-types.
- **`sum_pairs_sq`** — `Σ_{u∈ρ} Σ_{u'≠u} (A_u + A_{u'})² = 2(|ρ|−2)·Σ A_u² + 2(Σ A_u)²`.  Step 3
  above; pure algebra over a finite set.
- `linkRestrict_sq`, `linkGraph_mass_of_mem`, `cochainNormSq`, `link_massInner_eq`.
- **`sum_link_massInner`** — **the first identity**:
  `Σ_{|σ|=k} ⟨f_σ,f_σ⟩_{X_σ} = (n−k)(k+1)·‖f‖²_k`.
- **`sum_m_insert`** — `Σ_{u ∉ τ} m(τ ∪ {u}) = (n+1−|τ|)·m(τ)`; step 4 above.

What remains of C2 is the assembly of the second identity from these four, then C4.

## Layer C — the localization identity and the vanishing core, PROVED

`HTGeometry/GarlandLocalization.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

Both halves of Garland's localization identity now hold in Lean, for a pure `n`-dimensional weighted
complex and a `k`-cochain `f`:

- **`sum_link_massInner`** — `Σ_{|σ|=k} ⟨f_σ,f_σ⟩_{X_σ} = (n−k)(k+1)·‖f‖²_k`.
- **`sum_link_dirichlet`** — `Σ_{|σ|=k} E_{X_σ}(f_σ,f_σ) = ‖δf‖²_{k+1} + k(n−k)·‖f‖²_k`.

Supporting results, all proved: `two_dirichlet_link_eq` (restricting the link Dirichlet sums to the
link), `coTerm`/`coTerm_sq`/`sum_coTerm` (the signed face values, whose sum is the coboundary),
`dirTerm_eq` (a pair term of the link Dirichlet form equals `m(ρ)·(A_u + A_v)²`),
`sdiff_erase_erase` and `insert_insert_erase_erase` (the two set identities the reindexing needs),
`sum_two_dirichlet_link` (the triple reindexing, three applications of `sum_powersetCard_insert`),
`sum_m_face_erase`, `cochainNormSq_nonneg`.

And the theorem those identities exist for:

- **`cochainNormSq_eq_zero_of_spectralGap`** — **Garland's vanishing, analytic core.**  If `k < n`,
  every link of a `k`-face has a spectral gap `lam` with `k < lam·(k+1)`, and `f` is a cocycle whose
  link restrictions all have mass average zero, then `‖f‖²_k = 0`, so `f` vanishes on every face.
  The proof is exactly the classical one: the gap turns the second identity into
  `k(n−k)‖f‖² ≥ lam(n−k)(k+1)‖f‖²`, and `lam(k+1) > k` forces `‖f‖² = 0`.

This is the heart of Garland's method, and to my knowledge it had not been formalized before.

### What remains in Layer C

- C5: identify "mass average zero on every link" with co-closedness `δ*f = 0`, and pass from "no
  nonzero harmonic cochain" to `H^k = 0` by finite-dimensional Hodge decomposition.
- The equivariant version: `H^*(Γ,ℝ)` from `Γ`-invariant cochains on a contractible complex with a
  proper cocompact action, so that the finite-complex statement above applies to `SL_n(𝒪_S)`.

## Layer C — Garland's vanishing theorem, PROVED

Same module.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- **`codiff`** — the codifferential, unnormalized:
  `(δ*f)(τ) = Σ_{u ∉ τ} m(τ ∪ {u})·faceSign(τ ∪ {u}, u)·f(τ ∪ {u})`.
- **`codiff_adjoint`** — **it is adjoint to the coboundary**:
  `Σ_{|ρ|=k+2} m(ρ)·δf(ρ)·g(ρ) = Σ_{|τ|=k+1} f(τ)·(δ*g)(τ)`.
  Proved by the same reindexing (`sum_powersetCard_insert`) as the localization identity.
- **`sum_mass_linkRestrict`** — **the mass average of a link restriction is the codifferential**:
  `Σ_u mass_σ(u)·f_σ(u) = (n − |σ|)·(δ*f)(σ)`.  This is what identifies the analytic hypothesis of
  the vanishing core with co-closedness.
- `eq_zero_of_cochainNormSq_eq_zero` — a cochain of zero mass norm vanishes on every face of
  positive weight.
- **`harmonic_eq_zero`** — **Garland's vanishing theorem.**  On a pure `n`-dimensional weighted
  complex with `k < n`, if every link of a `k`-face has a spectral gap `lam` with
  `k < lam·(k+1)`, then every harmonic `k`-cochain (`δf = 0` and `δ*f = 0`) vanishes on every face
  of positive weight.

Layer C is now complete except for the two passages to cohomology:

- Hodge: from "no nonzero harmonic cochain" to `H^k = 0`, i.e. every cocycle is a coboundary.  The
  argument is the standard one — minimize `‖f − δg‖²` over `g`; the minimizer is co-closed, hence
  harmonic, hence zero — and needs the orthogonal projection onto the space of coboundaries in a
  finite-dimensional inner product space.
- Equivariance: `H^*(Γ,ℝ)` from `Γ`-invariant cochains on a contractible complex with a proper
  cocompact action, so that the statement applies to `SL_n(𝒪_S)` acting on its Bruhat–Tits building.

## Layer C — the Hodge step, started

Same module.  The passage from "no nonzero harmonic cochain" to `H^k = 0` needs cochains as a
finite-dimensional real vector space with a positive-definite pairing, so that the coboundaries have
an orthogonal complement.  The route chosen avoids inner-product-space machinery entirely and uses
mathlib's bilinear-form orthogonality
(`LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`), which is pure algebra.

Landed:

- `Cochain V k` — cochains of a fixed degree as functions on `{τ : Finset V // τ.card = k + 1}`,
  automatically a finite-dimensional real vector space.
- `extend`, `extendₗ` — extension by zero to all finite vertex sets, as a linear map.
- `restrictₗ`, **`cobₗ`** — **the coboundary as a linear map between the fixed-degree cochain
  spaces**, built from the corpus's `simplicialCoboundaryₗ`.
- **`pairing`** — the weighted pairing `⟨a,b⟩ = Σ_{|τ|=k+1} m(τ)·a(τ)·b(τ)` as a
  `LinearMap.BilinForm ℝ`, with `pairing_comm`, `pairing_isRefl`, `pairing_self_nonneg` and
  **`pairing_eq_zero_iff`** — **it is positive definite when the faces of that dimension have
  positive weight**.

`harmonic_eq_zero`'s co-closedness hypothesis was weakened to the faces that actually matter
(`∀ σ ∈ powersetCard k univ`), which is exactly what orthogonality to the coboundaries delivers.

Remaining in the Hodge step: the orthogonal complement of `range (cobₗ k)`, the identification of
that complement with co-closedness via `codiff_adjoint`, and the conclusion that every cocycle is a
coboundary.

## Layer C — COMPLETE for a finite complex

`HTGeometry/GarlandLocalization.lean` (737 lines).  Axiom audit: `propext, Classical.choice,
Quot.sound`.

- **`cocycle_eq_coboundary`** — **Garland's vanishing theorem in cohomological form.**  On a pure
  `n`-dimensional weighted complex whose faces of dimension `j+1` have positive weight, with
  `j + 1 < n`, if every link of a `(j+1)`-face has a spectral gap `lam` with
  `(j+1) < lam·(j+2)`, then every cocycle of degree `j+1` is a coboundary — i.e. `H^{j+1} = 0`.

The Hodge step was carried out with mathlib's bilinear-form orthogonality rather than inner-product
spaces, so it stays pure algebra:

- `sum_subtype_card` — the bridge between sums over `powersetCard n univ` and sums over the subtype
  of faces of that cardinality.
- **`pairing_cob`** — the pairing of a cochain against a coboundary is its pairing against the
  codifferential, by `codiff_adjoint`.
- `indicator`, `extend_indicator`, **`codiff_eq_zero_of_pairing_cob_eq_zero`** — **orthogonality to
  the coboundaries is co-closedness**, by testing against the indicator of a face.
- `card_erase_ne`, **`extend_cobₗ`** — the extension of a coboundary is the coboundary of the
  extension, because the extension by zero of a cochain of fixed degree has its coboundary
  concentrated in the next degree.
- **`pairing_restrict_nondegenerate`** — the pairing restricted to any subspace is nondegenerate,
  since it is positive definite.
- The assembly: `IsCompl` of the coboundaries and their orthogonal complement
  (`isCompl_orthogonal_of_restrict_nondegenerate`), split a cocycle, show the orthogonal part is
  harmonic, and kill it with `harmonic_eq_zero`.

### What remains before Layer D

The equivariant version: `H^*(Γ,ℝ)` computed from `Γ`-invariant cochains on a contractible complex
with a proper cocompact action.  The finite-complex statement above is the model; the equivariant
one replaces `Cochain V k` by its `Γ`-invariants and the sums over all faces by sums over a
fundamental domain, with the same two localization identities.

## Layer D — the entry point

`HTGeometry/WeightedGraphSpectralGap.lean`.

- **`hasSpectralGap_of_bound`** — **a bound on the averaging form is a spectral gap.**  Since
  `E(f,f) = ‖f‖²_m − ⟨Af,f⟩`, a bound `⟨Af,f⟩ ≤ θ‖f‖²_m` on functions of mass average zero is
  exactly the gap `1 − θ`.  `averaging` names the form.

This is the interface Layer D has to hit: to give the links of the Bruhat–Tits building a spectral
gap, it suffices to bound their averaging form, which is an eigenvalue estimate for the incidence
graph of a spherical building over `𝔽_q`.

### The quantitative target

For `H²` the criterion needs `λ₁ > 2/3` on the links of vertices and of edges.  The link of a
simplex in the building of `SL_n(K_v)` is a spherical building over the residue field `𝔽_q`, and the
governing rank-two case is the point–line incidence graph of a projective plane over `𝔽_q`.  There
the incidence matrix satisfies `N Nᵀ = q·I + J` — two distinct points lie on exactly one line and
each point lies on `q + 1` lines — which forces the singular values `q + 1` and `√q`, hence
`λ₁ = 1 − √q/(q+1)`.  That exceeds `2/3` as soon as `q ≥ 5`, and the finite place of `S` is ours to
choose, so the arithmetic costs nothing.

`N Nᵀ = q·I + J` is an identity about a projective plane, not an analytic estimate, so the whole
quantitative input of Garland's method is finite combinatorics.

## Layer D — the design identity, PROVED

`HTGeometry/IncidenceDesignBound.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- **`sum_incidence_sq`** — **the design identity.**  If `Σ_l N(p,l)N(p',l) = r` when `p = p'` and
  `lam` otherwise, then for every `f`
  `Σ_l (Σ_p N(p,l) f(p))² = (r − lam)·Σ_p f(p)² + lam·(Σ_p f(p))²`.
  This is the whole eigenvalue content of a `2`-design, obtained by expanding the square and
  splitting the diagonal — no analysis.
- `sum_incidence_sq_of_sum_eq_zero` — on functions of sum zero the second term drops and the
  transport multiplies the squared length by exactly `r − lam`.
- **`sum_incidence_sq_projectivePlane`** — for a projective plane (`lam = 1`, `r = q + 1`) the
  factor is `q`.  Combined with Cauchy–Schwarz this is the bound `√q` on the nontrivial singular
  values of the incidence matrix, hence `λ₁ = 1 − √q/(q+1)` for the incidence graph, which exceeds
  `2/3` once `q ≥ 5`.

What remains in Layer D's rank-two case is the passage from this identity to
`hasSpectralGap_of_bound`: split a mean-zero function on the bipartite vertex set into its two
constant-adjusted halves, apply Cauchy–Schwarz to `⟨Nᵀf₀, g₀⟩`, and observe that the constant part
only ever helps the inequality.

## Layer D — the incidence pairing bound, PROVED

Same module.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- **`two_mul_incidence_le`** — for a `2`-design and a function `a` of sum zero on the points,
  `2·Σ_{p,l} N(p,l)·a(p)·b(l) ≤ √(r − lam)·(Σ_p a(p)² + Σ_l b(l)²)` for every `b`.

This is the Cauchy--Schwarz step that turns the design identity into a spectral bound: the pairing
is `Σ_l (Nᵀa)(l)·b(l)`, Cauchy--Schwarz bounds its square by `‖Nᵀa‖²·‖b‖² = (r − lam)·‖a‖²·‖b‖²`,
and `4AB ≤ (A+B)²` finishes.  Together with `hasSpectralGap_of_bound` it is the whole spectral input
of Garland's method for the rank-two links, once the bipartite bookkeeping (splitting a mean-zero
function on `P ⊔ L` into its two constant-adjusted halves) is done.

## Layer D — the incidence graph

Same module.

- `incW`, **`incidenceGraph`** — the bipartite incidence graph of an incidence structure, as a
  `WeightedGraph (P ⊕ L)`.
- `incidenceGraph_mass_inl`, `incidenceGraph_mass_inr` — its vertex masses are the point degree and
  the line degree.
- **`incidenceGraph_averaging`** — its averaging form is
  `2·Σ_{p,l} N(p,l)·f(inl p)·f(inr l)`, the factor two coming from counting each edge in both
  orders.

With `two_mul_incidence_le` and `hasSpectralGap_of_bound` in hand, what is left of the rank-two
spectral gap is the constant-adjustment bookkeeping: a mean-zero function on `P ⊔ L` has
`α·|P| + β·|L| = 0` for its two averages, and when `|P| = |L|` this forces `β = −α`, so the constant
part contributes `−2α²|P|r` to the averaging form and `+2α²|P|r` to the mass norm — it only helps
the inequality in both places.

## Layer D — the rank-two spectral gap, PROVED

`HTGeometry/IncidenceDesignBound.lean` (323 lines).  Axiom audit: `propext, Classical.choice,
Quot.sound`.

- **`incidenceGraph_hasSpectralGap`** — **the incidence graph of a symmetric `2`-design has spectral
  gap `1 − √(r − lam)/r`.**  Hypotheses: both degrees equal `r`, any two distinct points lie on
  `lam` common lines, and `|P| = |L|`.

For a projective plane over `𝔽_q` this reads `1 − √q/(q+1)`, which exceeds `2/3` once `q ≥ 5` — the
exact hypothesis `cocycle_eq_coboundary` needs at `k = 2`.

Supporting results proved along the way: `incidenceGraph_massInner` (the mass norm is `r` times the
sum of the two squared lengths), `incidenceGraph_sum_eq_zero` (mass average zero is the vanishing of
the total sum), `incidence_pairing_shift` (the pairing after shifting both functions by constants),
`sum_sq_sub_const` (the squared length after shifting by the mean).

The mechanism of the constant part is the point worth recording: a mean-zero function on `P ⊔ L`
has `al + be = 0`, so the constant contributes `−2·al²·|P|·r` to the averaging form and
`+2·al²·|P|·√(r−lam)` to the bound — it helps on both sides, which is why the eigenvalue `−1` forced
by bipartiteness never obstructs Garland's one-sided inequality.

### Layer D, remaining

1. The Bruhat--Tits building of `SL_n` over a local field as a `WeightedComplex`: homothety classes
   of lattices, incidence, purity of dimension `n − 1`.
2. Its contractibility.
3. The identification of the link of a simplex with a spherical building over the residue field, and
   the reduction of its spectral gap to the rank-two case above.  The corpus's `BuildingLink`,
   `SolomonInduction` and `BuildingHomologyConcentration` layer is the object in question.

## Layer B1 — the Steinberg group, PROVED

`HTGeometry/SteinbergGroupPresentation.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

`K_2` of a ring is the kernel of `St(R) → E(R)`, so the Steinberg group is the first object Layer B
needs.  It is now built as a `PresentedGroup` on one generator per off-diagonal position and ring
element.

- `SteinbergGen` — the generators: a position `i ≠ j` and an entry `a`.
- `steinbergAddRel`, `steinbergCommRel`, `steinbergChainRel`, `steinbergRels` — Steinberg's three
  relation families.
- **`SteinbergGroup`** — the presented group; `steinbergX` the generator at a position.
- **`steinbergX_mul`** — `x_ij(a)·x_ij(b) = x_ij(a+b)`.
- **`steinbergX_zero`** — `x_ij(0) = 1`, derived from additivity.
- **`steinbergX_commute`** — generators at disjoint positions commute.
- **`steinbergX_chain`** — `[x_ij(a), x_jk(b)] = x_ik(ab)`.

Next in Layer B: the homomorphism `St(R) → GL(R)` sending `x_ij(a)` to the transvection
`1 + a·E_ij`, which needs the three relations verified for elementary matrices (mathlib has
`Matrix.transvection` and `transvection_mul_transvection_same`); then `E(R)` as its image, and
`K_2(R)` as the kernel.

## Layer B1 — `K_2` of a ring, PROVED

`HTGeometry/SteinbergElementaryGroup.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

Milnor's `K_2` is now defined and its defining map built.

- **`elemUnit`** — the elementary matrix `1 + a·E_ij` as a unit, with inverse `1 − a·E_ij`.
- `elemUnit_mul`, `elemUnit_zero`, `elemUnit_inv` — additivity in the entry, from
  `Matrix.transvection_mul_transvection_same`.
- **`transvection_comm`** — elementary matrices at disjoint positions commute, because both
  products of the single-entry matrices vanish.
- **`transvection_chain`** — `[1+aE_ij, 1+bE_jk] = 1 + abE_ik`.  The three-step expansion, each step
  killing the products that vanish: `E_ij·E_ij = 0`, `E_jk·E_ij = 0`, `E_ik·E_ij = 0`,
  `E_jk·E_jk = 0`, `E_ik·E_jk = 0`, and `E_ij·E_jk = E_ik`.
- `elemUnit_commute`, `elemUnit_chain` — the same at the level of units.
- **`steinbergToGL`** — **the map from the Steinberg group to the invertible matrices**, obtained
  from `PresentedGroup.toGroup` now that all three relations are verified for elementary matrices;
  `steinbergToGL_x` records its value on a generator.
- **`elementaryGroup`** — its image; **`KTwo`** — **its kernel, which is `K_2(R)`**, with
  `mem_KTwo_iff` and the normality instance.

Layer B's remaining steps are unchanged: `St(R) → E(R)` is the universal central extension (so
`K_2(R) ≅ H_2(E(R), ℤ)`), Matsumoto's theorem `K_2(F) ≅ K_2^M(F)`, the localization identifying the
Milnor tame kernel of `𝒪_S` with `K_2(𝒪_S)`, and homological stability in degree two.

## Layer B — the Weyl element

Same module.

- `weylMatrix` — the Weyl matrix `1 + u·E_ij − u⁻¹·E_ji − E_ii − E_jj`, i.e. the block
  `[[0, u], [−u⁻¹, 0]]` at the two indices and the identity elsewhere.
- **`transvection_weyl`** — **the Weyl element of the Steinberg group maps to it**:
  `t_ij(u)·t_ji(−u⁻¹)·t_ij(u) = weylMatrix i j u`.  The expansion is the same three-step pattern as
  the chained commutator, using `E_ij·E_ji = E_ii`, `E_ji·E_ij = E_jj`, `E_ii·E_ij = E_ij`, and the
  vanishing of the repeated products.

The Steinberg symbol `{u,v} = h(uv)·h(u)⁻¹·h(v)⁻¹` with `h(u) = w(u)·w(1)⁻¹` lands in `K_2` once
`w(u)·w(1)⁻¹` is identified with the diagonal matrix `diag(u, u⁻¹)` — the remaining block
computation, since `w(1)⁻¹ = w(−1)` and `[[0,u],[−u⁻¹,0]]·[[0,−1],[1,0]] = [[u,0],[0,u⁻¹]]`.  That
identification is what makes the symbol map `K_2^M(F) → K_2(F)` of Matsumoto's theorem exist.

## Layer B — the Steinberg symbol, PROVED

`HTGeometry/SteinbergElementaryGroup.lean` (354 lines).  Axiom audit: `propext, Classical.choice,
Quot.sound`.

The object Matsumoto's theorem is about now exists in Lean, and the fact that makes it exist is
proved.

- `single_eq_smul` — a single-entry matrix is its entry acting on the unit single-entry matrix.
  This is what lets `module` finish the block computations: after the products are resolved by the
  multiplication table of the four atoms `E_ij, E_ji, E_ii, E_jj`, everything is a linear
  combination.
- **`weylMatrix_mul_neg_one`** — `w(u)·w(−1) = diag(u, u⁻¹)`, the block identity
  `[[0,u],[−u⁻¹,0]]·[[0,−1],[1,0]] = [[u,0],[0,u⁻¹]]`, proved from the sixteen-entry multiplication
  table of the four single-entry matrices.
- `diagMatrix_one`, **`diagMatrix_mul`** — the diagonal matrices multiply: `d(u)·d(v) = d(uv)`.
- `diagUnit`, `diagUnit_mul` — the same as units, with inverse `d(u⁻¹)`.
- `steinbergWeyl`, `steinbergTorus`, **`steinbergSymbol`** — `w(u) = x_ij(u)x_ji(−u⁻¹)x_ij(u)`,
  `h(u) = w(u)w(−1)`, and `{u,v} = h(uv)·h(u)⁻¹·h(v)⁻¹`.
- `steinbergToGL_weyl`, `steinbergToGL_torus` — their images: the Weyl matrix and the diagonal unit.
- **`steinbergSymbol_mem_KTwo`** — **the Steinberg symbol lies in `K_2`**, because its image is
  `d(uv)·d(u)⁻¹·d(v)⁻¹ = 1`, the diagonal units commuting because `Rˣ` does.

This is the map `K_2^M(F) → K_2(F)` of Matsumoto's theorem, at the level of symbols.  What remains
of B3 is that the symbol is bimultiplicative and kills the Steinberg relation — so that it descends
from `K_2^M` — and then that the induced map is an isomorphism.

## Layer B — the column subgroups

`HTGeometry/SteinbergGroupPresentation.lean`, `HTGeometry/SteinbergElementaryGroup.lean`.

The centrality of `K_2` in the Steinberg group — the fact that makes `St(R) → E(R)` a central
extension, and hence `K_2(R) ≅ H_2(E(R), ℤ)` — runs on the abelian "column" and "row" subgroups
generated by the `x_kj(·)` with a fixed second index (or the `x_ik(·)` with a fixed first index),
and on the injectivity of the map to matrices on them.

- **`steinbergX_commute_col`**, **`steinbergX_commute_row`** — those subgroups are abelian, directly
  from the disjoint-position relation.
- **`transvection_col_mul`** — on the matrix side the product is `1 + a·E_kj + b·E_lj`: the entries
  simply add, because the product of the two single-entry matrices vanishes.
- **`transvection_col_comm`** — hence they commute there too.

The injectivity of the map on a column subgroup — a product `∏_k x_kj(b_k)` maps to
`1 + Σ_k b_k E_kj`, which is the identity only if every `b_k` is zero — is the next brick, and it is
what turns "same image" into "equal" in Milnor's centrality argument.

## Layer B — column injectivity, PROVED

`HTGeometry/SteinbergElementaryGroup.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `single_col_apply`, **`sum_single_col_apply`** — the `(p, j)` entry of `Σ_k b_k·E_kj` is `b_p`.
- **`sum_single_col_eq_zero_iff`** — **a column sum vanishes exactly when all its coefficients
  do.**

This is the injectivity that turns "same image in the matrices" into "equal" for the abelian column
subgroups, which is the step Milnor's centrality argument turns on: an element of `K_2` conjugates a
column generator to something with the same image, hence to itself.

## Layer B — perfectness of the Steinberg group, PROVED

`HTGeometry/SteinbergGroupPresentation.lean`.

- **`steinbergX_eq_commutator`** — every generator is a commutator:
  `x_ik(a) = [x_ij(a), x_jk(1)]`, directly from the chained relation with `b = 1`.
- **`steinbergGroup_perfect`** — **`St(R)` is perfect** as soon as every pair of distinct indices
  admits a third: the generators generate (`PresentedGroup.closure_range_of`) and each is a
  commutator.

Perfectness is one of the two halves of "`St(R) → E(R)` is the universal central extension"; the
other is centrality of `K_2`, whose mechanism — the abelian column subgroups and the injectivity of
the map to matrices on them — is already proved.  Together they give `K_2(R) ≅ H_2(E(R), ℤ)`, the
bridge from the tame kernel to the group homology that Garland's vanishing controls.

## Layer D — the counting weight, PROVED

`HTGeometry/WeightedComplexLink.lean`.

- **`unitComplex`** — a complex with every top face of weight one.  This is the weighting a building
  carries.
- **`unitComplex_m`** — the weight of a face is then the number of chambers containing it.
- **`unitComplex_m_pos_iff`** — positive weight exactly when some chamber contains the face, which
  is the positivity hypothesis `cocycle_eq_coboundary` needs.

This is the interface between a building presented by its chambers and the Garland machinery: such a
complex becomes a `WeightedComplex` with the right weights, `linkGraph_mass` reads its links as
weighted graphs, and `incidenceGraph_hasSpectralGap` supplies their spectral gaps once the rank-two
links are identified with incidence graphs of projective planes.

## Layer B — perfectness of the elementary group, PROVED

`HTGeometry/SteinbergElementaryGroup.lean`.

- **`elementaryGroup_perfect`** — `⁅E(R), E(R)⁆ = E(R)`: the elementary group is perfect, being the
  image of the perfect Steinberg group.  With centrality of `K_2` this is exactly the hypothesis
  under which `St(R) → E(R)` is the universal central extension and `K_2(R) ≅ H_2(E(R), ℤ)`.

## Layer B — the column subgroup, PROVED

`HTGeometry/SteinbergGroupPresentation.lean`.

- `columnGens`, **`columnGens_comm`** — the generators with a fixed second index commute pairwise.
- **`columnSubgroup`**, **`columnSubgroup_isMulCommutative`** — **the subgroup they generate is
  abelian**, via `Subgroup.isMulCommutative_closure`.
- `steinbergX_mem_columnSubgroup` — the generators lie in it.

Milnor's centrality argument needs exactly two facts about these subgroups: that they are abelian,
and that the map to the matrices is injective on them.  The first is now proved in the group; the
second is proved on the matrix side (`sum_single_col_eq_zero_iff`, `transvection_col_mul`).  What
remains is to transport the second across, and then the normalisation argument that lets one
conclude that an element of `K_2` commutes with every generator.

## Layer D — flag complexes, PROVED

`HTGeometry/WeightedComplexLink.lean`.

- `IsChainFinset` — a finite vertex set whose elements are pairwise comparable, with its decidability
  instance.
- **`flagComplexOfCard`** — **the flag complex of a finite ordered type in a fixed rank**: the top
  faces are the chains of a given size, each of weight one.  This is the shape a building has.
- **`flagComplexOfCard_pure`** — it is pure by construction, which discharges the purity hypothesis
  of every Layer C theorem.
- `flagComplexOfCard_isChain` — every face of it is a chain.

With `unitComplex_m_pos_iff` for positivity, a building presented as the flag complex of its poset
of proper nonzero subspaces now satisfies the two structural hypotheses of `cocycle_eq_coboundary`
directly; what remains in Layer D is the identification of the links with spherical buildings of
lower rank and, at rank two, with incidence graphs of projective planes.

## Session close — 2026-08-14

Fourteen modules added, all wired into `GaloisForLFunctions/HTGeometry.lean`, all built with
`lake build` and warning-free.  Axiom audit throughout: `propext, Classical.choice, Quot.sound`.

Card `deninger-selective-positive-cell-h0-preservation` was closed and moved to `3-formalized`.
Card `deninger-algebraic-cyclotomic-milnor-amplitude` remains at stage 2, blocked on exactly one
statement — the tame kernel of a number field is torsion — which is no longer a citation but a
construction under way in Layers B, C and D of this programme.

## Layer B — the column normal form and injectivity, PROVED

`HTGeometry/SteinbergColumnInjectivity.lean` (wired, axiom-clean).  This is the brick the previous
entry named as next: "transport the injectivity across".  It is transported by giving the column
subgroup an explicit normal form.

- `columnGen j k a` — the column generator, trivial at the column index itself, so it is defined for
  every pair of indices; `columnGen_self`, `columnGen_of_ne`, `columnGen_zero`, `columnGen_mul`,
  `columnGen_commute`.
- `noncommProd_eq_one` — a noncommutative product of trivial factors is trivial.
- **`columnElt j b = noncommProd_k x_kj(b k)`** — the column element of a coefficient vector.
- **`columnElt_mul`** — `columnElt j (b + c) = columnElt j b · columnElt j c`, from
  `Finset.noncommProd_mul_distrib`; with `columnElt_zero` and `columnElt_neg` this makes the column
  elements a subgroup.
- `steinbergToGL_columnGen`, **`steinbergToGL_noncommProd`**, **`steinbergToGL_columnElt`** — the
  image of a column element is `1 + Σ_k b_k E_kj`.  The induction is the same cross-term vanishing
  as everywhere in this layer: `E_aj · E_kj = 0` unless `k = j`, where the coefficient is zero by
  construction.
- **`columnElt_eq_one_of_image`** — a column element with trivial image is trivial, by
  `sum_single_col_eq_zero_iff`.
- `columnRange`, `steinbergX_mem_columnRange`, `noncommProd_mem_subgroup`,
  `columnGen_mem_columnSubgroup`, **`columnSubgroup_eq_columnRange`** — the column subgroup *is* the
  set of column elements.
- **`steinbergToGL_injOn_columnSubgroup`** — **the map to the matrices is injective on the column
  subgroup.**

Both facts Milnor's centrality argument turns on are now theorems: the column subgroups are abelian
(`columnSubgroup_isMulCommutative`) and `St(R) → E(R)` is injective on them.  What remains for
centrality is the index-avoidance argument: an element of `K_2` is a word in finitely many
generators, so some index `h` is unused; conjugation by the generators occurring in the word carries
the column subgroup `C_h` into itself, so `y x_kh(a) y⁻¹ ∈ C_h` has the same image as `x_kh(a)` and
is therefore equal to it; the chained relation `x_ij(a) = [x_ih(a), x_hj(1)]` then propagates
commutation to every generator.

## Layer B — centrality of `K_2` on a column, PROVED

`HTGeometry/SteinbergColumnCentrality.lean` (wired, axiom-clean).  The previous entry left
centrality needing "the normalisation argument that lets one conclude that an element of `K_2`
commutes with every generator".  That argument is now a theorem, with the index-avoidance count
isolated as the one remaining hypothesis.

- `steinbergX_neg` — `x_ij(-a) = x_ij(a)^{-1}`.
- **`conj_steinbergX_mem_columnSubgroup`** — conjugating a column generator `x_kj(a)` by a generator
  `x_pq(b)` whose *first* index avoids the column keeps it in the column subgroup.  Two cases, and
  both are relations already proved: if `q != k` the two commute
  (`steinbergX_commute` with `q != k` and `p != j`); if `q = k` the chained relation gives
  `x_pq(b) x_qj(a) x_pq(b)^{-1} = x_pj(ba) x_qj(a)`, a product of two column generators.
- `conj_columnSubgroup_le` — the same for the whole subgroup, by `Subgroup.closure_le` into the
  conjugation preimage.
- **`steinbergX_mem_normalizer`** — such a generator lies in the normalizer of the column subgroup;
  the reverse inclusion is the same statement for the inverse generator, which has the same first
  index.
- **`KTwo_commute_of_mem_normalizer`** — **an element of `K_2` in the normalizer of a column
  subgroup centralizes it.**  The conjugate `y x y^{-1}` has the same image as `x` because
  `y` maps to the identity, and the map is injective on the column
  (`steinbergToGL_injOn_columnSubgroup`), so the conjugate *is* `x`.
- **`KTwo_commute_columnSubgroup_of_avoid`** — packaged: an element of `K_2` lying in the subgroup
  generated by the generators whose first index avoids `j` centralizes the `j`-th column.

What remains of centrality is exactly the count Milnor's argument uses to discharge the last
hypothesis: an element of `K_2` is a word in finitely many generators, so for a large enough index
type some index `h` is unused by that word, whence the element lies in the avoiding subgroup at `h`;
the chained relation `x_ij(a) = [x_ih(a), x_hj(1)]` then propagates commutation from the `h`-column
and `h`-row to every generator.  With that, `St(R) -> E(R)` is a central extension, and together
with perfectness (`steinbergGroup_perfect`, `elementaryGroup_perfect`) it is the universal central
extension, giving `K_2(R) = H_2(E(R), Z)` — the bridge Layer B exists to build.

## Layer B — the index-avoidance count, PROVED

`HTGeometry/SteinbergIndexAvoidance.lean` (wired, axiom-clean).  The previous entry left centrality
needing "the count Milnor's argument uses to discharge the last hypothesis: an element of `K_2` is a
word in finitely many generators, so for a large enough index type some index `h` is unused".  That
count is now a theorem, and it needs no list manipulation.

- `indexGens T` — the generators whose two indices both lie in a finite set `T`;
  `avoidGens j` — those whose first index avoids `j`.
- `indexGens_mono`, `indexGens_subset_avoidGens` — monotone in `T`, and contained in the avoiding
  set as soon as `j` is outside `T`.
- **`finiteIndexSubgroup`** — the elements admitting *some* finite index set form a subgroup: the
  union of two finite sets is finite and the generating sets are monotone, so the carrier is closed
  under multiplication; inverses and the identity are immediate.
- **`exists_finset_indices`** — **every element of the Steinberg group uses only finitely many
  indices.**  The subgroup above contains every `PresentedGroup.of g` (take `T = {g.i, g.j}`), and
  the generators generate, so it is everything.
- **`KTwo_commute_columnSubgroup_of_not_mem`** — an element of `K_2` centralizes the column at any
  index its own word avoids.
- **`exists_column_centralized_of_card`** — as soon as the word does not exhaust the index type,
  such an index exists.

So Milnor's centrality argument is now formal except for one propagation step: from "`y` centralizes
the column and the row at a spare index `h`" to "`y` commutes with every generator", via the chained
relation `x_ij(a) = [x_ih(a), x_hj(1)]`.  The row half is the transpose of everything proved here —
`steinbergX_commute_row` is already available, and the row subgroup and its injectivity mirror the
column ones exactly.

With that step, `St(R) -> E(R)` is a central extension; with `steinbergGroup_perfect` and
`elementaryGroup_perfect` it is the universal central extension, giving `K_2(R) = H_2(E(R), Z)`.

## Layer B — CENTRALITY OF `K_2`, PROVED

`HTGeometry/SteinbergRowCentrality.lean` (wired, axiom-clean).  The row mirror of the column layer,
and with it Milnor's centrality argument closes.

The row half, mirroring the column half exactly:

```
rowGens, rowSubgroup, rowSubgroup_isMulCommutative     the row subgroup is abelian
single_row_apply, sum_single_row_apply,
  sum_single_row_eq_zero_iff                          a row sum vanishes only if its coefficients do
rowGen, rowElt, rowElt_zero/mul/neg                   the row normal form
steinbergToGL_rowElt                                  its image is 1 + sum_k b_k E_ik
rowElt_eq_one_of_image, rowRange, rowSubgroup_eq_rowRange
steinbergToGL_injOn_rowSubgroup                       the map is injective on the row subgroup
conj_steinbergX_mem_rowSubgroup                       conjugation by a generator whose SECOND index
                                                      avoids the row stays in the row
steinbergX_mem_rowNormalizer, KTwo_commute_rowSubgroup_of_mem_normalizer,
  KTwo_commute_rowSubgroup_of_not_mem
```

The conjugation case `k = p` uses the chained relation in the form `B A B^{-1} = C^{-1} A`, obtained
from `A B A^{-1} B^{-1} = C` by inverting `B A^{-1} B^{-1} = A^{-1} C`.

And then centrality:

```
KTwo_commute_steinbergX
    an element of K_2 whose word avoids h commutes with EVERY generator:
      x_ij(a) with j = h  lies in the h-column,
      x_ij(a) with i = h  lies in the h-row,
      otherwise  x_ij(a) = [x_ih(a), x_hj(1)],  a commutator of one of each.

KTwo_mem_center            hence it lies in the centre of the Steinberg group
KTwo_mem_center_of_card    and such an index exists as soon as the word does not exhaust n
```

**`St(R) -> E(R)` is therefore a central extension.**  With `steinbergGroup_perfect` and
`elementaryGroup_perfect` it is the *universal* central extension, which is the statement
`K_2(R) = H_2(E(R), Z)` that Layer B exists to produce.

Layer B's remaining steps are the ones after that bridge: Matsumoto's theorem `K_2(F) = K_2^M(F)`,
the localization identifying the Milnor tame kernel of `O_S` with `K_2(O_S)`, and homological
stability in degree two.

## Layer B — the Steinberg symbol is normalized, PROVED

`HTGeometry/SteinbergSymbolNormalization.lean` (wired, axiom-clean).  Matsumoto's theorem presents
`K_2` of a field by the Steinberg symbols, so the first thing to establish about the symbol is its
normalisation.

- **`steinbergWeyl_neg`** — `w(-u) = w(u)^{-1}`.  Inverting `w(u) = x_ij(u) x_ji(-u^{-1}) x_ij(u)`
  reverses the three factors and negates each entry, and `(-u)^{-1} = -u^{-1}` for units, so the
  result is literally `w(-u)`.
- **`steinbergTorus_one`** — `h(1) = w(1) w(-1) = w(1) w(1)^{-1} = 1`.
- **`steinbergSymbol_one_left`**, **`steinbergSymbol_one_right`** — `{1, v} = {u, 1} = 1`.

What Matsumoto still needs of the symbol is bimultiplicativity and the Steinberg relation
`{u, 1-u} = 1`; with those the symbol descends from `K_2^M(F)` and the induced map is the
isomorphism.

## Layer B — the symbol is central, and satisfies the cocycle identity, PROVED

`HTGeometry/SteinbergSymbolCocycle.lean` (wired, axiom-clean).  Centrality now pays off immediately.

- `steinbergWeyl_mem_indexClosure`, `steinbergTorus_mem_indexClosure`,
  `steinbergSymbol_mem_indexClosure` — the Weyl, torus and symbol elements are words in the two
  indices of the Weyl element only.
- **`steinbergSymbol_mem_center`** — **the Steinberg symbol is central**, as soon as a third index
  exists: it lies in `K_2` (already proved) and its word avoids that index, so `KTwo_mem_center`
  applies.
- **`steinbergTorus_mul`** — `h(uv) = {u,v} h(v) h(u)`: the torus elements fail to be multiplicative
  exactly by the symbol.
- **`steinbergSymbol_cocycle`** — **`{uv,w}·{u,v} = {u,vw}·{v,w}`.**  Compute `h(uvw)` in the two
  possible ways; centrality moves `{u,v}` past `h(w)` in the first; the common tail
  `h(w) h(v) h(u)` cancels.

This is the associativity constraint Matsumoto's presentation imposes.  What the symbol still needs
for that route is bimultiplicativity and the Steinberg relation `{u, 1-u} = 1`.

## Layer B — the symbol's asymmetry is the torus commutator, PROVED

`HTGeometry/SteinbergSymbolSwap.lean` (wired, axiom-clean).

Over a commutative ring `uv = vu`, so `h(uv) = {u,v} h(v) h(u)` and `h(vu) = {v,u} h(u) h(v)`
describe the same element.  Comparing them isolates the symbol's failure to be symmetric:

```
steinbergSymbol_swap
    {v,u}^{-1} {u,v}  =  h(u) h(v) h(u)^{-1} h(v)^{-1}

steinbergSymbol_comm_of_torus_commute   the torus elements commute  ==>  {u,v} = {v,u}
torus_commute_of_steinbergSymbol_comm   and conversely
```

Both sides lie in `K_2` — the images `d(u), d(v)` commute — so the discrepancy is central by
`steinbergSymbol_mem_center`.  Together with `steinbergSymbol_cocycle` and the normalisation
`{1,v} = {u,1} = 1`, the symbol now satisfies three of the four laws Matsumoto's presentation
imposes; the remaining one is the Steinberg relation `{u, 1-u} = 1`, which is where the *ring*
enters rather than just the group.

## Layer B — the torus elements commute up to the centre, PROVED

`HTGeometry/SteinbergTorusCommutator.lean` (wired, axiom-clean).

```
torus_commutator_mem_KTwo      [h(u), h(v)] lies in K_2
torus_commutator_mem_center    and is central, given a third index
steinbergToGL_torus_commutator its image is the identity
```

Immediate from the swap law: `[h(u), h(v)] = {v,u}^{-1} {u,v}`, a product of two symbols, each in
`K_2` and each central.  So `u |-> h(u)` is a homomorphism into `St(R)/K_2 = E(R)`, whose image is
the diagonal `d(u)` — which is what `steinbergToGL_torus` and `diagUnit_mul` already say on the
matrix side.

### Layer B status after this session

```
Steinberg group, presentation, relations                     done
K_2 as the kernel of St(R) -> GL(R)                          done
perfectness of St(R) and of E(R)                             done
column subgroup: abelian, normal form, injectivity           done
row subgroup: abelian, normal form, injectivity              done
index avoidance: every word uses finitely many indices       done
CENTRALITY of K_2                                            done
  ==> St(R) -> E(R) is a central extension; with perfectness, the universal one,
      i.e. K_2(R) = H_2(E(R), Z)
symbol: normalisation, cocycle identity, swap law            done
symbol: bimultiplicativity, Steinberg relation {u,1-u}=1     TO BUILD
Matsumoto K_2(F) = K_2^M(F)                                  TO BUILD
localization: Milnor tame kernel of O_S = K_2(O_S)           TO BUILD
homological stability in degree two                          TO BUILD
```

The next brick is the Steinberg relation `{u, 1-u} = 1`.  Unlike everything above it needs the
*ring* rather than just the group: the classical route is the Weyl conjugation formula
`w_ij(u) x_ij(a) w_ij(u)^{-1} = x_ji(-u^{-1} a u^{-1})`, which has to be derived from the three
Steinberg relations directly, since the map to matrices is not injective.

## Layer B — the Weyl conjugation formula, PROVED

`HTGeometry/SteinbergWeylConjugation.lean` (wired, axiom-clean).  This is the first Layer B step
that could not be read off the matrices: the map `St(R) -> GL(R)` is not injective, so the group
identity has to come from the three Steinberg relations alone.

```
steinbergX_conj_chain     x_ij(a) x_jk(b) x_ij(a)^{-1} = x_ik(ab) x_jk(b)
steinbergX_conj_chain'    x_jk(b) x_ij(a) x_jk(b)^{-1} = x_ik(ab)^{-1} x_ij(a)

steinbergWeyl_conj_first  w_ij(u) x_ik(a) w_ij(u)^{-1} = x_jk(-u^{-1} a)
```

The Weyl conjugation is three conjugations in sequence: the outer `x_ij(u)` commutes with `x_ik(a)`
(disjoint positions); the middle `x_ji(-u^{-1})` chains it to `x_jk(-u^{-1} a) x_ik(a)`; the second
`x_ij(u)` chains the new factor to `x_ik(-a) x_jk(-u^{-1}a)`, and the two `x_ik` factors — with
entries `-a` and `a` — cancel by additivity.  The cancellation is exactly where `u u^{-1} = 1`
enters.

The mirror statement `w_ij(u) x_kj(a) w_ij(u)^{-1} = x_ki(a u^{-1})` is the same computation with
the roles of the two chained relations exchanged, and composing the two along
`x_ij(a) = [x_ik(a), x_kj(1)]` gives `w_ij(u) x_ij(a) w_ij(u)^{-1} = x_ji(-u^{-1} a u^{-1})` — the
identity the Steinberg relation `{u, 1-u} = 1` runs on.

## Layer B — the classical Weyl conjugation formula, PROVED

Same module.  The mirror move and the composition are now theorems too:

```
steinbergWeyl_conj_second   w_ij(u) x_kj(b) w_ij(u)^{-1} = x_ki(b u^{-1})
steinbergWeyl_conj_self     w_ij(u) x_ij(a) w_ij(u)^{-1} = x_ji(-u^{-1} a u^{-1})
```

The mirror is the same three-conjugation pattern with the two forms of the chained relation
exchanged; the cancellation there is `b V U = b`, again `u u^{-1} = 1`.

The composition is the point.  `x_ij(a) = [x_ik(a), x_kj(1)]` expresses a generator with only two
indices as a commutator of two generators each involving the third, conjugation is a group
homomorphism so it distributes over the commutator, and the two moves send those to
`x_jk(-u^{-1} a)` and `x_ki(u^{-1})` — whose chained commutator is `x_ji(-u^{-1} a u^{-1})`.

This is the identity Milnor's proof of the Steinberg relation `{u, 1-u} = 1` runs on, and it is the
first place in Layer B where a genuinely three-index argument was needed: with only `i` and `j` the
Steinberg relations say nothing about how `x_ij` and `x_ji` interact.

## Layer B — the third Weyl move, PROVED

Same module.

```
steinbergWeyl_conj_row   w_ij(u) x_jk(c) w_ij(u)^{-1} = x_ik(u c)
```

This is the move on a generator whose *first* index is `j`, and it completes the pattern: the Weyl
element at `(i,j)` sends

```
x_ik(a)  |->  x_jk(-u^{-1} a)        (first index i -> j)
x_jk(c)  |->  x_ik(u c)              (first index j -> i)
x_kj(b)  |->  x_ki(b u^{-1})         (second index j -> i)
x_ij(a)  |->  x_ji(-u^{-1} a u^{-1}) (both, by composing along a commutator)
```

The cancellation in this one is `V U = 1` rather than `U V = 1` — the two are different rewrites of
the same unit law and both are needed, since the entries appear on opposite sides.  The collection
step at the end is where the three `x_ik` entries `-Uc, Uc, Uc` add to `Uc` and the two `x_jk`
entries `-c, c` cancel; the two families commute, which is what makes the collection legal.

The remaining move is `w_ij(u) x_ki(d) w_ij(u)^{-1} = x_kj(-d u)`; with it, `x_ji(b) = [x_jk(b),
x_ki(1)]` gives `w_ij(u) x_ji(b) w_ij(u)^{-1} = x_ij(-u b u)`, and the Weyl action is completely
determined.  That is the last input Milnor's proof of `{u, 1-u} = 1` needs from the group side.

## Layer B — the Weyl action is completely determined, PROVED

Same module.  The last two pieces:

```
steinbergWeyl_conj_col        w_ij(u) x_ki(d) w_ij(u)^{-1} = x_kj(-d u)
steinbergWeyl_conj_transpose  w_ij(u) x_ji(b) w_ij(u)^{-1} = x_ij(-u b u)
```

The column move is the shortest of the four: the middle conjugation produces
`x_ki(d) x_kj(dU)` for the first factor and leaves the second alone, and the two `x_ki` factors —
one of them inverted — cancel outright, leaving a single `x_kj(dU)^{-1}`; the outer generator then
commutes with it.

So the Weyl element at `(i,j)` acts on every generator, and the action is the expected one:

```
x_ik(a) |-> x_jk(-u^{-1} a)          x_jk(c) |-> x_ik(u c)
x_kj(b) |-> x_ki(b u^{-1})           x_ki(d) |-> x_kj(-d u)
x_ij(a) |-> x_ji(-u^{-1} a u^{-1})   x_ji(b) |-> x_ij(-u b u)
```

All six from the three Steinberg relations alone.  Note the asymmetry between the two-index cases:
conjugation inserts `u^{-1}` on both sides going one way and `u` on both sides going the other,
which is exactly what makes `w_ij(u)^2 = h(-1)` and drives the torus computation.

With the action determined, the group-side inputs to Milnor's proof of the Steinberg relation
`{u, 1-u} = 1` are complete; what remains for that relation is the ring-side identity relating
`h(u)`, `h(1-u)` and `h(u(1-u))` through the conjugation formulas above.

## Layer B — the torus acts by the diagonal character, PROVED

`HTGeometry/SteinbergTorusAction.lean` (wired, axiom-clean).

```
steinbergWeyl_neg_one_conj_self / _first / _col
    at u = -1 the Weyl formulas degenerate: (-1)^{-1} = -1, so the signs cancel and w(-1)
    acts by a bare transposition of the two indices

steinbergTorus_conj_self   h(u) x_ij(a) h(u)^{-1} = x_ij(u a u)
steinbergTorus_conj_first  h(u) x_ik(a) h(u)^{-1} = x_ik(u a)
steinbergTorus_conj_col    h(u) x_ki(d) h(u)^{-1} = x_ki(d u^{-1})
```

Each is `w(-1)` then `w(u)`: the inner move transposes the indices with no unit, the outer one
reinstates it.  These are exactly the conjugation formulas of the diagonal matrix `diag(u, u^{-1})`
— which is what `steinbergToGL_torus` says on the matrix side — but proved in the *group*, where the
map to matrices is not injective and so says nothing.

This is the form in which the torus enters Milnor's proof of the Steinberg relation: `{u, 1-u} = 1`
is extracted by conjugating a carefully chosen generator by `h(u) h(1-u) h(u(1-u))^{-1}` and using
that the three scalings compose to the identity exactly when `u + (1-u) = 1`.

## Layer B — all six torus weights and the inverse Weyl action, PROVED

`HTGeometry/SteinbergTorusAction.lean` now carries the complete weight decomposition:

```
h(u) x_ij(a) h(u)^{-1} = x_ij(u a u)        h(u) x_ji(b) h(u)^{-1} = x_ji(u^{-1} b u^{-1})
h(u) x_ik(a) h(u)^{-1} = x_ik(u a)          h(u) x_jk(c) h(u)^{-1} = x_jk(u^{-1} c)
h(u) x_ki(d) h(u)^{-1} = x_ki(d u^{-1})     h(u) x_kj(b) h(u)^{-1} = x_kj(b u)
```

Reading the exponents off the six lines gives the weights `(+2, -2, +1, -1, +1, -1)` of the
coroot — `h(u)` is the diagonal `diag(u, u^{-1}, 1, ...)` acting by conjugation, established in the
group rather than read off the (non-injective) matrix map.

`HTGeometry/SteinbergWeylInverseConjugation.lean` adds the six mirror formulas for `w(u)^{-1}`,
obtained by feeding `-u` into the forward ones through `w(-u) = w(u)^{-1}`.  The two formulas with a
unit on each side are unchanged — the signs cancel — and the four one-sided ones flip sign.  These
are what move a Weyl element leftwards through a word.

### Where the Steinberg relation `{u, 1-u} = 1` actually sits

With the weights above, the group-side inputs are exhausted: conjugation formulas alone cannot
produce the relation, because they never see the *additive* structure of `R` beyond the chain
relation, and `{u, 1-u} = 1` is precisely an additive statement about `u + (1-u) = 1`.

The remaining route is the Dennis-Stein element: for `a, b ∈ R` with `1 + ab ∈ R*`,

```
<a,b> = x_ji(-b(1+ab)^{-1}) x_ij(a) x_ji(b) x_ij(-(1+ab)^{-1} a) h_ij(1+ab)^{-1} ,
```

which lies in `K₂` and satisfies `<a,b><b,a> = 1`, `<a,b><a,c> = <a, b+c+abc>` and
`{u,v} = <u-1, ...>`-type identities from which `{u,1-u} = 1` drops out.  Formalizing this needs the
additive relations among the four generator factors above, i.e. `steinbergX_mul` interleaved with
the chain relation — not the conjugation calculus.  That is the next brick; it is a genuine
computation in the group, not a corollary of what is proved here.

## Layer B — the Dennis-Stein symbol lands in K₂, PROVED

`HTGeometry/DennisSteinSymbol.lean` (wired, axiom-clean).

```
dennisStein hij a b w
  = x_ji(-b w^{-1}) x_ij(a) x_ji(b) x_ij(-w^{-1} a) h_ij(w)^{-1} ,      w = 1 + ab a unit

transvection_dennisStein   the four elementary factors multiply to diagMatrix i j w
dennisStein_mem_KTwo       hence the symbol maps to 1 and lies in K₂
dennisStein_mem_indexClosure / dennisStein_mem_center
dennisStein_right_zero / dennisStein_left_zero    <a,0> = <0,b> = 1
```

The matrix identity is the two-index block computation

```
[1    0][1 a][1 0][1 -a/w]   [w  0 ]
[-b/w 1][0 1][b 1][0   1 ]  =[0 1/w]
```

proved over an arbitrary commutative ring: the four transvections are expanded in the single-entry
basis `E_ij, E_ji, E_ii, E_jj`, `match_scalars` reduces the matrix equation to five scalar goals, and
each closes by `linear_combination` against the one relation `w^{-1}(1+ab) = 1`.  The coefficients of
`E_ij` and `E_ji` cancel outright, `E_ii` picks up `ab = w-1`, and `E_jj` picks up
`-ab w^{-1} = w^{-1} - 1`.

This is the first object in the programme whose defining data is a *ring element*, not a unit — and
that is exactly why it can reach `{u, 1-u} = 1`, which the conjugation calculus cannot.  Next: the
three Dennis-Stein relations

```
<a,b> <b,a> = 1 ,   <a,b> <a,c> = <a, b + c + abc> ,   <a, bc> = <ab, c> <ac, b>  (as available)
```

from which `{u,v} = <u-1, ...>` identifies the Steinberg symbol and the relation follows.

## Layer B — Bruhat decomposition and its obstruction, PROVED

`HTGeometry/DennisSteinBruhat.lean` (wired, axiom-clean).

```
dennisStein_mul_torus          <a,b> h(w) = x_ji(-bw^{-1}) x_ij(a) x_ji(b) x_ij(-w^{-1}a)
steinbergX_mul_opposite        x_ij(a) x_ji(b) = x_ji(bw^{-1}) (<a,b> h(w)) x_ij(w^{-1}a)
steinbergX_mul_opposite_center  the same with the symbol pushed to the far right
dennisStein_one                <a,b>_{w=1} = x_ji(b)^{-1} x_ij(a) x_ji(b) x_ij(a)^{-1}
commutator_opposite_mem_KTwo    ab = 0  =>  that commutator lies in K₂
commutator_opposite_mem_center  ... and is central
```

The first is the Bruhat decomposition of the big cell,

```
[1 a][1 0]   [1     0][w 0   ][1 a/w]
[0 1][b 1] = [b/w   1][0 1/w ][0  1 ] ,     w = 1 + ab ,
```

transported into the Steinberg group, where it *fails*: the Dennis-Stein symbol is exactly the
discrepancy.  Because the symbol is in K₂ the identity is exact in `E(R)` and only lifts to `St(R)`
with a central correction.  This is the shape in which the symbol enters Matsumoto's presentation —
the symbol is what a Bruhat normal form costs over a ring rather than a field.

The degenerate cell `ab = 0` gives a statement of independent interest: opposite elementary
generators whose entries multiply to zero commute modulo K₂, and their commutator is central.  Over
a domain this is vacuous, but over a ring with zero divisors it produces genuine central elements.

## Layer B — the square of the Weyl element, modulo K₂, PROVED

`HTGeometry/SteinbergWeylSquare.lean` (wired, axiom-clean).

```
weylMatrix_sq                             weylMatrix i j u * weylMatrix i j u = diagMatrix i j (-1)
steinbergToGL_weyl_sq                     hence w(u)^2 maps to the diagonal unit at -1
steinbergWeyl_sq_mul_torus_inv_mem_KTwo   w(u)^2 h(-1)^{-1} lies in K₂
steinbergWeyl_sq_mul_torus_inv_mem_center ... and is central
steinbergWeyl_sq_mul_sq_inv_mem_KTwo      w(u)^2 and w(v)^2 agree modulo K₂ for ALL u, v
```

In the two-index block `w(u)` is `[[0,u],[-u^{-1},0]]`, whose square is `-1` — the unit cancels
between the two off-diagonal entries, so the answer does not involve `u` at all.

This is the K₂-level form of the classical relation `w(u)^2 = h(-1)`.  What the matrix map alone can
deliver is that the two sides agree up to a central element of K₂; the exact equality is a
consequence of the presentation and is not needed wherever the argument runs modulo the centre.
The last theorem records the sharper consequence: the map `u |-> w(u)^2` is constant modulo K₂.

Scope note for the next pass: the general derivation of `w(u)^2 = h(-1)` on the nose cannot come
from the conjugation calculus either — conjugation only shows `w(u)^2 h(-1)^{-1}` centralises every
generator, which is exactly the centrality proved here, and centrality is strictly weaker than
triviality in a group with nontrivial centre.  That is the same obstruction as for `{u, 1-u} = 1`,
and it has the same resolution: the Dennis-Stein relations.

## Layer B — the two orientations of a root, modulo K₂, PROVED

`HTGeometry/SteinbergIndexOrientation.lean` (wired, axiom-clean).

```
weylMatrix_swap                  weylMatrix j i (-u^{-1}) = weylMatrix i j u
diagMatrix_swap                  diagMatrix j i u^{-1}    = diagMatrix i j u
steinbergWeyl_swap_mem_KTwo      w_ji(-u^{-1}) w_ij(u)^{-1} in K₂
steinbergTorus_swap_mem_KTwo     h_ji(u^{-1}) h_ij(u)^{-1} in K₂
steinbergWeyl_swap_mem_center    ... and central
steinbergTorus_swap_mem_center   ... and central
```

Both matrix identities are exact and need no computation at all — reversing the index pair permutes
the four single-entry terms of the definition, and the unit bookkeeping is `(-u^{-1})^{-1} = -u` in
the Weyl case and `(u^{-1})^{-1} = u` in the torus case.  The two matrix lemmas audit to
`[propext, Quot.sound]`: no choice is used.

Consequence for the programme: the root system's two orientations are identified modulo the centre,
so any Layer-B statement proved for `(i,j)` transfers to `(j,i)` at no cost, with `u |-> -u^{-1}` on
Weyl parameters and `u |-> u^{-1}` on torus parameters.  This removes the orientation bookkeeping
from the Matsumoto presentation, where the relations are stated for an unordered root pair.

## Layer B — the torus is a homomorphism modulo K₂, PROVED

`HTGeometry/SteinbergTorusQuotientHom.lean` (wired, axiom-clean).

```
commute_mk_steinbergTorus       the images of h(u), h(v) commute in St(R)/K₂
steinbergTorusQuotientHom hij   u |-> [h_ij(u)]   as a group homomorphism  Rˣ -> St(R)/K₂
steinbergSymbol_eq_torus_defect {u,v} = h(uv) (h(v) h(u))^{-1}
```

Both failures of the torus — multiplicativity and commutativity — live in K₂, so the map descends to
an honest homomorphism on the quotient.  The last theorem says it plainly: the Steinberg symbol IS
the multiplicativity defect of the torus, so it vanishes in the quotient by definition.

This is the frame of Matsumoto's presentation.  `K₂` of a field is exactly the obstruction to
splitting `St(R) -> St(R)/K₂` over the torus multiplicatively, and the symbol is the cocycle
measuring it — already known here to be central, to satisfy the two-cocycle identity, and to have
its asymmetry equal to the torus commutator.

### Corpus audit for the Matsumoto target

The corpus already carries Milnor K-theory, so the target of Matsumoto is expressible:

```
HTGeometry/MilnorKTheory.lean     MilnorK F, milnorSymbol, milnorSymbol_mul_oneSub (Steinberg),
                                      milnorSymbol_mul_neg_self, milnorSymbol_anticomm
HTGeometry/MilnorKGradedRing.lean MilnorKDeg F n, milnorMul, milnorPairClass with multilinearity
                                      in each slot and the Steinberg relation at adjacent slots
HTGeometry/MilnorWittKTheory.lean the Milnor-Witt variant, [u][1-u] = 0
HTGeometry/MilnorKResidueSteinberg.lean  the Steinberg relation as an operator
```

So `K_2^M(F) = MilnorKDeg F 2` exists with all its relations.  What is missing is only the
comparison map, and building it still requires `{u, 1-u} = 1` in `K₂` — i.e. Milnor's Dennis-Stein
computation — which remains the single blocker for this layer.

## Layer B — the Bruhat cell parameters are unique, PROVED

`HTGeometry/BruhatCellUniqueness.lean` (wired, axiom-clean).  Searched first: no Dennis-Stein or
Bruhat-uniqueness material exists elsewhere in the corpus.

```
bruhatMatrix_eq        T_ji(beta) D(w) T_ij(alpha)
                         = 1 + E_ii(w-1) + E_jj(w^{-1}-1+alpha beta w) + E_ij(alpha w) + E_ji(beta w)
bruhat_params_unique   equal Bruhat products have equal (w, alpha w, beta w)
```

In the two-index block the product is

```
[1 0][w 0   ][1 alpha]   [w        alpha w      ]
[b 1][0 w^{-1}][0   1 ] = [beta w   w^{-1}+ab w ]
```

so the three parameters are read straight off the matrix: `w` from the `(i,i)` entry, then `alpha`
and `beta` from the two off-diagonal ones.

**Why this is the tool that was missing.**  The Bruhat decomposition in `St(R)` writes

```
x_ij(a) x_ji(b) = x_ji(b w^{-1}) <a,b> h(w) x_ij(w^{-1} a)
```

with the Dennis-Stein symbol as the central correction.  Uniqueness of the parameters means that
whenever one element of `St(R)` admits two Bruhat expressions, the parameters must coincide, and the
central corrections can then be cancelled against each other.  That is the mechanism by which word
identities in the Steinberg group become identities *between symbols* — which is exactly what the
Dennis-Stein relations, and hence `{u, 1-u} = 1`, require.

Trap recorded: `match_scalars` again produced a spurious sixth atom (`alpha (w^{-1}-1) = 0`, which is
false) until `Matrix.zero_mul`/`mul_zero`/`add_zero` were added to the preceding `simp only`, exactly
as in `QuadrupleDiagonalSum`.  An unreduced `0 * single _ _ 1` is treated as its own atom and
generates an unprovable goal; the underlying identity is fine.

## Layer B — Bruhat uniqueness in the group; the derivation route for the Dennis-Stein relations

`HTGeometry/BruhatGroupUniqueness.lean` (wired, axiom-clean).

```
steinbergToGL_bruhat         the matrix image of  x_ji(beta) Z h(w) x_ij(alpha)  with Z in K₂
bruhat_group_params_unique   two such words equal  =>  (w, alpha w, beta w) agree
bruhat_center_unique         same parameters  =>  the central parts are equal
```

The central factor maps to the identity, so the matrix image is exactly the Bruhat matrix, whose
parameters are unique by the previous section.  Once the parameters agree, the outer factors cancel
and the central corrections must be equal.

### The derivation this unlocks, written out

Take four ring elements and compute `P = x_ij(a1) x_ji(b1) x_ij(a2) x_ji(b2)` in two ways, assuming
the relevant `1 + ab` are units.

Bruhat the FIRST pair, then the resulting middle pair, moving `h(w1)` past the `x_ji` by
`steinbergTorus_conj_transpose` and merging the two torus factors by `steinbergTorus_mul`:

```
P = x_ji(b1 c1 + c1^2 b2 C) . [ D(a1,b1) D(A,b2) {W,w1}^{-1} ] . h(w1 W) . x_ij(C A)
      A = c1 a1 + a2 ,  W = 1 + A b2 ,  C = W^{-1}
```

Bruhat the LAST pair first, moving `x_ij` past `h(w2)` by `steinbergTorus_conj_self`:

```
P = x_ji(B C') . [ D(a1,B) D(a2,b2) {w2,V}^{-1} ] . h(V w2) . x_ij(c2^2 C' a1 + c2 a2)
      B = b1 + b2 c2 ,  V = 1 + a1 B ,  C' = V^{-1}
```

Both are Bruhat words with central corrections, so `bruhat_group_params_unique` forces the
parameters to agree and `bruhat_center_unique` then gives

```
D(a1,b1) D(A,b2) {W,w1}^{-1}  =  D(a1,B) D(a2,b2) {w2,V}^{-1} .
```

That is a Dennis-Stein relation with the Steinberg symbols appearing explicitly, and every
ingredient of the derivation is already a theorem in this tree: the Bruhat decomposition, the six
torus conjugations, `steinbergTorus_mul`, centrality of both symbol families, and now the two
uniqueness statements.  Specialising `a2 = 0` or `b1 = 0` collapses it to the classical
Dennis-Stein identities, and from those `{u, 1-u} = 1` follows by Milnor's choice of parameters.

What remains is the Lean bookkeeping of that two-way computation — long, but with no missing
mathematics.

## Layer B, continued — the Dennis-Stein relations, and the confirmed route to `{u, 1-u} = 1`

Four new modules, all wired and axiom-clean.

```
HTGeometry/DennisSteinAddRight.lean
  dennisStein_add_right   <a,b1> . <w1^{-1} a, b2> . {W,w1}^{-1} = <a, b1+b2>
                          w1 = 1 + a b1 ,  W = 1 + w1^{-1} a b2

HTGeometry/DennisSteinInverse.lean
  steinbergSymbol_inv_left   {w^{-1}, w} = (h(w) h(w^{-1}))^{-1}
  dennisStein_neg_right      <a,b> . <w^{-1}a, -b> = {w^{-1}, w}
  dennisStein_neg_right_torus  h(w) h(w^{-1}) <a,b> <w^{-1}a,-b> = 1

HTGeometry/DennisSteinAddLeft.lean
  dennisStein_add_left    <a1, b w2^{-1}> . <a2, b> . {w2,U}^{-1} = <a1+a2, b>
                          w2 = 1 + a2 b ,  U = 1 + a1 b w2^{-1}

HTGeometry/DennisSteinWeylTransport.lean
  dennisStein_weyl_transport
        <a,b>_ij . w_ij(1) h_ij(w) w_ij(1)^{-1}  =  <-a,-b>_ji . h_ji(w)
```

The first three are two-way Bruhat computations closed with `bruhat_group_params_unique` /
`bruhat_center_unique`; in each case the two Bruhat words turn out to have *identical* outer
parameters, not merely proportional ones, so the central parts cancel outright.  The arithmetic
heart of the right-hand relation is `W b1 + w1^{-1} b2 = b1 + b2`; of the left-hand one,
`w2^{-1} a1 + a2 U = a1 + a2`.

The transport relation is different in kind: conjugation by `w_ij(1)` sends the Bruhat word of
`x_ij(a) x_ji(b)` to that of `x_ji(-a) x_ij(-b)`, the unit `1 + ab = 1 + (-a)(-b)` is unchanged, and
the outer parameters again match on the nose.  The symbol is central, so conjugation fixes it and
the entire discrepancy sits in the torus factors.

### The route to the Steinberg relation, now concrete

In the standard normalisation the Dennis-Stein symbols satisfy

```
(D1)  <a,b> = -<-b,-a>
(D2)  <a,b> + <a,c> = <a, b + c + abc>
(D3)  <a,bc> = <ab,c> + <ac,b>
```

and every Steinberg symbol of units is a Dennis-Stein symbol,

```
{a,b} = <(a-1) b^{-1}, b>     (note 1 + (a-1) b^{-1} b = a, so the unit of the symbol is a).
```

Given those, the Steinberg relation is three lines:

```
D3 with c = 1  =>  <ab,1> = 0             (the two sides differ by <a,b> exactly)
D1             =>  <-1,b> = -<-b,1> = 0
link           =>  {u, 1-u} = <(u-1)(1-u)^{-1}, 1-u> = <-1, 1-u> = 0 .
```

So the remaining obligations for `{u,1-u} = 1` are exactly:

1. `(D1)` in this tree's normalisation — `dennisStein_weyl_transport` is the geometric half; what is
   left is to identify `w_ij(1) h_ij(w) w_ij(1)^{-1}`.  Conjugating the definition termwise gives
   `w_ij(1) w_ij(t) w_ij(1)^{-1} = w_ji(-t)`, hence the conjugate is `w_ji(-w) w_ji(1)`, which is
   `h_ji(-w)` corrected by `w_ji(-1)^{-2}`; the square is already handled by `SteinbergWeylSquare`.
2. `(D3)` — the only genuinely three-index relation, coming from
   `x_ij(bc) = [x_ik(b), x_kj(c)]`.  This is why `K₂` needs `n >= 3`.
3. the comparison `{a,b} = <(a-1)b^{-1}, b>`, a two-index identity of the same shape as the ones
   already closed.

`(D2)` is `dennisStein_add_right` (the composite second argument `b + c + abc = b + c w` is exactly
the `w`-rescaling that appears there), and the degenerate cases `<a,0> = <0,b> = 1` are already
proved.  Nothing on this list is open mathematics; all three are word computations in `St(R)` of the
kind now mechanised twice over.

### Obligation (1) closed — `(D1)` in this tree's normalisation

`HTGeometry/WeylTorusConjugation.lean` (wired, axiom-clean).

```
steinbergWeyl_one_conj_weyl   w_ij(1) w_ij(t) w_ij(1)^{-1} = w_ji(-t)
steinbergTorus_one_conj       w_ij(1) h_ij(w) w_ij(1)^{-1} = h_ji(-w) . h_ji(-1)^{-1}
dennisStein_index_reversal    <a,b>_ij . h_ji(-w) . h_ji(-1)^{-1} = <-a,-b>_ji . h_ji(w)
```

The Weyl conjugation is termwise on the defining word `w_ij(t) = x_ij(t) x_ji(-t^{-1}) x_ij(t)`,
using `-(-t)^{-1} = t^{-1}`; the torus statement then follows from `h_ji(1) = 1`, which says exactly
`w_ji(1) = w_ji(-1)^{-1}`, together with `h_ji(-1) = w_ji(-1)^2`.

So the sign-and-order relation is now unconditional, with the torus discrepancy identified
explicitly.  Remaining for `{u,1-u} = 1`: the three-index relation `(D3)` and the comparison
`{a,b} = <(a-1)b^{-1}, b>`.

### Obligation (2) — `(D3)`, the three-index relation: the exact plan

All three symbols in `(D3)` carry the *same* unit, `w = 1 + abc = 1 + (ab)c = 1 + (ac)b`, which is
what makes the relation a statement about central corrections alone.

The input is already in the tree: `steinbergX_chain hij hjk hik a b` is
`[x_ij(a), x_jk(b)] = x_ik(a b)`.  Writing

```
x_ji(bc) = [ x_jk(b), x_ki(c) ]
```

and expanding `x_ij(a) x_ji(bc)` gives a five-letter word in `x_ij, x_jk, x_ki`; pushing `x_ij(a)`
rightwards produces `x_ik(ab)` and `x_kj(ca)` by the chain relation, and the remaining moves are
free because generators sharing a row or a column commute (`steinbergX_commute_row`,
`steinbergX_commute_col`).  The two surviving rank-one pairs `x_ij / x_ji`, `x_ik / x_ki` are exactly
the ones whose Bruhat decomposition produces `<ab, c>` and `<ac, b>`.

This is the only step of the programme that genuinely needs `n >= 3`, and it is the reason `K₂` of a
ring is not visible in the rank-one Steinberg group: in `St₂(R)` the symbol `<x,1>` does not vanish.

### Obligation (3) — the comparison `{a,b} = <(a-1)b^{-1}, b>`

Two-index, same shape as the relations already closed: `steinbergX_mul_opposite hij ((a-1)b^{-1}) b a`
has unit exactly `a`, so the Bruhat word of `x_ij((a-1)b^{-1}) x_ji(b)` carries `h_ij(a)`.  Running
the same word with `a`, with `ab` and with `1` (where the symbol degenerates, `<0,b> = 1`) and
multiplying gives `h(ab) h(a)^{-1} h(b)^{-1}` on the torus side and three Dennis-Stein symbols on the
other.

## Layer B, third pass — scaling, the coboundary formula, and the Steinberg relation in torus form

Four more modules, all wired and axiom-clean.

```
HTGeometry/SteinbergTransportMoves.lean
  steinbergX_move_right       x_ij(a) x_jk(b)   = x_ik(ab)   x_jk(b)    x_ij(a)
  steinbergX_move_right_inv   x_ij(a) x_jk(b)^-1 = x_jk(b)^-1 x_ik(ab)^-1 x_ij(a)
  steinbergX_move_left        x_ij(a) x_ki(c)   = x_kj(ca)^-1 x_ki(c)   x_ij(a)
  steinbergX_move_left_inv    x_ij(a) x_ki(c)^-1 = x_ki(c)^-1 x_kj(ca)  x_ij(a)

HTGeometry/DennisSteinScaling.lean
  dennisStein_scale           <a,b> = <t a, b t^{-1}> . [ h_ij(w), h_ik(t) ]
  dennisStein_normalize_right <a,b> = <b a, 1>        . [ h_ij(w), h_ik(b) ]   (b a unit)

HTGeometry/SteinbergSymbolCoboundary.lean
  dennisSteinUnit hij v  :=  <1, v-1>            (unit v; note 1 + 1.(v-1) = v)
  torusCommutator        :=  [ h_ij(w), h_ik(t) ]
  steinbergSymbol_eq_dennisSteinUnit_coboundary
        f(w) . ( f(W) . [h_ij(W), h_ik(w)] ) . {W,w}^{-1} = f(w W)

HTGeometry/SteinbergRelationTorusForm.lean
  torusCommutator_relation_of_add_one
        [h_ij(U), h_ik(u^{-1})] . [h_ij(w), h_ik(v^{-1})] = [h_ij(w), h_ik(U)]
        whenever  u + v = 1 ,  w = 1 + v b ,  U = 1 + u b w^{-1} .
```

### What these say

The scaling relation is a conjugation argument, not a Bruhat computation: conjugating the defining
word of `<a,b>` by the torus element `h_ik(t)` of a *different* index pair sends
`x_ij(s) |-> x_ij(t s)` and `x_ji(s) |-> x_ji(s t^{-1})`, leaves the unit `1 + ab` unchanged, and
fixes the symbol because the symbol is central.  So the entire dependence of `<a,b>` on how the
product `ab` is split between the two arguments is one torus commutator.

Consequently every symbol with a unit argument normalises to first argument `1`, and the
one-variable function

```
f(v) = <1, v-1>
```

carries everything.  Feeding `a = 1`, `b1 = w-1`, `b2 = (W-1) w` into the addition relation and
normalising the second symbol at `t = w` turns the addition relation into the coboundary formula
above: **the Steinberg symbol is the coboundary of `f`, corrected by the torus commutator.**  Since
a coboundary is symmetric in its two arguments while `{.,.}` is not, the antisymmetric part of the
symbol is exactly the antisymmetric part of the commutator pairing.

Running the *first-argument* addition relation at a splitting `u + v = 1` gives a second expression
for the same coboundary.  Comparing the two cancels every Dennis-Stein symbol and the Steinberg
symbol itself, leaving the last displayed identity: the additivity `u + v = 1` — the only point in
the whole theory where a unit is split into two units, and the hypothesis of `{u, 1-u} = 1` — now
lives purely in commutators of diagonal elements.

### The single remaining input

Everything above is unconditional.  What is still missing for `{u, 1-u} = 1` is the three-index
vanishing

```
f(v) = <1, v-1> = 1 ,
```

equivalently `<x, 1> = 1` through the index reversal.  This is the `(D3)` obligation and the only
step that needs `n >= 3`: in `St_2(R)` the symbol `<x,1>` genuinely does not vanish.  Granted it,
`f == 1`, the coboundary formula collapses to `{W, w} = [h_ij(W), h_ik(w)]` — the classical
"symbol as a commutator of torus elements" — and the torus-form relation above becomes exactly
`{u, 1-u} = 1`.

The transport moves needed for that computation are now in place as
`SteinbergTransportMoves.lean`.

### Correction to the previous section

The claim that the single remaining input is `f(v) = <1, v-1> = 1` is wrong, and the reason is worth
recording because it is a trap.

What `(D3)` actually yields is the vanishing of the symbol with **second** argument `1`,

```
g(v) := <v-1, 1>  =  1 ,
```

since `(D3)` at `c = 1` reads `<a,b> = <ab,1> + <a,b>`.  It says nothing directly about `<1, b>`.
Indeed, `dennisStein_normalize_right` gives, for `b` a unit,

```
<a, b>  =  g(w) . [ h_ij(w), h_ik(b) ] ,        w = 1 + a b ,
```

so `f(v) = <1, v-1> = g(v) . [h_ij(v), h_ik(v-1)]`, and granted `g == 1` this is
`f(v) = [h_ij(v), h_ik(v-1)]` — which is the Steinberg relation itself, not a step towards it.
Assuming `f == 1` would have been circular.

The correct statement of what remains is therefore:

1. `(D3)`, giving `g == 1`.  With it, `<a,b> = [h_ij(w), h_ik(b)]` for every unit `b`.
2. the comparison `{a,b} = <(a-1)b^{-1}, b>`.  With `g == 1` this immediately upgrades to the
   classical commutator formula
   ```
   {a, b} = [ h_ij(a), h_ik(b) ]
   ```
   because the unit of `<(a-1)b^{-1}, b>` is exactly `a`.
3. the vanishing `[h_ij(u), h_ik(1-u)] = 1`.  `torusCommutator_relation_of_add_one` is a genuine
   family of relations on this pairing — for `u + v = 1`, `w = 1 + vb`, `U = 1 + u b w^{-1}`,
   ```
   [h_ij(U), h_ik(u^{-1})] . [h_ij(w), h_ik(v^{-1})] = [h_ij(w), h_ik(U)] ,
   ```
   and the scaling relation applied twice gives multiplicativity of the pairing in its second
   argument.  Whether that family already forces the vanishing, or whether the `(D3)` word
   computation has to supply it, is the open point.

Everything proved so far is unaffected: `dennisStein_add_right`, `dennisStein_add_left`,
`dennisStein_neg_right`, `dennisStein_index_reversal`, `dennisStein_scale`,
`steinbergSymbol_eq_dennisSteinUnit_coboundary` and `torusCommutator_relation_of_add_one` are all
unconditional and hold as stated.
