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
