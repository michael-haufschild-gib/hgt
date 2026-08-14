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
