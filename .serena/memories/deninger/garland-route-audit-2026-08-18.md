# Garland route audit (2026-08-18) — the selected route to `K_2(O_K) ⊗ ℚ = 0` does not close

Read this before adding any brick to `garland-formalization-programme`.

## The finding

The programme card conflates two different theorems of Garland.

- **Garland 1971**, *A finiteness theorem for `K₂` of a number field*, Ann. of Math. 94 — the paper
  that actually proves `K₂(𝒪_F)` finite. Its method is **archimedean**: Riemannian geometry and
  harmonic forms, establishing `H²(SL_n(𝔬), ℝ) = 0` for `n > 6`.
- **Garland 1973**, *p-adic curvature…*, Ann. of Math. 97 — the combinatorial building/spectral-gap
  theorem that Layer C formalizes. Its hypothesis is that `Γ` is a **cocompact (uniform)** lattice in
  the p-adic group. Casselman removed the residue-field-size restriction, not cocompactness.

An `S`-arithmetic lattice is uniform **iff** the ambient group is anisotropic over the base field.
`SL_n` (`n ≥ 2`) is isotropic over every number field, so `SL_n(𝒪_S)` is **non-uniform**: on the
Bruhat–Tits building it has finitely many cell orbits but **infinite** stabilizers (conjugates of
`SL_n(𝒪)`). The equivariant descent is then the isotropy spectral sequence
`E₁^{p,q} = ⊕_σ H^q(Γ_σ, ℝ) ⇒ H^{p+q}(Γ, ℝ)`, whose `q = 1, 2` rows are the very groups the argument
is meant to kill. **Circular.** No choice of `S` rescues it.

## What survives and keeps its value

`HTGeometry/GarlandLocalization.lean` (localization identities, `harmonic_eq_zero`,
`cocycle_eq_coboundary`), `WeightedGraphSpectralGap.lean`, `WeightedComplexLink.lean`,
`IncidenceDesignBound.lean`, `IncidenceWeightedComplex.lean`,
`FiniteProjectivePlaneSpectralGap.lean` — these are correct unconditional theorems and are, as far as
I can tell, the first formalization of Garland's 1973 method. They are simply not sufficient for the
arithmetic target. Layers D1–D3 (Bruhat–Tits building, contractibility, links) and C5 (equivariant
descent) should **not** be built in the service of this card.

All of Layer B (Steinberg group, `K₂`, centrality, perfectness, Weyl/torus calculus, the symbol) is
route-independent and stays: every route needs Matsumoto to convert between the Milnor tame kernel
that Layer A consumes and the `K₂` of the ring the cohomological input produces.

## The sound routes and their true cost

Borel's stable cohomology (≡ Garland 1971); Quillen finite generation + Borel rank; Soulé +
Quillen–Lichtenbaum; Bader–Sauer higher-Kazhdan restriction. All analytic, all multi-year. A
literature sweep (Aug 2026) found **no** elementary/algebraic proof of rank-zero for `K₂(𝒪_F)`.
Sum-of-squares certificates for cohomological Laplacians are not uniform in `F` and are excluded by
the project's no-computation rule.

## Consequence for the blocked card

`deninger-algebraic-cyclotomic-milnor-amplitude` stays at stage 2, and it has **two** independent
research-scale blockers, not one: (a) `(1)` needs Borel/Garland-1971; (b) `(4)` needs `E∞`/CDGA
homotopy theory and derived base change, which mathlib does not have at all.
