# The Selberg zeta function of a surface with a small eigenvalue

- **ID:** A120
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM (classical [C])
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.1 "Models and laws of world I", A120;
  `1-in-progress/review-1111-classical-inputs.md` (row A120)
- **Statement:** there is a compact hyperbolic surface `X = Γ\ℍ` whose Selberg zeta function
  `Z(s) = Π_{γ prim} Π_{k≥0} (1 − N(γ)^{−s−k})` has an Euler product on `Re s > 1`, continues to
  an entire function with `Z(1 − s) = Z(s) exp(−|X| ∫_0^{s−½} v tan(πv) dv)`, and has a finite
  nonempty set of zeros off `Re s = ½` in `0 < Re s < 1`: the points `½ ± √(¼ − λ)` for the
  eigenvalues `λ < ¼` of `X`.

## Why a compact surface
For a cofinite group with cusps (the corpus's `Γ_N`, `exists_finiteIndex_small_eigenvalue`) the
functional equation carries the scattering determinant and `Z` vanishes at the resonances, the poles
of `φ(s)` in `Re s < ½`; for congruence groups these are `ρ/2` for the zeros `ρ` of `ζ`: infinitely
many zeros off the line. A finite stratum needs a compact surface. A periodic model (Ihara zeta of a
non-Ramanujan graph, a "virtual curve") has a finite stratum only modulo the period `2πi/log q`.

## Plan (dependency order)
1. **Surface.** An explicit cocompact torsion-free `Γ ⊂ SL(2, ℝ)` with a compact fundamental set
   `K ⊂ ℍ` (every orbit meets `K`) and discreteness. Candidates: the unit group of a maximal order
   of an indefinite division quaternion algebra over `ℚ` (discreteness from integrality,
   compactness from anisotropy + Minkowski), passing to a torsion-free congruence subgroup; or the
   regular-octagon genus-2 group (Poincaré polygon theorem).
2. **Spectral theory.** For compactly supported `C^∞` point-pair profiles `k`, the automorphic kernel
   `K(z, w) = Σ_γ k(u(z, γw))` is continuous on `X × X`; `L_k` is a compact self-adjoint
   (Hilbert–Schmidt) operator on `L²(X)` (corpus: `HTGeometry` Hilbert–Schmidt and trace machinery,
   `RHTower/HyperbolicPointPair` point-pair principle, `RepPointPair*`). Joint eigenbasis of the
   commuting `L_k`; eigenfunctions are Laplace eigenfunctions with `L_k u = h(r) u` (Selberg
   transform); the spectrum `λ_j = ¼ + r_j²` is discrete with `λ_j → ∞`.
3. **Trace formula.** `Σ_j h(r_j) = |X|/(4π) ∫ h(r) r tanh(πr) dr + Σ_{γ} ℓ(γ₀) g(ℓ(γ))/(2 sinh(ℓ(γ)/2))`
   for `g` smooth compactly supported, via `tr L_{k₁} L_{k₂} = ∫_X K(z, z)` and hyperbolic orbital
   integrals; then for the resolvent test functions by approximation.
4. **Small eigenvalue.** A cyclic cover `X_n → X` along a non-separating closed geodesic has
   `λ₁(X_n) → 0` (test function constant on `n − 1` sheets, linear across one collar; min–max).
5. **Selberg zeta.** Euler product convergence on `Re s > 1` (prime geodesic count from the trace
   formula), `Z′/Z(s)/(2s−1) − Z′/Z(a)/(2a−1) = Σ_j [1/(λ_j − s(1−s)) − 1/(λ_j − a(1−a))] + (identity
   terms)`, entire continuation, zeros with multiplicities, the functional equation from the
   symmetry of the identity term.

## Step 1 in detail: an explicit cocompact group (paper)
`B = (2, 3)_ℚ` is a division algebra: `x₀² − 2x₁² − 3x₂² + 6x₃² = 0` in integers forces `3 | x₀, x₁`
(squares mod 3), then `3 | x₂, x₃`: infinite descent. `ι(i) = diag(√2, −√2)`, `ι(j) = [[0,3],[1,0]]`
embeds `B ⊗ ℝ ≅ M₂(ℝ)` with `nrd = det`. `O = ℤ⟨1, i, j, ij⟩`, `Γ = O¹ = {x ∈ O : nrd x = 1}`.
- *Discrete*: `ι(O)` is a lattice in `M₂(ℝ) ≅ ℝ⁴`.
- *Cocompact* (no Mahler): for `z = g·i`, Minkowski gives `x ∈ O ∖ 0` with `‖g⁻¹ι(x)‖² ≤ C`
  (Frobenius norm; `covol(g⁻¹ι(O)) = covol(ι(O))`). Anisotropy gives `1 ≤ |nrd x| ≤ C/2`. For each
  `n`, the elements of norm `n` fall into finitely many `O¹`-orbits under left multiplication:
  `x′ ≡ x mod nO` and `nrd x = nrd x′ = n` give `x′x⁻¹ = x′x̄/n ∈ O` of norm 1. With a finite set `R`
  of representatives, `x = γ r`, so `‖g⁻¹γ‖ ≤ C max_R ‖r⁻¹‖`, i.e. `d(γ·i, z) ≤ R₀`: every point is
  within a fixed distance of the orbit `Γ·i`, so the Dirichlet domain at `i` is compact.
- *Torsion-free subgroup*: `Γ(5) = {γ ≡ 1 mod 5O}`; a torsion element has `trd ∈ {0, ±1, ±2}`,
  `≡ 2 mod 5` forces `trd = 2`, so `γ − 1` is nilpotent, hence `0` in a division algebra.
- *Crux*: a nonzero homomorphism `Γ(5) → ℤ` (needed for the cyclic covers with `λ₁ → 0`). Candidates:
  Eichler periods of a nonzero weight-2 form (`γ ↦ ∫_{z₀}^{γz₀} f dz`; zero periods force `f = 0`),
  or `H₁ = Γ^{ab}` with `χ(X) < 0` from Gauss–Bonnet. Given `χ̃`, an equivariant Lipschitz
  `θ(z) = Σ_γ ψ(γ⁻¹z) χ̃(γ)` (Γ-partition of unity `ψ`) gives the test function `e^{2πiθ/n}` on
  `Γ_n = ker(χ̃ mod n)`, orthogonal to constants, with Rayleigh quotient `O(1/n²)`.

## Status
Not started in Lean. The vendored `DifferentialGeometry.Analysis.Spectral.Scalar` (built oleans:
`EigenBasis`, `Spectrum`, `Enumeration`) gives the eigenbasis and discrete spectrum of the Laplacian
on a compact boundaryless Riemannian manifold; using it needs `Γ\ℍ` as a smooth manifold with the
hyperbolic metric. Corpus inputs located: point-pair mean value and integral principle
(`HyperbolicRotationMean`, `HyperbolicPointPair`), Selberg transforms and the test-field eigenvalue
criterion for `Γ_N` (`RepPointPairSmallEigenCriterion`, `NonvacuousSmallEigenvalue`), the Mayer
determinant and geodesic Euler product for the modular surface (`GaussMayerGeodesicProduct`), trace
and Hilbert–Schmidt infrastructure in `HTGeometry`.

## Log
- 2026-11-13 — created; route analysis (compact surface needed; cusped and periodic models fail the
  finite-stratum requirement); plan written.
