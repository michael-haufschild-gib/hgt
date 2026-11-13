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

## Status
Not started in Lean. Corpus inputs located: point-pair mean value and integral principle
(`HyperbolicRotationMean`, `HyperbolicPointPair`), Selberg transforms and the test-field eigenvalue
criterion for `Γ_N` (`RepPointPairSmallEigenCriterion`, `NonvacuousSmallEigenvalue`), the Mayer
determinant and geodesic Euler product for the modular surface (`GaussMayerGeodesicProduct`), trace
and Hilbert–Schmidt infrastructure in `HTGeometry`.

## Log
- 2026-11-13 — created; route analysis (compact surface needed; cusped and periodic models fail the
  finite-stratum requirement); plan written.
