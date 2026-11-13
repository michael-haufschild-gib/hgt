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

## Route (no Laplacian)
The spectrum is read off the resolvent operators alone. For real `s > 1` let
`k_s(u) = (1/4π) ∫_u^∞ ρ(w)^{2s−1} (w(1+w))^{−½} (w−u)^{−½} dw`, `ρ(w) = √(1+w) − √w` (the Green
function `Q_{s−1}(1+2u)/2π`, defined as an inverse Abel transform). Then
- *Abel transform:* `𝒜k_s(x) = e^{−(s−½)|x|}/(2s−1)` (Fubini and `∫_v^w (w−u)^{−½}(u−v)^{−½} du = π`).
- *Resolvent identity:* `k_s ⋆ k_a = (k_a − k_s)/(s(s−1) − a(a−1))` as point-pair kernels: the Abel
  transform turns `⋆` on `ℍ` into convolution on `ℝ` (horocycle slices), exponentials convolve
  explicitly, and `𝒜` is injective (`𝒜𝒜k(v) = π∫_v^∞ k`).
- *Operators:* on a cocompact free `Γ`, `T_s = L_{k_s}` is Hilbert–Schmidt on `L²(F)`, self-adjoint,
  `T_s T_a = (T_a − T_s)/(s(s−1) − a(a−1))`. An eigenvector of `T_a` with eigenvalue `μ ≠ 0` has
  `T_s e = e/(λ + s(s−1))`, `λ := 1/μ − a(a−1)`; boundedness of every `T_s` (`s > 1`) forces `λ ≥ 0`.
- *Trace:* `K_a − K_s` (`s > a`) is continuous and positive, so Mercer gives
  `Σ_j (h_a − h_s)(λ_j) = vol·(k_a − k_s)(0) + Σ_{[γ]} ℓ₀ (𝒜k_a − 𝒜k_s)(ℓ)/(2 sinh(ℓ/2))`, i.e.
  `Φ(s)/(2s−1) = Φ(a)/(2a−1) + vol·(k_a−k_s)(0) − Σ_j (h_a − h_s)(λ_j)`, `Φ = Z′/Z`,
  `(k_a − k_s)(0) = (1/2π) Σ_k (1/(s+k) − 1/(a+k))`.
- *Zeta:* the right side continues `Φ` meromorphically with simple poles of residue `m_j` at
  `s(s−1) = −λ_j`; `Z = s(s−1)·Π_{λ_j>0}(1 + s(s−1)/λ_j)e^{−s(s−1)/λ_j}·e^{H(s)}` on `Re s > 0`,
  `H` a primitive of the holomorphic rest; `Z(1−s)/Z(s) = exp(vol ∫_0^{s−½} v tan πv dv)` from
  `Σ_k (1/(s+k) − 1/(1−s+k)) = π cot πs`.
- *Small eigenvalue:* on `Γ_n = {χ ∈ 2nℤ}` the test field `e^{2πiθ/2n}` has
  `⟨T_a F, F⟩ ≥ (m_a − C/n²)‖F‖²`, `m_a = 1/(a(a−1))`; the top eigenvalue of `T_a` on `1^⊥` then
  exceeds `1/(a(a−1)+¼)`, i.e. `λ < ¼`; `k_a > 0` gives ergodicity, so `λ > 0`.

## Modules (folder `CompactHyperbolicSurfaces/`)
1. cocompact free groups: counting `#{γ : u(z,γw) ≤ R} ≤ C(1+R)`, fundamental set, unfolding;
2. the quaternion group `Γ(23) ⊂ O¹`, `O = {[[α, 3β],[β′, α′]] : α, β ∈ ℤ[√2]}`: discrete, cocompact
   (Minkowski), free;
3. walls and `χ : Γ(23) → ℤ` with `χ(u₀) = ±2`;
4. resolvent kernels and Abel calculus; 5. operators, resolvent identity, spectrum;
6. Mercer trace; 7. conjugacy classes, orbital integrals, trace formula; 8. Selberg zeta;
9. small eigenvalue on `Γ_n`; 10. assembly.

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
Lean (folder `CompactHyperbolicSurfaces/`, compiled):
- `HorocyclicSlices`: Abel transform `abelL`, slices, weighted masses, convolution slices, ball volumes.
- `CocompactGroups`: `IsCocompactFree`, orbit counting `exists_card_le`, fundamental domain
  `exists_isFundamentalDomain`.
- `ResolventKernels`, `ResolventKernelBounds`: `resKernel`, `abelL_resKernel`, decay `u^{−s}`, local
  `u^{−¼}`, difference kernel `diffKernel` (continuous, `abelL_diffKernel`).
- `ConvolutionProfiles`: radiality of `convK`, `abelL_convProfile`, Abel inversion `ae_eq_of_abelL_eq`.
- `ResolventIdentity`: `convK_resKernel_ae` (`k_s ⋆ k_a = D_{a,s}/(s(s−1) − a(a−1))` a.e.).
- `AutomorphicKernels`: `autK`, unfolding, `exists_tsum_rpow_le`, `continuous_autR`.
- `ResolventOperators`, `ResolventOperatorIdentity`, `ResolventCompactness`: `CompactQuotient`,
  `resOp` (self-adjoint, `‖T_s‖ ≤ 1/(s(s−1))`), `resOp_comp` (`T_sT_a = c⁻¹(T_a − T_s)`),
  `resOp_comm`, `isCompactOperator_resOp`.
Next: spectral parametrization, Mercer trace, trace formula, zeta,
explicit group and walls, small eigenvalue.

## Log
- 2026-11-13 — created; route analysis (compact surface needed; cusped and periodic models fail the
  finite-stratum requirement); plan written.
