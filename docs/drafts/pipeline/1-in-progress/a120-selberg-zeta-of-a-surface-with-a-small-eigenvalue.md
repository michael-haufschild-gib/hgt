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

## Remaining route (paper)
Notation: `X = Γ\ℍ` a `CompactQuotient` with `|tr γ| > 2` for `γ ≠ 1` (true in `Γ(N)`: `tr = 2x₀`,
`x₀ ≡ 1 mod N`, `|x₀| ≤ 1` forces `x = 1` by anisotropy of the pure part). `D = k_a − k_s`, `1 < a < s`.
1. *Hyperbolic elements.* `γ = ±σ dil(N) σ⁻¹`, `N > 1`; `ℓ(γ) = log N`. Commuting with `dil(N)`, `N ≠ 1`,
   means diagonal. The centralizer `Z(γ)` embeds in `ℝ` by `δ ↦ log M_δ` (`σ⁻¹δσ = ±dil(M_δ)`),
   injectively (`−1 ∉ Γ`), with finitely many values in bounded sets (`finite_near`, `d(σi, δσi) = |log M_δ|`),
   so `Z(γ) = ⟨γ₀⟩`. Primitive = generates its centralizer. Classes `≠ 1` ↔ (primitive class, `m ≥ 1`),
   `[γ₀] , m ↦ [γ₀^m]`, `ℓ = mℓ₀`.
2. *Class orbital integral.* `A = σ·{1 ≤ |z| < e^{ℓ₀}}` meets each `Z(γ)`-orbit exactly once. Fibres of
   `δ ↦ δ⁻¹γδ` are cosets `Z(γ)δ₁`, so `Σ_{γ'∈[γ]} ∫_F D(u(z,γ'z)) = Σ_δ ∫_F 1_A(δz) D(u(δz,γδz)) = ∫_A D(u(w,γw))
   = ℓ₀ 𝒜D(ℓ)/(2 sinh(ℓ/2))` (`RHTower.lintegral_smul_annulus_pairU_conj`, `t = η/(2 sinh(ℓ/2))`).
3. *Trace formula.* `hasSum_nu` + Tonelli: `Σ_j ν_j = |F|·D(0) + Φ(a)/(2a−1) − Φ(s)/(2s−1)`,
   `Φ(s) = Σ_{[γ]≠1} ℓ₀ e^{−sℓ}/(1 − e^{−ℓ})`, `D(0) = (1/2π)Σ_k (1/(a+k) − 1/(s+k))`
   (substitution `w = ((1/x − x)/2)²`: `dw/(w√(1+w)) = −4dx/(1−x²)`). Positivity gives `Φ(a) < ∞` for `a > 1`.
4. *Euler product.* `Z_E(s) = Π_{prim p, k ≥ 0} (1 − e^{−(s+k)ℓ_p})`, `Re s > 1`, nonvanishing,
   `logDeriv Z_E = Φ` (`logDeriv_tprod_eq_tsum`, rearrangement through the bijection of 1).
5. *Continuation to `Re s > 0`.* Identity theorem on `Re s > 1`:
   `Φ(s) = E'/E(s) + R(s)`, `E = Π_j (1 + w_j) e^{−w_j}`, `w_j = (s(s−1) − c)/(λ_j + c)`, `c = a(a−1)`
   (`Σ 1/(λ_j+c)² < ∞` from `Σν_j < ∞`); `R(s) = (2s−1)[Φ(a)/(2a−1) + (|F|/2π) Σ_k (1/(a+k) − 1/(s+k))]`
   with explicit primitive `G = A(s²−s) + (|F|/2π) Σ_k g_k`, `g_k = (s²−s)/(a+k) − 2s + (2k+1) Log(s+k) − g_k(a)`.
   `Z = κ E e^{G}` on `Re s > 0`, `= Z_E` on `Re s > 1`.
6. *Functional equation* on `0 < Re s < 1`: `E(1−s) = E(s)`; `R(s) + R(1−s) = |F| v tan πv`, `v = s − ½`
   (cotangent series), so `Z(1−s) = Z(s) exp(−|F| ∫_0^{s−½} v tan πv dv)`.
7. *Zeros off the line* in the strip: `λ_j + s(s−1) = 0`, `s ∉ ½ + iℝ` ⇒ `s = ½ ± √(¼ − λ_j)`, `0 < λ_j < ¼`;
   finitely many (compact `T_a`).
8. *Walls.* `W = {w ∈ O : trd w = 0, nrd w = −2, w ≡ i mod 5}`, `H_w(z) = c|z|² − 2a·Re z − b` for
   `ι(w) = [[a,b],[c,−a]]`; `H_{gMg⁻¹}(gz) = H_M(z)/|cz+d|²`; a wall separating `z, z'` vanishes on the
   segment `[z, z']`, where `(a − cx)² + c²y² = 2` bounds its entries, so finitely many walls separate points
   of a compact set. `θ(z) = Σ_w (1[H_w(z)>0] − 1[H_w(z₀)>0])` (measurable, bounded increments over bounded
   distances), `χ(γ) = θ(γz₀)` a homomorphism `Γ(5) → ℤ`. On `|z|² = 3`, `H_w = −2√2(3x₃ + x₁ Re z)`; a
   sign change between `z₀ = i√3` and `ηz₀` (`η = 26 + 15j = (2+√3)³`, `Re ηz₀ = 2340/1351`) forces
   `x₂ = 0`, `x₁² − 3x₃² = 1`, `|x₁| ≤ 1351` (Pell), and mod 5 leaves `26i − 15ij`, `1351i − 780ij`:
   `χ(η) = −2`.
9. *Small eigenvalue.* `Γ_n = {γ ∈ Γ(5) : n ∣ χ(γ)}`, `n` odd (cocompact: `ηᵏδ` with `2k ≡ χ(δ) mod n`).
   `F = e^{2πiθ/n}`: `Γ_n`-invariant, unimodular, `⟨F, 1⟩ = 0` (`η` normalizes `Γ_n`, `F∘η = e^{−4πi/n}F`).
   Dirichlet form `∬ K_a|f(y) − f(z)|² = 2‖f‖²/c − 2Re⟨f, T_a f⟩`; for `F` it is
   `≤ |F|(4 tail_a(U) + (2πL_U/n)²/c)` (`|ΔF| ≤ 2` always, `≤ 2πL_U/n` for `u ≤ U`). Choose `U`, then `n`:
   `Re⟨F, T_aF⟩ > ‖F‖²/(c + ¼)`; the constrained norm of `T_a` on `1^⊥` is an eigenvalue `μ > 1/(c + ¼)`,
   `λ = 1/μ − c < ¼`, and `λ ≠ 0` by ergodicity (`k_a > 0`).
10. *Open: entire continuation.* `Z = κE e^{G}`, `e^{G}` has the factor `Π_k (s+k)^{(2k+1)|F|/2π}`: `Z`
   extends to an entire function iff `|F|/2π ∈ ℤ` (Gauss–Bonnet, `|F| = 4π(g − 1)`). The Lean statement
   is on `Re s > 0`. Candidate routes: (a) Dirichlet polygon, vertex cycles with angle sum `2π`, fan
   triangulation and `area(T) = π − Σ angles`, giving `|F| = 2π(E − V − 1)`; (b) weight-`m` Bergman
   projections: `rank = ∫_F K_m(z,z) = (m−1)|F|/4π` (hyperbolic orbital integrals of holomorphic kernels
   vanish), `m = 4, 6` give `|F|/4π ∈ ℤ`.

## Status
Lean (folder `CompactHyperbolicSurfaces/`, umbrella `CompactHyperbolicSurfaces.lean`, wired into
`MainTheorems.lean`; all compiled, headline axioms `propext, Classical.choice, Quot.sound`):
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
- `ResolventSpectrum`: eigenbasis `specVec`, `spectralParam ≥ 0`, `resOp_specVec_eq`
  (`T_s e_j = e_j/(λ_j + s(s−1))`), completeness `resOp_eq_zero_of_orthogonal`.
- `MercerRepresentatives`, `MercerBound`, `MercerTrace`: continuous Γ-invariant representatives,
  row energy and Bessel bound `exists_sum_nu_specRep_le`, Mercer `diffKer_eq_mercerKer`, trace
  `hasSum_nu` (`Σ_j ν_j = ∫_F K(z, z)`), `Countable SpecIndex`.
- `QuaternionOrder`, `QuaternionGroup`, `QuaternionCocompact` (Step 1 for every `N ≥ 3`, not only
  `N = 5`): anisotropy `eq_zero_of_nrd_eq_zero`, `congGroup N`, `finite_dist_congGroup`,
  `eq_one_of_smul_eq_congGroup`, Minkowski `exists_short` (covolume `det_latBasis = 24`),
  `exists_congGroup_mul_of_quatKey_eq`, `isCocompactFree_congGroup`,
  `exists_compactQuotient_congGroup`.

- `HyperbolicElements`, `Centralizers`, `ClassOrbitalIntegrals`, `PrimitiveClasses`: `γ = ±σ dil σ⁻¹`,
  cyclic centralizers, class orbital integrals, primitive classes `PClass × ℕ ≃ NClass`.
- `DiffKernelDiagonal`, `TraceFormula`, `LengthSeries`: `diffKernel_zero`, `trace_formula`,
  `trace_formula_lengthSeries`.
- `SelbergEulerProduct`, `SpectralProduct`, `PsiSeries`, `SelbergZeta`: `hasProd_eulerZeta`,
  `logDeriv_eulerZeta`, `specProd`, `selbergZeta` holomorphic on `Re s > 0`, `eulerZeta_eq_selbergZeta`,
  `selbergZeta_one_sub`, `selbergZeta_eq_zero_iff`.
- `QuaternionWalls`, `WallCrossing`: `two_lt_abs_trSL_congGroup`, `hermForm_conj_smul`,
  `finite_separating`, `wallCount_smul`, `wallHom`, `exists_abs_wallCount_sub_le_of_dist`,
  `measurable_wallCount`, `wall_cross_classify`, `wallHom_eta` (`χ(η) = −2`).
- `DirichletEnergy`: `resOp_oneL`, `integral_energy`, `exists_eq_smul_oneL` (ergodicity),
  `exists_spectralParam_mem_Ioo`.
- `CyclicCovers`: `coverGroup`, `isCocompactFree_coverGroup`, `integral_testF_eq_zero`,
  `integral_energy_testL_le`, `exists_coverGroup_small_eigenvalue`.
- `SmallEigenvalueZeta`: `offLine_zeros_eq`, headline `exists_selbergZeta_small_eigenvalue` (Euler product,
  holomorphy on `Re s > 0`, functional equation, zeros off the line in the strip = `{½ ± √(¼ − λ_j)}`,
  finite and nonempty).

Open: entire continuation (step 10, Gauss–Bonnet).

## Log
- 2026-11-13 — created; route analysis (compact surface needed; cusped and periodic models fail the
  finite-stratum requirement); plan written.
- 2026-11-13 — Mercer trace and Step 1 (explicit cocompact free group) formalized; paused by user.
- 2026-11-14 — steps 1–9 formalized; headline `exists_selbergZeta_small_eigenvalue`; open: step 10.
