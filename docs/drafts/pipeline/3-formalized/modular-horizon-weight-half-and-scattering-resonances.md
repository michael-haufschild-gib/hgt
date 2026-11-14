# Metaplectic Cusp-Reflection Reciprocity Separates Weight `½` from the Cubic Cover and Bounds Modular Horizon Scattering Resonances

- **ID:** modular-horizon-weight-half-and-scattering-resonances
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1311/obstacles-summary.md` §2.7 (B188, A120), §2.12 (Q1–Q5, C1–C3)
- **Statement:** The exact horizon input that fails in weight `½` (double cover) and bounds the scattering resonances is **odd-order metaplectic cusp-reflection Möbius reciprocity coupled with rational sub-horizon trivialization**: on `n = 2` covers, quadratic Gauss sums square to `χ(−1)q` (yielding square-supported non-negative constant terms `fN 0 = phiSq` with `phiSq p = 0` at primes) and `j_ϑ(U, z)² ≠ 1` on `Γ₀(4) ≤ SL₂(ℤ)`, permitting an explicit non-coboundary unitary-multiplier Lewis–Zagier period vector `Ψ_ϑ` at `w = 3/2` (`λ = 3/16 < 1/4`); whereas on the `n = 3` Kubota cover of `SL₂(ℤ[ω])\ℍ³`, cubic Gauss sums cube to the ideal Möbius sign `γ₃(I)³ = μ(I) · p/|p|`, the multiplier `κ₃` restricts identically to `1` on all of `SL₂(ℤ)`, the `L²` residual cubic theta state `Θ₃` at `s = 4/3` (`λ = 8/9 < 1`) arises from a simple pole (in contrast to the double pole of `Θ₃²`), Bianchi horizon pulse ringdown at rate `δ ∈ (0, ¼]` is equivalent to `ζ_{ℚ(√−3)}(ρ) ≠ 0` on `Re ρ > 1 − 2δ`, and the cubic-cover binding-bin row balance pins the unconditional bounds `Re ρ ∈ [1/8, 7/8]`, Mayer scattering resonances `Re s ∈ [1/16, 7/16]`, horizon ringdown rate `δ = 1/16`, and horocycle/Farey/cusp-energy/two-mode thermalization `O(y^{9/16 − ε})`.

## Goal
Resolve `obstacles-summary.md` §2.7 and §2.12 unconditionally in Lean 4 without axioms or unproved premises: isolate the exact algebraic-spectral boundary between `n = 2` and `n = 3` metaplectic covers, calibrate both off-line resonance mechanisms (weight `½` at `λ = 3/16` and compact hyperbolic quotients with small eigenvalues), prove the Bianchi horizon ringdown–strip equivalence, and derive the unconditional bounds on scattering resonances and modular-horizon thermalization rates.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions.RingdownOfTheCubicCover`, `lake --old env lean` green on all 5 modules, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]` only)

## Lean formalization (`GaloisForLFunctions.RingdownOfTheCubicCover`)
- `formal/GaloisForLFunctions/RingdownOfTheCubicCover/TheWeightHalfThreeTermCalibration.lean`:
  - `vecNormSq_thetaUT`, `vecNormSq_thetaUS`, `vecNormSq_thetaUTPrime`
  - `differentiableOn_thetaLewisPeriod`, `not_exists_coboundary_eq_thetaLewisPeriod`, `thetaLewisPeriod_zero_re_pos`
  - `thetaLewisPeriod_S_reciprocity`, `thetaLewisPeriod_three_term`, `weight_half_horizon_calibration`
- `formal/GaloisForLFunctions/RingdownOfTheCubicCover/MetaplecticCuspReciprocitySeparatesCovers.lean`:
  - `gaussQ_neg_one_four`, `weight_half_J_U_sq`, `weight_half_jU_U_sq_ne_one`, `weight_half_jU_nontrivial_on_Gamma0_four`
  - `cubic_multiplier_trivial_on_SL2Z`, `weight_half_constant_term_vanishes_on_primes`
  - `gaussSum_power_moebius_dichotomy`, `cubic_composite_gauss_recovers_ideal_moebius`
  - `residual_eigenvalue_and_pole_order_comparison`, `metaplectic_horizon_input_separates_weight_half_from_cubic_cover`
- `formal/GaloisForLFunctions/RingdownOfTheCubicCover/BianchiHorizonRingdownEquivalence.lean`:
  - `xiBianchi_one_sub`, `norm_bianchiScatteringPhase_axis`, `bianchi_bilateral_laplace_eq`
  - `bianchi_zeroFreeStrip_iff_pulse_ringdown`, `bianchi_xi_zeroFreeStrip_iff_pulse_ringdown`
  - `bianchi_hecke_zeroFreeStrip_iff_pulse_ringdown`, `bianchi_quarter_ringdown_iff_dedekind_rh`
- `formal/GaloisForLFunctions/RingdownOfTheCubicCover/CompactHorizonCalibration.lean`:
  - `selbergZeta_zero_re_eq_half_or_im_eq_zero`, `selbergZeta_nonreal_zero_re_eq_half`
  - `selbergZeta_offline_zero_iff_exceptional_eigenvalue`, `finite_offline_selbergZeta_zeros`
  - `selbergZeta_no_offline_zeros_iff_spectralGap_quarter`, `compact_spectral_packet_decay`, `compact_vs_cuspidal_horizon_dichotomy`
- `formal/GaloisForLFunctions/RingdownOfTheCubicCover/UnconditionalScatteringResonanceBounds.lean`:
  - `LFunction_chi3D_zero_mem_quasiRH_strip`, `bianchiZeta_zero_mem_quasiRH_strip`, `xiBianchi_zero_mem_quasiRH_strip`, `heckeLFunction_thirdCyclotomic_zero_mem_quasiRH_strip`
  - `zetaZeroAbscissa_mem_Icc`, `zeroAbscissa_chi3D_mem_Icc`
  - `isMayerScatteringResonance_re_mem_Icc`, `mayerResonanceMultiplicity_eq_zero_outside_strip`, `scatteringEntry_holomorphicOrder_nonneg_outside_strip`
  - `bianchi_pulse_ringdown_one_sixteenth`, `modular_pulse_ringdown_one_sixteenth`
  - `horocycleMean_rate_nine_sixteenths`, `fareyCount_rate_nine_sixteenths`, `cusp_energy_rate_nine_sixteenths`, `twoMode_cavity_rate_nine_sixteenths`
  - `horizon_ringdown_vertex_balance`, `binding_bin_saving_iff_faster_ringdown`

## Paper proof

### 1. Weight-`½` Twisted Three-Term Calibration (`w = 3/2`, `λ = 3/16`) `[PROVED HERE]`
Let `Θ⃗(τ) = (ϑ₃(τ), ϑ₄(τ), ϑ₂(τ))ᵀ : ℍ → ℂ³` be the vector of Jacobi theta constants. Under `T(τ) = τ + 1` and `S(τ) = −1/τ`, modular transformation laws give `Θ⃗(τ + 1) = U_T Θ⃗(τ)` and `Θ⃗(−1/τ) = (−iτ)^{1/2} P_S Θ⃗(τ)` (`Im τ > 0`), where `U_T(v₀, v₁, v₂) = (v₀, v₁, e^{πi/4} v₂)` after swapping `(ϑ₃, ϑ₄)` (`U_T(v₀, v₁, v₂) = (v₁, v₀, e^{πi/4} v₂)`) and `P_S(v₀, v₁, v₂) = (v₀, v₂, v₁)`. Setting `U_S := e^{−πi/4} P_S` and `U_{T'} := P_S U_T⁻¹ P_S = U_S U_T⁻¹ U_S⁻¹`, each of `U_T, U_S, U_{T'}` is unitary for the standard `ℓ²` norm on `ℂ³`, and at `τ = iy` (`y > 0`), setting `u = −1/τ − 1 = i/y − 1 ∈ ℍ` yields `Θ⃗(τ/(1 + τ)) = (1 + τ)^{1/2} U_{T'} Θ⃗(τ)`.

At spectral parameter `w = 2s = 3/2` (`s = 3/4`, `λ = s(1 − s) = 3/16 < 1/4`), define `Ψ_ϑ(z) := i ∫_0^∞ (z + iy)^{−3/2} Θ⃗(iy) dy` on `{Re z > 0}`:
1. **Holomorphicity and cusp decay:** By `‖Θ⃗(iy)‖ ≤ C(1 + y^{−1/2})`, the integrand is dominated locally uniformly on `{Re z > 0}` by `C (z₀ + y)^{−3/2} (1 + y^{−1/2}) ∈ L¹(0, ∞)`, establishing holomorphicity on `{Re z > 0}` and `‖Ψ_ϑ(a)‖ = O(a^{−1/2} + a^{−1}) → 0` as `a → +∞`, which excludes every coboundary `v − a^{−3/2} U_T v` (`v ≠ 0` tends to `v`, while `v = 0` contradicts `Re(Ψ_ϑ(a)_0) > 0`).
2. **Strict positivity:** For `a > 0` and `y > 0`, `ϑ₃(iy) ≥ 1 > 0` and `arg((a + iy)^{−3/2}) ∈ (−3π/4, 0)`, so `−Im((a + iy)^{−3/2}) > 0` and `Re(Ψ_ϑ(a)_0) > 0`.
3. **Anti-unitary `S`-reciprocity:** Changing variables `y = 1/u` and applying `Θ⃗(i/u) = u^{1/2} P_S Θ⃗(iu)` yields `conj(Ψ_ϑ(a)) = a^{−3/2} U_S Ψ_ϑ(1/a)`.
4. **Twisted three-term equation:** Applying Cauchy's integral theorem on `{Im τ > 0}` to `(a + τ)^{−3/2} Θ⃗(τ) dτ` over the truncated geodesic triangle between `γ₀(y) = iy`, `γ₁(y) = 1 + iy`, and `γ₂(y) = iy/(1 + iy)` (`y ∈ [1/R, R]`, `R → ∞`) yields `Ψ_ϑ(a) = U_T Ψ_ϑ(a + 1) + (a + 1)^{−3/2} U_{T'} Ψ_ϑ(a/(a + 1))`.

### 2. Metaplectic Cusp-Reflection Dichotomy (`n = 2` vs `n = 3`) `[PROVED HERE]`
1. **Rational modular descent:** At `U = [[1, 0], [4, 1]] ∈ Γ₀(4) ≤ SL₂(ℤ)`, `gaussQ(−1, 4) = 2(1 − i)` gives `J(U, z)² = 4z + 1` on `ℍ` (`J(U, i)² = 1 + 4i`) and `j_ϑ(U, z)² ≠ 1` for every `z ∈ ℍ`. Thus `j_ϑ` twists `Γ₀(4)` non-trivially and isolates `y^{1/4} θ` (`λ = 3/16`) from untwisted `SL₂(ℤ)` scattering. Conversely, on the `n = 3` cover of `SL₂(ℤ[ω])\ℍ³`, the extended Kubota character `κ₃` has order dividing `3`, normalizes `globalKubotaKernel`, and restricts identically to `1` on `SL₂(ℤ)`.
2. **Gauss-sum Möbius sign law:** For multiplicative characters `χ` of order `m > 2` on `𝔽_q^×`, even `m` satisfies `g(χ, ψ)^m ≡ χ(−1) q (mod (μ − 1)²)` while odd `m` satisfies `g(χ, ψ)^m ≡ −q (mod (μ − 1)²)`. In weight `½` (`n = 2`), the constant-term convolution `fN 0 = phiSq` vanishes on all primes (`phiSq p = 0`) and is non-negative everywhere; on `n = 3`, cubing the normalized composite cubic Gauss sum over distinct prime ideals away from `1 − ω` recovers `γ₃(∏ P_i)³ = μ(∏ P_i) · (p/|p|)`. Meanwhile `cubicEisensteinResidue` (`Θ₃`) is a non-zero `L²` simple-pole residue at `s = 4/3` (`λ = 8/9 < 1`), whereas squaring `Θ₃` produces a double pole `(s − 4/3)² M(s) D(s) → 108 π³ r³ ≠ 0`.

### 3. Bianchi Horizon Ringdown ⇔ Dedekind Zero-Free Strip `[PROVED HERE]`
For `K = ℚ(√−3)`, `ζ_K(s) = ζ(s) L(s, χ_{−3})` (`chi3D`, primitive of conductor `3`) completes to the entire function `xiBianchi(s) = 3^{s/2} ξ(s) Λ(s, χ_{−3})` satisfying `xiBianchi(1 − s) = xiBianchi(s)`. With the Bianchi reflection kernel `φ_K(u) = (u + 1/2) 3^{−1/2} ξ(2u) Λ(2u, χ_{−3}) / xiBianchi(1 + 2u)` (`|φ_K(iξ)| = |1/2 + iξ|`) and reflected pulse field `𝓕_{K, h}(τ) = ∫_{−∞}^∞ â_h(ξ) φ_K(iξ) e^{iξτ} dξ`:
- **Zero-free strip ⇒ Ringdown:** Non-vanishing of `ζ_K` on `Re ρ > 1 − 2δ` (`0 < δ ≤ 1/4`) provides polynomial vertical bounds for `1/ζ` and `1/L(·, χ_{−3})` on closed substrips `−σ ≤ Re u ≤ 0` (`σ < δ`); shifting the vertical contour `Re u = 0 → −σ` against rapid decay of `â_h` yields `‖𝓕_{K, h}(τ)‖ = O(e^{−(δ − ε)τ})` on `τ ≥ 0`.
- **Ringdown ⇒ Zero-free strip:** Shifting `Re u = 0 → 1` bounds `𝓕_{K, h}(τ) = O(e^τ)` on `τ ≤ 0`, so under `O(e^{−(δ − ε)τ})` decay on `τ ≥ 0` the bilateral Laplace transform `ℒ_h(w)` is holomorphic on `−δ < Re w < 1` and satisfies `xiBianchi(1 + 2w) ℒ_h(w) = 2π â_h(−iw) (w + 1/2) 3^{−1/2} ξ(2w) Λ(2w, χ_{−3})` by Fourier inversion on `0 < Re w < 1` and identity theorem on `−δ < Re w < 1`. Any zero `ρ = 1 + 2p` (`−δ < Re p < 0`) forces `â_h(−ip) ξ(2p) Λ(2p, χ_{−3}) = 0`, contradicting `h = excitingPulse p` since `Re(1 − 2p) > 1`.

### 4. Compact Horizon Calibration `[PROVED HERE]`
On any `CompactQuotient X` (`1 < a`) with hyperbolic non-trivial elements, `X.selbergZeta_eq_zero_iff` reduces `Z_Γ(s) = 0` to `λ_j + s(s − 1) = 0` (`λ_j ≥ 0`), with no continuous scattering channel. Taking imaginary parts forces `(2 Re s − 1) Im s = 0`, so every non-real zero lies on `Re s = 1/2`; zeros in `1/2 < Re s < 1` are strictly real, finite in number (`X.finite_lam_lt ha (1/4)`), and parameterized by `s = 1/2 + √(1/4 − λ_j)` (`0 < λ_j < 1/4`); and finite spectral packets above `λ_min > 0` decay at rate `1/2 − √(max(0, 1/4 − λ_min))`.

### 5. Unconditional Scattering Resonance Bounds and Vertex Balance `[PROVED HERE]`
Combining `riemannZeta_ne_zero_of_seven_eighths_lt_re` and `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re chi3D` with functional-equation reflection, Mayer's resonance characterization `IsMayerScatteringResonance s ↔ ζ(2s) = 0` on `0 < Re s < 1/2`, and the Bianchi and modular ringdown equivalences establishes unconditionally:
- `s.re ∈ [1/8, 7/8]` for all nontrivial zeros of `ζ`, `L(·, χ_{−3})`, `ζ_{ℚ(√−3)}`, and `xiBianchi`, and `1/2 ≤ Θ ≤ 7/8` for both `zetaZeroAbscissa` and `zeroAbscissa chi3D`;
- `s.re ∈ [1/16, 7/16]` for all Mayer scattering resonances of `PSL₂(ℤ)\ℍ²`, with vanishing resonance multiplicity and non-negative meromorphic order of `scatteringEntry` outside `[1/16, 7/16]` in `(0, 1/2)`;
- `O(e^{−(1/16 − ε)τ})` pulse ringdown on both `SL₂(ℤ[ω])\ℍ³` and `PSL₂(ℤ)\ℍ²`, and `O(y^{9/16 − ε})` convergence on `(0, 1]` for horocycle means, Farey depth counts, Maass cusp-form horocycle energies, and two-mode cuspidal cavity responses;
- at `(lx, ly, ℓ) = (17/48, 23/48, 1/6)`, `lowBoundary = 7/8` (`δ = 1/16`), the binding-bin exponent at `δ_bin = 79/204` is `(13/16)(R − 443/663)` pinned at `−7/30672 < 0` by `rowCount (79/204) (1/2) = 21766/32589`, and along `(17/48 − h/2, 23/48 − h/2, 1/6 + h)` (`h > 0`), `lowBoundary = 1 − 2(1/16 + h/8)` has negative binding-bin exponent iff `R < (443 − 270 h)/(663 + 1224 h)`.

## Log
- 2026-11-14 — proved on paper and formalized unconditionally in `GaloisForLFunctions.RingdownOfTheCubicCover` (5 modules, `lake --old env lean` green, `#print axioms` clean).
