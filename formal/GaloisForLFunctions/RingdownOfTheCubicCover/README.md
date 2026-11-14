# Ringdown of the Cubic Cover (RCC)

Namespace `GaloisForLFunctions.RingdownOfTheCubicCover`; umbrella
`RingdownOfTheCubicCover.lean`.

## 1. Mathematical summary

This folder resolves unconditionally which horizon input fails on the `n = 2` metaplectic double
cover (weight `½` on `Γ₀(4) ≤ SL₂(ℤ)`) and holds on the `n = 3` cubic cover of the Bianchi
horizon `SL₂(ℤ[ω])\ℍ³`, calibrates both off-line resonance mechanisms (weight-`½` multiplier twists
and compact hyperbolic quotients), proves the exact equivalence between Bianchi horizon pulse
ringdown and Dedekind zero-free strips, and derives the unconditional bounds on scattering
resonances and modular-horizon thermalization rates.

The separating horizon input has two coupled parts:
1. **Rational modular descent (`SL₂(ℤ)` triviality of the cover multiplier)**:
   - On `n = 2` (weight `½`), at `U = [[1, 0], [4, 1]] ∈ Γ₀(4) ≤ SL₂(ℤ)`, the quadratic Gauss sum
     `G(-1; 4) = 2(1 - i)` gives `J(U, z)² = 4z + 1` (`J(U, i)² = 1 + 4i`) and `(j_ϑ(U, z))² ≠ 1`
     at every `z ∈ ℍ`. Thus `j_ϑ` is non-trivial on `Γ₀(4)`, decoupling the exceptional residual
     eigenfunction `y^{1/4} θ` (`λ = 3/16 < 1/4`, `s = 3/4`) from untwisted `SL₂(ℤ)` scattering and
     admitting an explicit non-coboundary unitary-multiplier solution of the three-term Lewis–Zagier
     functional equation at `w = 2s = 3/2`.
   - On `n = 3` (cubic cover of `SL₂(ℤ[ω])\ℍ³`), the extended cubic Kubota character `κ₃` on
     `Γ(3) · SL₂(ℤ)` takes values in `μ₃` and restricts identically to `1` on all of `SL₂(ℤ)`.
2. **Odd-order Gauss-sum Möbius sign reciprocity**:
   - For even cover degree `n` (`n = 2`), `g(χ)^n` carries the character parity `χ(-1)` rather than
     `-1`, and the weight-`½` constant-term Dirichlet convolution `fN 0 = phiSq` vanishes at every
     prime modulus (`phiSq p = 0`) and is non-negative everywhere.
   - For odd cover degree `n = 3`, `γ₃(I)³ = μ(I) · (p / |p|)` recovers the exact ideal Möbius sign
     up to the Grossencharacter angular unit, while the `L²` residual cubic theta eigenfunction at
     `s = 4/3` (`λ = 8/9 < 1`) couples into the base channel via the non-vanishing double pole
     `(s - 4/3)² M(s) D(s) → 108 π³ r³ ≠ 0`.

## 2. Modules and main theorems

| Module | Main declarations | Mathematical content |
|---|---|---|
| `TheWeightHalfThreeTermCalibration.lean` | `vecNormSq_thetaUT`, `vecNormSq_thetaUS`, `vecNormSq_thetaUTPrime`, `differentiableOn_thetaLewisPeriod`, `not_exists_coboundary_eq_thetaLewisPeriod`, `thetaLewisPeriod_zero_re_pos`, `thetaLewisPeriod_S_reciprocity`, `thetaLewisPeriod_three_term`, `weight_half_horizon_calibration` | Explicit holomorphic vector `Ψ_ϑ : {Re z > 0} → ℂ³` built from `(ϑ₃, ϑ₄, ϑ₂)` solving the unitary-multiplier three-term Lewis–Zagier equation `Ψ_ϑ(a) = U_T Ψ_ϑ(a + 1) + (a + 1)^{-3/2} U_{T'} Ψ_ϑ(a / (a + 1))` with anti-unitary `S`-reciprocity `conj(Ψ_ϑ(a)) = a^{-3/2} U_S Ψ_ϑ(1/a)` at `w = 3/2` (`s = 3/4`, `λ = 3/16 < 1/4`), vanishing at `+∞` (hence non-coboundary) and strictly positive in `Re(Ψ_ϑ(a)_0)`. |
| `MetaplecticCuspReciprocitySeparatesCovers.lean` | `gaussQ_neg_one_four`, `weight_half_J_U_sq`, `weight_half_jU_U_sq_ne_one`, `weight_half_jU_nontrivial_on_Gamma0_four`, `cubic_multiplier_trivial_on_SL2Z`, `weight_half_constant_term_vanishes_on_primes`, `gaussSum_power_moebius_dichotomy`, `cubic_composite_gauss_recovers_ideal_moebius`, `residual_eigenvalue_and_pole_order_comparison`, `metaplectic_horizon_input_separates_weight_half_from_cubic_cover` | Exact separation between `n = 2` (`j_ϑ(U, z)² ≠ 1` on `Γ₀(4)`, `phiSq p = 0`, `phiSq c ≥ 0`, `g(χ)^m ≡ χ(-1) #F` for even `m`, exceptional `λ = 3/16` with `Ψ_ϑ` at `w = 3/2`) and `n = 3` (`κ₃|_{SL₂(ℤ)} = 1`, `γ₃(I)³ = μ(I) · unit`, `L²` residual `Θ₃` at `λ = 8/9 < 1` with double pole `(s - 4/3)² Λ(s) → 108 π³ r³ ≠ 0`). |
| `BianchiHorizonRingdownEquivalence.lean` | `xiBianchi_one_sub`, `norm_bianchiScatteringPhase_axis`, `bianchi_bilateral_laplace_eq`, `bianchi_zeroFreeStrip_iff_pulse_ringdown`, `bianchi_xi_zeroFreeStrip_iff_pulse_ringdown`, `bianchi_hecke_zeroFreeStrip_iff_pulse_ringdown`, `bianchi_quarter_ringdown_iff_dedekind_rh` | On `SL₂(ℤ[ω])\ℍ³` (`K = ℚ(√−3)`), `O(e^{-(δ - ε)τ})` late-time ringdown of compact pulses scattered off `φ_K(w) = Λ_K(2w) / Λ_K(1 + 2w)` (`0 < δ ≤ 1/4`) is unconditionally equivalent to the zero-free strip `Re ρ ≤ 1 - 2δ` for `ζ_K(s) = ζ(s) L(s, χ₋₃)` (and `heckeLFunction (trivialModulus K) 1`); `δ = 1/4` is equivalent to GRH for `ζ_K`. |
| `CompactHorizonCalibration.lean` | `selbergZeta_zero_re_eq_half_or_im_eq_zero`, `selbergZeta_nonreal_zero_re_eq_half`, `selbergZeta_offline_zero_iff_exceptional_eigenvalue`, `finite_offline_selbergZeta_zeros`, `selbergZeta_no_offline_zeros_iff_spectralGap_quarter`, `compact_spectral_packet_decay`, `compact_vs_cuspidal_horizon_dichotomy` | On any compact hyperbolic surface `X : CompactQuotient`, continuous Eisenstein scattering is absent: every Selberg zero satisfies `Re s = 1/2 ∨ Im s = 0` (zero non-real off-line zeros), zeros in `1/2 < Re s < 1` are finite in number and biject with `0 < λ_j < 1/4`, `1/2 < Re s < 1` is zero-free iff `λ_j ≥ 1/4` for all positive eigenvalues, and discrete wavepackets decay at the spectral-gap rate `1/2 - √(max(0, 1/4 - λ_min))`. |
| `UnconditionalScatteringResonanceBounds.lean` | `LFunction_chi3D_zero_mem_quasiRH_strip`, `bianchiZeta_zero_mem_quasiRH_strip`, `xiBianchi_zero_mem_quasiRH_strip`, `zetaZeroAbscissa_mem_Icc`, `zeroAbscissa_chi3D_mem_Icc`, `isMayerScatteringResonance_re_mem_Icc`, `mayerResonanceMultiplicity_eq_zero_outside_strip`, `scatteringEntry_holomorphicOrder_nonneg_outside_strip`, `bianchi_pulse_ringdown_one_sixteenth`, `modular_pulse_ringdown_one_sixteenth`, `horocycleMean_rate_nine_sixteenths`, `fareyCount_rate_nine_sixteenths`, `cusp_energy_rate_nine_sixteenths`, `twoMode_cavity_rate_nine_sixteenths`, `horizon_ringdown_vertex_balance`, `binding_bin_saving_iff_faster_ringdown` | Unconditional confinement of nontrivial zeros of `ζ`, `L(s, χ₋₃)`, and `ζ_{ℚ(√−3)}` to `Re ρ ∈ [1/8, 7/8]` (`1/2 ≤ Θ ≤ 7/8`), Mayer scattering resonances of `PSL₂(ℤ)\ℍ²` to `Re s ∈ [1/16, 7/16]`, Bianchi and modular pulse ringdown at `O(e^{-(1/16 - ε)τ})`, horocycle / Farey / cusp-energy / two-mode cavity thermalization at `O(y^{9/16 - ε})`, and exact vertex balance at `(17/48, 23/48, 1/6)` (`δ = 1/16`, `R = 21766/32589 < 443/663`) together with the iff threshold `R < (443 - 270 h) / (663 + 1224 h)` for `δ(h) = 1/16 + h/8 > 1/16`. |
| `EternalBianchiBoundaryDictionaryAndWardObstruction.lean` | `chi3EchoSeries_eq_chi3EchoGate`, `hasProd_chi3EchoGate`, `hasProd_bianchiPrimeGate`, `bianchiPrimeProduct_mul_archimedean_eq_scatteringPhase`, `bianchiRetardedCorrelator_isPole_iff`, `bianchiWightmanRL_isPole_iff`, `dedekind_rh_iff_bianchiWightmanRL_quarter_strip`, `bianchiWightmanRL_quarter_strip_implies_riemannHypothesis`, `bianchiWightmanRL_analyticOnNhd_one_sixteenth`, `bianchiDeformedReflectedField_decay`, `not_bianchiDeformedReflectedField_decay_gt`, `bianchi_universal_causal_ringdown_infimum_zero` | Independent rational-prime cycle gate Euler factorization on `SL₂(ℤ[ω])\ℍ³`, complete multiplicity-preserving single- and two-boundary (`G_{R,K}` and `G_{RL,K}` on `0 < |Im ν| < 1/2`) singularity dictionary for `ζ(s) L(s, χ₋₃)`, equivalence of quarter-strip `G_{RL,K}` analyticity with Dedekind RH, unconditional `1/16` strip analyticity, and collapse of the universal causal ringdown infimum to `0` under retarded prime-`2` Schur deformation (`1/2 < α < 1`). |
