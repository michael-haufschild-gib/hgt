# General data, cusp channel and spin two on the modular horizon

- **ID:** modular-horizon-general-data-cusp-spin-two
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** extends `3-formalized/modular-horizon-full-field-ringdown.md`
- **Statement:** On the massless topological AdS₄ black hole with horizon `PSL₂(ℤ)\ℍ`: every compact pulse gives an exact solution by the method of images, with echo identity and ringdown. Every `f ∈ L²` of the horizon is a constant plus a limit of pulse fields plus a cuspidal part, and the wave evolution is a strongly continuous cosine family, contractive off the constants. Cusp eigenfunctions vanish at the cusp, have `λ ≥ ¼`, and give undamped horizon modes at rate exactly `D`. Each zero is a nonzero gravitational quasinormal mode, each pulse carries an exact `SL₂(ℤ)`-covariant vacuum perturbation of the metric in closed form, in the vector and in the scalar sector, and each component of the metric rings down in the modes of the zeros.

## Goal
Replace Gaussian amplitudes by general data, add the discrete channel, and pass from the conformal scalar to the metric. Not an RH route.

## Gates
- [x] 0 → 1 in-progress: corpus read (Schläfli shift, deck spectral theorem, Selberg at level one, vector and scalar stream Einstein tables, joint smoothness of the Fourier–Bessel family)
- [x] 1 → 2 fully-proven: paper proofs below
- [x] 2 → 3 formalized: modules below, each checked with `lake --old env lean` with no messages

## Lean certificate
Folder `formal/GaloisForLFunctions/BlackHoleRingdown/`, wired into the umbrella `BlackHoleRingdown.lean`.

| Claim | Module | Theorems |
|---|---|---|
| I.1 Sharp decay in the order | `TheSharpDecayOfTheBesselKernel` | `norm_modifiedBesselKOrder_le_shifted`, `exists_norm_modifiedBesselKOrder_sharp` |
| I.2 Polynomial bounds for `E` | `TheSharpBoundsOfTheEisensteinFunction`, `ThePolynomialGrowthOfTheEisensteinFunction`, `TheEisensteinFunctionOnContours` | `exists_weightedTail_jets_le_sharp`, `exists_eisenstein_jets_line_le_poly`, `exists_jets_goodHeight`, `exists_jets_left_line` |
| I.3 Pulse amplitude | `ThePulseAmplitude` | `CompactPulse.rapidAmplitude`, `amplitude_D`, `eq_integral_amplitude_line`, `integral_mul_cexp_eq` |
| I.4 Image field | `TheImageFieldOfAPulse`, `TheLiftOfAnyModularWave` | `isModularWave_imageField`, `imageField_smul`, `neumannWave_metric_wave`, `dirichletWave_metric_wave` |
| I.5 Bridge | `TheSpectrumOfTheImageField` | `imageField_eq_packet`, `pulseField_eq_packet`, `isModularWave_pulseField` |
| I.6 Echo, wavefront | `TheEchoesOfAPulse` | `setIntegral_pulsePacket`, `pulseReflected_eq`, `pulseEcho_eq`, `pulseEcho_eq_zero`, `pulseReflected_before_wavefront`, `setIntegral_imageField` |
| I.7 Ringdown | `TheContourPackage`, `TheRingdownOfAPulse` | `contour_expansion`, `contourData_pulse`, `pulse_ringdown`, `exists_pulseMode`, `exists_pulse_exciting_zero`, `neumannWave_pulse_ringdown` |
| I.8 General `L²` data | `TheVolumeOfTheModularHorizon`, `TheEisensteinChannel`, `TheCosineFamilyOfTheHorizon`, `TheGeneralHorizonData` | `volume_fd_eq`, `incEis_pulse`, `CompactPulse.hMellin_pulseF`, `inner_pulseL2_ones`, `eisTransformE_onesE`, `eisTransform_even`, `integral_even_pulseField_le`, `channelCos_pulse`, `channelCos_add_sub`, `continuous_channelCos`, `exists_horizon_decomposition`, `norm_channel_add_cusp_le` |
| II.1–2 Decay and reality | `TheCuspFormsVanishAtTheCusp` | `tendsto_component_atImInfty`, `toMaassCuspEigenform`, `lam_ne_zero`, `one_quarter_le_cuspEigenBasis` |
| II.3–4 Modes, cosine family | `TheCuspChannel` | `isModularWave_cuspMode`, `norm_neumann_cuspMode`, `norm_dirichlet_cuspMode`, `integral_cuspMode`, `exists_cuspEigenBasis_modes`, `cuspCosine_add_sub`, `continuous_cuspCosine`, `norm_cuspCosine_le`, `hasDerivAt_repr_cuspCosine` |
| III.1 Vector modes | `TheVectorModesOfTheMetric`, `TheGravitationalModesOfTheZeros` | `vectorMetricField_einstein`, `vectorMetricField_vacuum`, `gP_master`, `fN_master` |
| III.2–3 Each zero | `TheGravitationalModesOfTheZeros` | `numeratorField_eigen`, `vector_mode_neumann`, `vector_mode_dirichlet`, `scalar_mode`, `numerator_at_zero`, `gravitational_mode_of_zero`, `norm_time_factor` |
| III.4 Metric of a pulse | `TheLinearityOfTheEinsteinOperator`, `TheMetricOfARow`, `TheMetricOfAPulse`, `TheScalarWaveOfAPulse` | `cosmological_jetLin`, `vac_sum`, `rowMetric_vacuum`, `imageMetric_vacuum`, `imageT_profile`, `imageR_profile`, `pulseMetric_vacuum`, `scalarRow_vacuum`, `scalarMetric_vacuum` |
| III.5 Metric ringdown | `TheMetricRingdown`, `TheScalarWaveOfAPulse` | `differentiableAt_of_second_bound`, `contourData_cov`, `imageCov_eq_covPacket`, `imageT_ringdown`, `imageR_ringdown`, `imageT_mode`, `imageR_mode`, `exists_metric_excitation`, `scalarEntry_ringdown`, `scalarEntry_mode` |
| III.6 Covariance | `TheWaveOnTheQuotient` | `covariant_of_invariant`, `imageCov_covariant`, `imageT_covariant`, `imageR_covariant`, `scalarEntry_smul`, `scalarEntry_AA_smul`, `eisensteinNumerator_smul`, `covNum_covariant`, `add_radialPhase_eq` |

## Claims and paper proofs

### Part I: general horizon data

**I.1 Sharp decay.** For `x > 0`, `ν = η + iξ`, `0 ≤ θ < π/2`: `‖K_x(ν)‖ ≤ e^{-|ξ|θ} K_{x cos θ}(η)`, by shifting the Schläfli line to `Im t = θ`. Take `θ = π/2 - 1/(1+|ξ|)`.

**I.2 Polynomial bounds.** The factor `e^{-π|ξ|/2}` of I.1 cancels `|1/ξ(1+2iξ)| ≲ (1+|ξ|)^N e^{π|ξ|/2}`, so `E` and its jets are polynomially bounded on `Re u = 0`, `Re u = -A`, `Re u = c ≥ ½`, and on horizontal segments at the good heights.

**I.3–I.5 Pulses.** For `h ∈ C_c^∞`, `a(w) = (2π)⁻¹∫h e^{-iwS}dS` is entire and rapidly decreasing on strips. `Π_h = ½Σ y_γ^{½} h(τ + log y_γ)` is a locally finite sum, and each row solves the wave equation because `y_γ` is harmonic with `y²|∇y_γ|² = y_γ²`. Inserting Fourier inversion row by row and moving the line from `Re u = 1` to `Re u = 0`, with residue at `u = ½`, gives `Π_h = 𝓕_h + 6a(-i/2)e^{τ/2}`.

**I.6 Echo.** Fubini on `Re w = 1` gives `h ∗ K = ∫_{Re w = 1} a(-iw) e^{wT} φ(½+w)`, and the shift to `Re w = 0` gives `𝒮_h = h ∗ K - 6a(-i/2) e^{T/2}`. `K = 0` on `τ ≤ 0` gives an exact wavefront. The horocycle mean of `Π_h` is `√Y (h(τ + log Y) + (h ∗ K)(τ - log Y))`, with no mean term.

**I.7 Ringdown.** The contour package needs only analyticity of the numerator on `Re u ≤ 0` and integrable bounds on the two lines and at the good heights, which I.2 and the rapid decay of `a` provide.

**I.8 General data.** The substitution `y = e^S` gives `ψ̂_τ(s) = 2π e^{(s-½)τ} a(-i(s-½))` for `ψ_τ(y) = √y h(τ + log y)`. Unfolding and `vol 𝒟 = π/3` give `⟨Π_h, 𝟙⟩ = 6a(-i/2) e^{τ/2} ‖𝟙‖²`, so `𝓕_h ⊥ 𝟙`. The corpus Parseval reads `‖E‖² = π⁻¹‖T E‖² + κ|⟨E, 𝟙⟩|²` on the Eisenstein space. With Cauchy–Schwarz, `(1 - κ‖𝟙‖²) e^{τ} ≲ ‖T_τ‖²`, bounded in `τ`, while `(1 - κ‖𝟙‖²)‖𝟙‖² = π⁻¹‖T𝟙‖² ≥ 0`. Hence `T𝟙 = 0`, and `T` is an isometry up to `π` off the constants. `T_τ(t) = 2π(e^{itτ}a(t)𝟙 + e^{-itτ}a(-t)Φ𝟙)`, so `½(T_τ + T_{-τ}) = cos(tτ) T_0` and the even part is contractive. Level two gives the integral inequality on `𝒟`, which holds at every level. Pulses form a vector space and the bound holds on each, so `𝓕_h(0) ↦ ½(𝓕_h(τ) + 𝓕_h(-τ))` extends to a contraction of the closure. Smooth height profiles are `h(S) = e^{-S/2}ψ(e^S)`, and mollification reaches every generator of the Eisenstein space.

### Part II: the cusp channel

**II.1 Decay.** `h U = L_φ U`. Along a horocycle `U` is periodic with mean zero, so its primitive `V` is bounded by `ℓ(y) = ∫₀¹|U|`, and `∫ g U = -∫ g' V`. For `g = φ(u)`, `u = ((x-x₀)²+(y-y₀)²)/(4y₀y)`, `|g'| ≲ X/(y₀y)` on `|x-x₀| ≤ X = √(4Ry₀y)`, so `|∫ g U| ≲ R ℓ(y)`. The kernel vanishes for `y ≤ y₀/(4R+3)`. So `|U(z)| ≲ ∫_{y₀/(4R+3)}^∞ y⁻²ℓ(y) dy → 0`.

**II.2 Reality.** So `U` is a Maass cusp form and `no_exceptional_of_principal_le` excludes `(0, ¼)`. At `λ = 0`, `L_φ U = U` for a positive unit profile, ergodicity makes `U` constant, and decay makes it zero.

**II.3–4.** `e^{∓itτ}U` solves the modular wave equation, the lifts have `ω = ±t - iD`, and the horocycle mean vanishes. `C(τ)` is diagonal on the Hilbert basis.

### Part III: spin two

**III.1 Vector modes.** `V = (∂_yY, -∂_xY)` is divergence-free, and the angular slots of the corpus table are `∂_y(y²ΔY)`, `-∂_x(y²ΔY)`, so they act by `λ`. `cosmological_component` reduces the Einstein tensor to the master expression and its `r` derivative. With `γ(r) = ½log(r²-1) - log 2r`, `γ' = 1/(r(r²-1))`, the functions `e^{wγ}` and `r e^{wγ}` solve the master equation for `λ = (w+1)(w+2)` and `λ = w(w+1)`.

**III.2–3 Zeros.** `N(u; ·)` is smooth by the corpus angular series and `y²ΔN = (u²-¼)N`. So `w = u-½`, `w = u-3/2` give vector modes and `s = u-3/2` a scalar mode through `field_residual_zero`. At a zero the term `y^{½+p}` is absent. `N(p; ·)` is not constant because `p² ≠ ¼`, so the perturbation is not zero.

**III.4 Metric of a pulse.** For a row, `S = t + γ + log s`, `σ = (∂_y s, -∂_x s)`, `F = r²-1`: `h_{ti} = σ_i(F m(S) + m'(S))`, `h_{ri} = σ_i (r/F) m'(S)`. For `m = a e^{wS}` this is the separated mode of `Y = a s^{w+1}/(w+1)`. The linearized Einstein operator is linear in the jet, and the two-jet at a point depends only on the values of `m` and its first three derivatives at one value of `S`. Four exponentials realize these values by Vandermonde, so the row is vacuum for every `C³` function `m`. Sum over rows, locally finite. For `m = e^{-S/2}(½h + h')`: `h_{ti} = e^{-τ/2}((F-½)𝓥_i + ∂_τ𝓥_i)`, `h_{ri} = (r/F)e^{-τ/2}(∂_τ𝓥_i - ½𝓥_i)`, `𝓥 = (∂_yΠ_h, -∂_xΠ_h)`.

In the scalar sector the corpus matrix `M_s` is polynomial in `s`, and `s_γ² e^{sS}` is the corpus field of `s_γ^{s+2}`. Five exponentials give vacuum for `H = e^{-3τ/2} M_D Π_h`, `D = ∂_τ - 3/2`.

**III.5 Metric ringdown.** At fixed `r, z` each block is a prefactor times the rotated gradient of the field of `g = c h + h'`: `c = F-½` temporal, `c = -½` radial. `N_x, N_y` are holomorphic in `u` as locally uniform limits of difference quotients, by the bound on second jets. The contour package gives the expansion, with top coefficient `(F-½+p) a N` and `(p-½) a N`, the separated mode of `p`. In the scalar sector each entry is `e^{-3τ/2}Π_g`, the mean gives `e^{-τ}`, and the amplitude is `A + Bs + Cs²` at `s = p - 3/2`.

**III.6 Covariance.** Differentiating `F∘g = F` for conformal `g` gives `V(z) = (dg)ᵀV(gz)`. `N(u; ·)` is invariant by the identity theorem from `Re u = 0`.

## Status of the parts
Not formalized:
- Mode sums converge only along the good heights.
- The Weyl asymptotic. Existence, discreteness and the lower bound `N(Λ) ≥ cΛ` are proved (`bhr-the-cusp-forms-of-the-modular-horizon-exist.md`, `bhr-the-cusp-spectrum-is-discrete.md`, `bhr-a-weyl-lower-bound-for-the-cusp-spectrum.md`).
- The metric of a pulse is not extended to the `L²` closure: exact vacuum perturbations are for compact pulses and separated modes.
- Regularity of the metric perturbations across `r = 1` is not treated: the radial block has `1/F` in these coordinates, and no gauge or ingoing form was proved.
- The scalar sector is treated at `s = u - 3/2`, the corpus fundamental reconstruction, and not at `s = u - ½`.

## No-go closure (mandatory when falsified)
Not applicable: no route was retired.

## Log
