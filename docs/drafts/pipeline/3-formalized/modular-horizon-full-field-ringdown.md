# Full-field ringdown on the modular horizon

- **ID:** modular-horizon-full-field-ringdown
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** follow-up to `3-formalized/ringdown-reads-the-horizon-spectrum.md`: its "Not formalized" items on the AdS black hole with modular horizon
- **Statement:** On the massless topological AdS₄ black hole with horizon `PSL₂(ℤ)\ℍ`, a Gaussian Eisenstein wave packet lifts to exact solutions of the conformally coupled wave equation, smooth across the future horizon. Its reflected constant term is the pulse convolved with the echo train minus its mean growth. Its late-time field is a uniformly convergent sum of damped modes, one per zeta zero, on the minus branch only, plus a remainder decaying faster than every exponential.

## Goal
Theorems about an actual solution of the wave equation on the metric, in place of the paper sketch "the full field carries the causal symbol". Not an RH route: universal damping stays RH-equivalent.

## Gates
- [x] 0 → 1 in-progress: corpus read (`lineModel`, `D4BMBackground`, residue theorem, inner bound, good heights)
- [x] 1 → 2 fully-proven: paper proofs below
- [x] 2 → 3 formalized: modules below, each checked with `lake --old env lean` with no messages

## Lean certificate
Folder `formal/GaloisForLFunctions/BlackHoleRingdown/`, wired into the umbrella `BlackHoleRingdown.lean`.

| Claim | Module | Theorems |
|---|---|---|
| 1 Metric reduction | `TheExactLiftOfTheModularWave`, `TheMetricOfTheModularHorizon` | `blackHoleWaveOperator_conformalScalar`, `metricWaveOperator_eq`, `volumeDensity_sq`, `conformalCoupling_eq` |
| 2 Exact lift | `TheExactLiftOfTheModularWave` | `neumannLift_modular_wave`, `dirichletLift_modular_wave`, `dirichletLift_boundary`, `neumannLift_normalDerivative` |
| 3 Vertical bounds | `TheVerticalBoundsOfTheEisensteinTail` | `norm_modifiedBesselKOrder_le_re`, `exists_weightedTail_jets_le` |
| 4 Packet | `TheNormalizedEisensteinFunction`, `TheEisensteinWavePacket`, `TheMetricOfTheModularHorizon` | `eisenstein_eigen`, `normalizedEisenstein_smul`, `wavePacket_wave`, `wavePacket_smul`, `neumannField_metric_wave`, `dirichletField_metric_wave`, `neumannField_smul`, `dirichletField_smul` |
| 5 Constant term | `TheEisensteinWavePacket` | `setIntegral_wavePacket` |
| 6 Echo identity | `TheConvolutionOfThePulseWithTheEchoes`, `TheReflectedSignalIsTheEchoTrain` | `incomingPulse_eq_closedForm`, `integral_pulse_mul_echoKernel_eq_line`, `integral_pulse_mul_exp`, `norm_xi_two_mul_le`, `integral_echoIntegrand_shift`, `reflectedSignal_eq_echoConvolution`, `setIntegral_wavePacket_echo` |
| 7 Ringdown expansion | `TheInverseXiContour`, `TheRingdownExpansion`, `TheModesOfTheRingdown` | `tendsto_sum_laurentCoeff_inverseXiQuotient`, `ringdown_expansion`, `exists_ringdownMode`, `laurentCoeff_packet_of_simple`, `exists_eisensteinNumerator_ne_zero`, `modeFrequency_eq_qnmMinus`, `qnmPlus_ne_modeFrequency`, `modeRate_zeroCopy`, `neumannField_ringdown`, `dirichletField_ringdown` |
| 8 Uniformity | `TheExpansionIsUniformAtLateTimes` | `exists_uniform_bound`, `ringdown_expansion_uniform` |
| 9 Horizon smoothness | `TheFieldIsSmoothAcrossTheHorizon` | `contDiff_wavePacket_time`, `tanh_tortoise`, `conformalScalar_neumannProfile_eq_ingoing`, `conformalScalar_dirichletProfile_eq_ingoing`, `contDiffAt_neumannIngoing`, `contDiffAt_dirichletIngoing` |
| 10 Transfer function | `TheFieldCarriesTheCausalSymbol` | `integral_cexp_mul_incomingPulse`, `integral_cexp_mul_echoResponse`, `retardedTransform_echoResponse`, `setIntegral_neumannField`, `causalSymbol_modeFrequency_isPole` |

The statements carry no hypotheses beyond the parameter ranges (`ε > 0`, `Y > 0`, `r > 1`, `A ≥ 1`, `Re w > ½`). `laurentCoeff_packet_of_simple` assumes a simple zero; it only evaluates the case `n = 0` of `exists_ringdownMode`, which covers every multiplicity.

## Claims
1. **Metric reduction.** The Laplace–Beltrami operator of `D4BMBackground.metric`, written through its inverse and determinant, plus `-R/6 = 2` (`R = -12`), applied to `F = ψ(t, x_*(r), x, y)/r`, equals `(r f)⁻¹ (ψ_{**} - ψ_tt + sech²x_* y²(ψ_xx + ψ_yy))`.
2. **Exact lift.** If `𝓕_ττ = Δ𝓕 + 𝓕/4` on the horizon and `τ = t - log(2 cosh x_*)`, then `e^{-τ/2}𝓕` and `tanh(x_*) e^{-3τ/2}𝓕` solve the radial equation of claim 1, with Neumann and Dirichlet data at the AdS boundary.
3. **Vertical bounds.** The Whittaker tail and its jets are bounded uniformly in `Im u`, locally uniformly in `(x, Y)`, for bounded `Re u`.
4. **Packet.** For `a(ξ) = exp(-ε(ξ-ξ₀)²)`, every `ε > 0`, the function `𝓕(τ, z) = ∫ a(ξ) E(z, ½+iξ) e^{iξτ} dξ` is `SL₂(ℤ)`-invariant and solves the modular wave equation. Its lifts solve the conformally coupled wave equation of the metric on `r > 1`.
5. **Constant term.** `∫₀¹ 𝓕 dx = Y^{1/2}(g(τ + log Y) + 𝒮(τ - log Y))`, with `g` the pulse and `𝒮(T) = ∫ a φ(½+iξ) e^{iξT} dξ`.
6. **Echo identity.** `𝒮(T) = ∫ g(T-τ)(K(τ) - (3/π) e^{τ/2}) dτ`.
7. **Ringdown expansion.** There is `R` with `‖R(τ)‖ ≤ C_A e^{-Aτ}` for every `A ≥ 1` and `𝓕 - R = 2π lim_k Σ_{|γ|<T_k} Res_{u=(ρ-1)/2}`. A zero of multiplicity `n+1` contributes `e^{pτ}` times a polynomial in `τ` of degree at most `n`, whose top coefficient vanishes exactly where `N(p; x, Y)` does. For each `Y` there is a point of the horocycle where `N(p; x, Y) ≠ 0`. After a lift of decay `D` the frequency is `ω = i(p-D)`, the minus branch, at rate `D + (1-β)/2` and frequency `-γ/2`. A plus-branch frequency is never a mode frequency.
8. **Uniformity.** The limit in claim 7 is uniform on `τ ≥ 0`, so at every precision finitely many modes and `R` approximate `𝓕` at all late times.
9. **Horizon smoothness.** In `(v, r)`, `v = t + x_*`, both fields extend `C^∞` to every `r > 0`, through `r = 1`. Here `τ = v - log(2r/(r+1))` and `tanh x_* = -1/r`.
10. **Transfer function.** `∫ e^{iωT} e^{-DT} (g∗K)(T) dT = 2π a(-iw) (s/(s-1)) 𝒞_D(ω)` for `w = D - iω`, `s = w + ½`, `Re w > ½`, and `∫₀¹ Φ dx = (e^{-τ/2}/r) √Y (g(τ + log Y) + (g∗K)(τ - log Y)) - 6a(-i/2)/r`. Every mode frequency is a pole of the causal symbol, for every overtone.

## Paper proofs

**Claim 1.** With `f = r²-1`, `∂_r x_* = 1/f`, `F = ψ/r`: `r² f ∂_r F = r ψ_* - f ψ`, whose `r` derivative is `r ψ_{**}/f - 2rψ`. Dividing by `r²` and adding the time and angular terms and `2F = 2ψ/r` cancels the `ψ/r` terms. The determinant is `-(r²/y²)²` and the inverse metric is diagonal, which gives the coefficients of the operator.

**Claim 2.** Put `T = tanh x`, `S = 1-T²`, `H' = T`, so `T' = S`, `S' = -2TS`. For `Ψ = e^{-τ/2}𝓕`: `Ψ_x = -TΨ_τ`, `Ψ_xx = -SΨ_τ + T²Ψ_ττ`, so `Ψ_tt - Ψ_xx = S(Ψ_ττ + Ψ_τ) = S e^{-τ/2}(𝓕_ττ - 𝓕/4)`. For `Ψ = T A`, `A = e^{-3τ/2}𝓕`: `Ψ_tt - Ψ_xx = TS(A_ττ + 3A_τ + 2A) = TS e^{-3τ/2}(𝓕_ττ - 𝓕/4)`.

**Claim 3.** `|cosh((η+iξ)t)| ≤ cosh(ηt)` gives `‖K_s(ν)‖ ≤ K_s(Re ν)`. The jets are combinations of `K(ν+k)`, `|k| ≤ 2`, with coefficients free of `ν`. The arithmetic coefficient obeys `‖c_n(u)‖ ≤ n^{3|Re u|+1}`.

**Claim 4.** Write `E = Y^{½+u} + ψ(u) Y^{½-u} + χ(u) T(u)` with `ψ(u) = ((1+2u)/(2u-1)) ξ(2u)/ξ(1+2u)` and `χ(u) = (1+2u)(2u)/ξ(1+2u)`. On `u = iξ`, `|ψ| = 1` and `‖χ‖` is below any Gaussian, so every jet of `E` is dominated by `e^{cξ²}` for any `c > 0`, and `∂_Y²` of the tail comes from the eigen-equation. Differentiate under the integral and use `Δ E = -(ξ²+¼)E`. Invariance holds for `ξ ≠ 0` because `E` is the completed Fourier model divided by `Λ(1+2u)`.

**Claim 5.** Fubini with the zero mean of the tail in `x`.

**Claim 6.** `g(S) = √(π/ε) exp(iξ₀S - S²/(4ε))`, and the same value is obtained from `∫ a(-iw) e^{wS} dy` on every line `w = c + iy`. For `c > ½`, Fubini and the Laplace transform of `K` give `g∗K(T) = ∫ a(-iw) e^{wT} φ(½+w) dy`. For `Re w ≥ 0`, `‖ξ(2w)‖ ≤ ‖ξ(1+2w)‖`: on `Re w > 0` this is the limit `c ↓ ½` of `norm_XiC_vertical_shift_lt_of_halfPlaneBound` at `α = ½`, and on `Re w = 0` it is the functional equation. So `|φ(½+w)|` is bounded by a rational factor, and the Gaussian kills the horizontal edges. The only pole in `0 ≤ Re w ≤ c` is `w = ½`, with residue `a(-i/2) e^{T/2} ξ(1)/ξ(2) = (3/π) a(-i/2) e^{T/2}`. Finally `∫ g(T-τ) e^{τ/2} dτ = 2π a(-i/2) e^{T/2}` by the closed form of `g`.

**Claim 7.** `E = N/ξ(1+2u)` with `N = Y^{½+u} ξ(1+2u) + ((1+2u)/(2u-1)) ξ(2u) Y^{½-u} + (1+2u)(2u) T`, analytic on `Re u < ½`. Since `‖ξ(s)‖ ≤ ξ(Re s)`, `‖N‖ ≤ K(1+|Im u|)²` on `-A ≤ Re u ≤ 0`, and `|(1+2u)/(2u-1)| ≤ 1` there. The numerator `a(-iu) e^{uτ} N` is therefore Gaussian, and the contour theorem gives the expansion at depth `A`. The residues do not depend on `A`, so by uniqueness of limits neither does `R`, and `e^{uτ}` gives `‖R‖ ≤ C_A e^{-Aτ}`. For the mode: with `ξ(1+2u) = (u-p)^{n+1} g(u)`, `g(p) ≠ 0`, the Leibniz rule for the Taylor coefficients of `(a N/g)(p+t) e^{(p+t)τ}` gives `e^{pτ} Σ_{i≤n} c_i τ^{n-i}/(n-i)!`, `c_0 = a(-ip) N(p)/g(p)`. Excitation: the horocycle mean of `N(p; ·, Y)` is `((1+2p)/(2p-1)) ξ(2p) Y^{½-p}`, nonzero because `ξ(2p) = ξ(1-2p)` and `Re(1-2p) > 1`. Plus branch: `ω₊(z(p')) = ω₋(z(p))` forces `p' = -p`, contradicting `Re p, Re p' < 0`.

**Claim 8.** On a finite rectangle, `𝓕 - R - 2π Σ Res` is the tail of the line `Re u = 0`, minus the tail of the line `Re u = -A`, minus the edges over `i`. For `τ ≥ 0` and `Re u ≤ 0`, `|e^{uτ}| ≤ 1`, so each term is dominated by its value at `τ = 0`, independent of `τ`, and tends to zero along the good heights.

**Claim 9.** The `k`-th time derivative of `𝓕` is the packet with symbol `E (iξ)^k`, again dominated by a Gaussian, so `𝓕` is `C^∞` in `τ`. `H = -x + log(1+e^{2x})` and `e^{2x} = (r-1)/(r+1)` give `τ = v - log(2r/(r+1))`, smooth on `r > 0`. Composing gives the claim.

**Claim 10.** `∫ e^{-wS} g(S) dS = 2π a(-iw)` by the closed form. `e^{-wT}(g∗K)(T)` is the convolution of `e^{-wτ}K` and `e^{-wS}g`, both integrable, so the transform is the product. The kernel transform is `retardedTransform_dampedEchoKernel`. The static term comes from claims 5, 6 and `e^{-τ/2} √Y e^{(τ - log Y)/2} = 1`.

## Limits
- Convergence of the mode sum is along the good heights `T_k`. Absolute convergence over all zeros is not claimed, as it needs lower bounds on `ξ'(ρ)` that are not available.
- The data are Gaussian packets in the Eisenstein channel. General data on the horizon, the cusp-form channel, and a spin-two field are not covered.
- A hyperbolic horizon does not occur for asymptotically flat black holes. This concerns the AdS solution only, not astrophysical ringdown.
- Universal damping at the rate `D + 1/4` is RH-equivalent (`riemannHypothesis_iff_universal_damping`). Nothing here decides it, and the rate bound is only `D < D + (1-β)/2 < D + ½`.

## No-go closure
Not applicable: the claims are proved.
