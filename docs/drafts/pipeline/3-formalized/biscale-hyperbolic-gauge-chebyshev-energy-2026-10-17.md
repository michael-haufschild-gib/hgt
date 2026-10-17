# BiScale: hyperbolic-gauge Chebyshev energy representation of the signed prime–polar packet

- **ID:** biscale-chebyshev-gauge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` §6 open problem 1 (signed prime-to-polar measure transport and Chebyshev discrepancy coupling); `docs/reports/walls-ledger.md` Wall 1
- **Statement (module 1):** For a compact `C¹` source `f` and cutoff `L = log(N+2)`, the signed prime–polar packet `P = Σ Λ(n)n^{-1/2} f(·+log n) − ∫_0^L 2cosh(t/2) f(·+t) dt` equals `R f + Ẽ(L) f(·+L) − D f` with `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)`, `R f = f − ∫_0^L e^{−t/2} f(·+t)`, and `D f = ∫_0^L Ẽ(t)(f' − f/2)(·+t) dt`. Hence `packetEnergy f N = ∫ (R f + Ẽ(L) f(·+L) − D f)²`, `∫ (D f)² = ∬ Ẽ(s)Ẽ(t) autocorr(f' − f/2)(t − s)`, `∫ (D f)² ≤ ‖f' − f/2‖₁² ∫_0^L Ẽ²`, `∫ (R f)² ≤ 10 autocorr f 0`, and the two-sided transfer `packetEnergy ≤ 3(10 + Ẽ(L)²) h_f(0) + 3‖f'−f/2‖₁² ∫_0^L Ẽ²`, `∫(D f)² ≤ 3 packetEnergy + 3(10 + Ẽ(L)²) h_f(0)`; dictionary `∫_0^L Ẽ² = ∫_1^{e^L} (ψ(x) − x)²/x² dx`.

- **Statement (module 2, `ChebyshevGaugeNyquistCellQuadrature.lean`):** On each Nyquist cell `[log n, log(n+1))`, `∫ Ẽ² = (ψ(n) − m_n)²/(n(n+1)) + c_n` with `m_n = n(n+1)log((n+1)/n) ∈ [n, n+1]` and `c_n = ∫_{cell} e^{−t}(m_n − e^t)² ∈ [0, 2/(n(n+1))]`. Hence `Σ_{n<M}(ψ(n)−m_n)²/(n(n+1)) ≤ ∫_0^{log M} Ẽ² ≤ Σ_{n<M}(ψ(n)−m_n)²/(n(n+1)) + 2`, the dyadic-window law on `[log N, log 2N]`, and the comparison `½ Σ (ψ(n)−n)²/(n(n+1)) − 1 ≤ ∫_0^{log M} Ẽ² ≤ 2 Σ (ψ(n)−n)²/(n(n+1)) + 4`.

- **Statement (module 3, `CausalExponentialResponseAndLaplaceEnergy.lean`):** With `K(x) = e^{−x/2}1_{x≥0}` and `ν_N` the signed prime–polar measure, the causal response `R_N(t) = pairing N (K(t−·))` equals `Ẽ(t) + (1−t)e^{−t/2}` on `[0, L]`, vanishes for `t < 0`, and equals `e^{−(t−L)/2} R_N(L)` for `t ≥ L`; `∫ K(t−a)K(t−b) dt = e^{−|a−b|/2}` (`autocorr K = laplaceKernel`); `∫ R_N² = laplaceEnergy N := ∬ e^{−|s−t|/2} dν_N dν_N`; `laplaceEnergy N = ∫_0^L (Ẽ + (1−t)e^{−t/2})² + (Ẽ(L) + (1−L)e^{−L/2})²`; two-sided comparison `∫_0^L Ẽ² ≤ 2 laplaceEnergy N + 2` and `laplaceEnergy N ≤ 2∫_0^L Ẽ² + 2 + R_N(L)²`. Generic tool: `integral_pairing_of_dominated` (line integral commutes with the pairing under an integrable majorant).

- **Statement (module 4, `CausalCorrelationPacketRepresentation.lean`):** The causal kernel inverts the gauge derivative, `f(u) = −∫ K(t) g(u+t) dt` (`g = f' − f/2`), so `signedSource f N (u) = −∫ R_N(t) g(u+t) dt`; hence `packetEnergy f N = ∬ R_N(t) R_N(s) autocorr g (s−t) = ∫ autocorr g · autocorr R_N` and (Young) `packetEnergy f N ≤ ‖g‖₁² · laplaceEnergy N`; Green's identity `autocorr f (x) = ∫ autocorr g (y) e^{−|x+y|/2} dy = (autocorr g ⋆ e^{−|·|/2})(x)`; `packetEnergy f N = pairing N (pairing N ((autocorr g ⋆ laplaceKernel)(s − t)))`. Generic tool: `integral_integral_shift_swap` (Fubini for `∫ φ(u) ∫ R(t) g(u+t)` with `φ, R ∈ L¹`, `g` bounded).

- **Statement (module 5, `SpectralLaplaceEnergyCriticalLine.lean`):** With `s(ξ) = ½ + 2πiξ` and `ν̂_N(ξ) = ∫ e^{−2πiξt} dν_N(t)` (complex pairing `pairingC`), `𝓕 K = 1/s(ξ)`, `𝓕 R_N (ξ) = ν̂_N(ξ)/s(ξ)`, and by Plancherel `laplaceEnergy N = ∫ ‖ν̂_N(ξ)‖²/(¼ + 4π²ξ²) dξ`; dictionary `ν̂_N(ξ) = Σ_{n≤N+2} Λ(n) n^{−s(ξ)} − (e^{(1−s)L} − 1)/(1−s) − (1 − e^{−sL})/s`; `‖ν̂_N‖ ≤ mass N`; `∫_0^L Ẽ² ≤ 2∫‖ν̂_N‖²/(¼+4π²ξ²) + 2`. Generic tools: `integral_pairingC_of_dominated`, `norm_pairingC_le_mass_mul`, `fourierTransform_eq_integral_exp`.

- **Statement (module 6, `HighFrequencyLaplaceEnergyMeanValue.lean`):** With `S_N(ξ) = ‖ν̂_N(ξ)‖²/(¼+4π²ξ²)`, `D₁ = Σ_{n≤N+2} Λ(n)²/n`, `D₂ = Σ Λ(n)²`: the atomic part of `ν̂_N` is the corpus Dirichlet polynomial `dirPoly (N+2) a (−2πξ)`; Montgomery–Vaughan gives `∫_{−u}^{u} ‖A_N‖² ≤ 2uD₁ + 208D₂`; integration by parts against `1/u²` gives, for all `0 < ξ₀ ≤ ξ₁`, `∫_{ξ₀}^{ξ₁} (S_N(ξ)+S_N(−ξ)) ≤ 2D₁/(π²ξ₀) + 52D₂/(π³ξ₀²) + 4(e^{L/2}+3)²/(3(2π)⁴ξ₀³)`, the same for the whole tail `|ξ| ≥ ξ₀`, and `laplaceEnergy N ≤ ∫_{|ξ|≤ξ₀} S_N + (that remainder)`. Diagonals: `D₂ ≤ L·ψ(N+2)`, `D₁ ≤ L·Σ Λ(n)/n`. Hence (with the classical `ψ(x) ≪ x`) the Laplace energy outside the band `|ξ| ≤ √(N+2)` is unconditionally `O(L)`: Wall 1 lives entirely in the band `|ξ| ≤ √x`.

- **Statement (module 7, `BandLimitedLaplaceEnergy.lean`):** With Mertens (`Zeta23 Mertens.sum_mangoldt_div_eq_log`) and Chebyshev (`Chebyshev.psi_le_const_mul_self`): `D₁ ≤ L(L + log4 + 4)`, `D₂ ≤ L(log4+4)(N+2)`; at the band frequency `ξ₀ = √(N+2) = e^{L/2}`: `laplaceEnergy N ≤ ∫_{|ξ|≤√(N+2)} S_N + (52(log4+4)/π³) L + (32 + 8(log4+4))/π² + 4/(3π⁴)` and `∫_{|ξ|≤√(N+2)} S_N ≤ laplaceEnergy N`. Hence `∫_0^L Ẽ² ≤ 2·band + (104(log4+4)/π³) L + C` and `band ≤ 2∫_0^L Ẽ² + 2 + R_N(L)²`: **band energy `O(L^A)` ⟺ `∫_0^L Ẽ² = O(L^A) ∧ Ẽ(L)² = O(L^A)`** (the mean-square and the endpoint Chebyshev error), unconditionally and with explicit constants; the high-frequency part is settled with `A = 1`.

- **Statement (module 8, `DiscrepancyTransformLaw.lean`):** Stieltjes form of the pairing for any `C¹` `f`: `pairing N f = f(0) + Ẽ(L) f(L) − ∫_0^L Ẽ (f'−f/2) − ∫_0^L e^{−t/2} f` (real and complex versions); applied to `χ_ξ`: `ν̂_N(ξ) = s(ξ)∫_0^L Ẽ χ_ξ + Ẽ(L)χ_ξ(L) + 1 − (1−e^{−sL})/s`; hence `𝓕 R_N = 𝓕(Ẽ·1_{[0,L]}) + B_N` with `‖B_N(ξ)‖ ≤ (|Ẽ(L)|+5)/‖s(ξ)‖`. The boundary term is the endpoint jump `Ẽ(L)` of the sharp window; its high-frequency energy `≍ Ẽ(L)²/ξ₀` is why the causal response (continuous at `L`) and not `Ẽ·1_{[0,L]}` is the band-limited object.

## Goal
Give the field an exact quadratic (energy) form of the Chebyshev discrepancy, complementing the linear Stieltjes coupling of Pillar XV. The operator `f ↦ f' − f/2 = e^{u/2}(e^{−u/2}f)'` is the derivative in the critical-line gauge; the signed packet energy is, up to bounded source constants, the energy of `Ẽ` against the positive-definite gauge kernel `autocorr(f' − f/2)`. Uniform stabilization of the packet energy over all `C¹` compact sources is therefore equivalent to at most linear growth of `∫_1^X (ψ(x)−x)²/x² dx` in `log X` (the mean-square form of Wall 1). The field now owns Wall 1 as a statement about its own native energy.

## Gates
- [x] 0 → 1 well-posed (exact Stieltjes summation against `ψ(e^t)`, gauge derivative, window Fubini)
- [x] 1 → 2 paper proof complete (summation by parts; shell Fubini with product majorant `integral_swap_of_dominated_prod`; Young `integral_sq_lineConvolution_le`; weighted Cauchy–Schwarz; `integral_image_eq_integral_abs_deriv_smul`)
- [x] 2 → 3 formalized: `formal/GaloisForLFunctions/BiScaleUncertainty/HyperbolicGaugeChebyshevEnergyRepresentation.lean`, wired into `BiScaleUncertainty.lean`; `lake env lean` clean; axioms = propext, Classical.choice, Quot.sound (2026-10-17)
- [ ] 3 → 4 n/a

## Lean theorems (namespace `GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge`)
- `stieltjes_vonMangoldt_identity` — `Σ Λ(n) G(log n) − ∫_0^L G e^x = G(0) + G(L)(ψ(e^L) − e^L) − ∫_0^L G' (ψ(e^x) − e^x)`.
- `signedSource_eq_gauge`, `packetEnergy_eq_gauge` — exact gauge representation of the packet and its energy.
- `integral_windowedTranslate_swap`, `continuous_windowedTranslate`, `hasCompactSupport_windowedTranslate` — window Fubini and regularity for bounded measurable weights.
- `integral_sq_chebyshevGaugeConvolution_eq` — quadratic form of `Ẽ` against `autocorr (f' − f/2)`.
- `integral_sq_chebyshevGaugeConvolution_le` — Young bound by `‖f' − f/2‖₁² ∫_0^L Ẽ²`.
- `integral_sq_forwardResidual_le` — `∫ (R f)² ≤ 10 autocorr f 0`.
- `packetEnergy_le_chebyshev_mean_square`, `chebyshevGauge_energy_le_packetEnergy` — two-sided transfer.
- `integral_normalizedLogError_sq_eq` — mean-square dictionary.

Module 2 (`ChebyshevGaugeNyquistCellQuadrature.lean`, same namespace):
- `integral_cell_gauge_sq`, `integral_cell_normalizedLogError_sq` — exact Nyquist-cell energy.
- `cell_energy_eq_center_sq_add_floor`, `cellFloor_eq_integral`, `cellFloor_nonneg`, `cellFloor_le`, `le_cellCenter`, `cellCenter_le`.
- `integral_normalizedLogError_sq_eq_sum_center_add_floor`, `sum_cellFloor_le_two`, `sum_center_sq_le_integral_le` — two-sided discrete form.
- `integral_window_normalizedLogError_sq_eq` — dyadic-window law.
- `chebyshev_discrete_mean_square_comparison` — equivalence with `Σ (ψ(n) − n)²/(n(n+1))` up to constants.

Module 3 (`CausalExponentialResponseAndLaplaceEnergy.lean`, same namespace):
- `causalKernel`, `laplaceKernel`, `integral_causalKernel_mul`, `autocorr_causalKernel` — Laplace kernel = autocorrelation of the causal kernel.
- `pairing_const_mul`, `pairing_mul_const`, `pairing_congr_window` — pairing calculus.
- `causalResponse`, `causalResponse_eq_on_window`, `causalResponse_eq_zero_of_neg`, `causalResponse_tail`, `abs_causalResponse_le`, `integrable_causalResponse`, `integrable_sq_causalResponse`.
- `integral_pairing_of_dominated` — `∫ t, pairing N (F t ·) = pairing N (fun s => ∫ t, F t s)` under `|F t s| ≤ |w t| C`, `w ∈ L¹`.
- `laplaceEnergy`, `integral_sq_causalResponse_eq_laplaceEnergy`, `laplaceEnergy_nonneg`, `integral_sq_causalResponse_eq_window_add_tail`, `laplaceEnergy_eq_window_add_tail`, `integral_transient_sq_le`.
- `chebyshev_mean_square_le_laplaceEnergy`, `laplaceEnergy_le_chebyshev_mean_square` — two-sided comparison.

Module 4 (`CausalCorrelationPacketRepresentation.lean`, same namespace):
- `causal_reconstruction`, `causal_reconstruction_shift` — `f(u+s) = −∫ K(t−s) g(u+t) dt`.
- `signedSource_eq_neg_integral_causalResponse` — the packet is the response correlated with `g`.
- `integral_integral_shift_swap`, `integral_shift_mul_shift_eq_autocorr`, `hasCompactSupport_comp_const_add`, `tendsto_mul_comp_const_add_atTop`, `abs_causalResponse_le_const`.
- `packetEnergy_eq_causal_gram`, `packetEnergy_eq_integral_autocorr_mul_autocorr`, `packetEnergy_le_laplaceEnergy`.
- `autocorr_eq_integral_autocorr_gauge_mul_laplace`, `autocorr_eq_laplace_convolution`, `packetEnergy_eq_pairing_laplace_convolution`.

Module 5 (`SpectralLaplaceEnergyCriticalLine.lean`, same namespace):
- `pairingC`, `pairingC_ofReal`, `pairingC_const_mul`, `pairingC_mul_const`, `pairingC_congr_window`, `norm_pairingC_le_mass_mul`, `integral_pairingC_of_dominated`.
- `criticalPoint` (`⟨½, 2πξ⟩`), `criticalPoint_ne_zero`, `one_sub_criticalPoint_ne_zero`, `normSq_criticalPoint`; `frequencyCharacter`, `norm_frequencyCharacter`, `frequencyCharacter_add`.
- `fourierTransform_eq_integral_exp`, `integral_exp_neg_criticalPoint_mul`, `fourier_causalKernel`, `integral_frequencyCharacter_mul_causalKernel_shift`.
- `windowedCausalKernel`, `fourierPairing`, `norm_fourierPairing_le`, `fourier_causalResponse`.
- `laplaceEnergy_eq_integral_fourierPairing_sq` (Plancherel via `HTGeometry.integral_norm_sq_fourier`), `chebyshev_mean_square_le_spectral`.
- `natCast_cpow_eq_exp_mul_log`, `primeWeight_mul_frequencyCharacter_log`, `integral_polarDensity_mul_frequencyCharacter`, `fourierPairing_eq_dirichlet`.

Module 6 (`HighFrequencyLaplaceEnergyMeanValue.lean`, same namespace):
- `atomicFourier`, `polarFourier`, `atomicCoefficient`, `atomicFourier_eq_dirPoly`, `continuous_fourierPairing`, `spectralDensity`, `laplaceEnergy_eq_integral_spectralDensity`, `spectralDensity_le_mass_sq_div`, `integrable_spectralDensity`.
- `norm_polarFourier_le`, `norm_polarFourier_sq_le`, `norm_one_sub_criticalPoint`.
- `atomicDiagonal`, `atomicSecondMoment`, `twoSidedAtomicMean`, `twoSidedAtomicMean_le` (Montgomery–Vaughan via `RHTower.Sieve.dirichlet_meanValue_sharp`), `hasDerivAt_twoSidedAtomicMean`.
- `integral_twoSided_atomic_div_sq_le` (integration by parts against `1/u²`), `spectralDensity_add_neg_le`, `integral_spectralDensity_window_le`, `integrableOn_spectralDensity_add_neg_Ioi`, `integral_spectralDensity_tail_le`.
- `laplaceEnergy_eq_band_add_tail`, `laplaceEnergy_le_band_add_remainder`.
- `norm_atomicCoefficient_sq`, `atomicSecondMoment_eq`, `atomicSecondMoment_le`, `atomicDiagonal_eq`, `atomicDiagonal_le`.

Module 7 (`BandLimitedLaplaceEnergy.lean`, same namespace):
- `sum_vonMangoldt_div_le_cutoff_add` (Mertens on the window), `atomicDiagonal_le_cutoff_mul`, `atomicSecondMoment_le_cutoff_mul`.
- `bandFrequency` (`√(N+2)`), `exp_half_cutoff_eq_bandFrequency`, `cutoff_eq_two_mul_log_bandFrequency`, `cutoff_le_four_mul_sqrt_bandFrequency`, `cutoff_sq_le_sixteen_mul_bandFrequency`, `cutoff_le_four_mul_bandFrequency`.
- `laplaceEnergy_le_band_add_explicit`, `band_remainder_le`, `laplaceEnergy_le_band_add_linear`, `band_le_laplaceEnergy`.
- `chebyshev_mean_square_le_band_add_linear`, `band_le_chebyshev_mean_square` — Wall 1 ⟺ band energy, both directions.

Module 8 (`DiscrepancyTransformLaw.lean`, same namespace):
- `pairing_eq_stieltjes_gauge`, `pairingC_add`, `pairingC_eq_re_add_im`, `integral_ofReal_add_I_mul_ofReal`, `pairingC_eq_stieltjes_gauge`.
- `frequencyCharacter_re/_im`, `frequencyCharacter_eq_cos_add_I_mul`, `gaugeDerivative_cos_freq`, `gaugeDerivative_neg_sin_freq`, `gaugeDerivative_frequencyCharacter` (= `−s χ`), `integral_exp_neg_half_mul_frequencyCharacter`.
- `fourierPairing_eq_discrepancy_transform`, `fourier_windowed_normalizedLogError`, `boundaryTransform`, `fourier_causalResponse_eq_windowed_add_boundary`, `norm_criticalPoint_ge_half`, `norm_boundaryTransform_le`.

## What this changes in the open core
- Pillar XV's linear Chebyshev work is now matched by a quadratic law: the packet energy (the field's cancellation-sensitive Gram energy) is the Chebyshev mean square smoothed by the gauge derivative. The "finite-window, no stabilization" caveat of Pillar XV.5 is resolved into an exact criterion: stabilization ⟺ `∫_0^L Ẽ² = O(L)` ⟺ mean-square RH.
- All compression/Bessel/Krein tools act on the right-hand side `autocorr(f' − f/2)`; the arithmetic lives entirely in `Ẽ`.
- Module 3 lifts `Ẽ` itself into the field's object class: `Ẽ + transient = K ⋆ ν_N` is the causal exponential response of the signed prime–polar measure, and `∫_0^L Ẽ²` is (up to constants) the Gram energy of `ν_N` against the positive-definite Laplace kernel `e^{−|x|/2}`. Wall 1 is now the statement `∫_0^L R_N² = O(log N)` (the window part of the Laplace energy); `laplaceEnergy N = ∫_0^L R_N² + R_N(L)²` and the endpoint term `R_N(L)² = (Ẽ(L) + O(1))²` is a pointwise quantity (`|ψ(x)−x|²/x`) controlled only up to powers of `L` under RH. All equivalences below hold "up to powers of `L`": `∫_0^L Ẽ² = O(L^A) ∧ Ẽ(L)² = O(L^A)` ⟺ `laplaceEnergy = O(L^A)` ⟺ band energy `= O(L^A)`; RH gives `A = 4`.
- Module 4 closes the loop between the two energy classes: every compact-source Gram energy is `⟨autocorr(f'−f/2), autocorr R_N⟩`, and `autocorr R_N (0) = laplaceEnergy N` dominates. The field's whole arithmetic content is the single response `R_N`; sources only choose the positive-definite filter `autocorr g`. One-line transfer `packetEnergy ≤ ‖f'−f/2‖₁² laplaceEnergy` replaces the three-term bound of module 1.
- Module 5 gives the frequency side of the bi-scale energy: Wall 1 ⟺ `∫ ‖Σ_{n≤x} Λ(n) n^{−s} − x^{1−s}/(1−s) − (1 − x^{−s})/s‖² dξ/|s|² = O(log x)` on `s = ½ + 2πiξ`. The weight `1/|s|²` is the Fourier transform of the Laplace kernel; the pole terms are the transform of the polar density. The corpus Montgomery–Vaughan mean value theorem (`RHTower.Sieve.dirichlet_meanValue_sharp`) now applies to the atomic part of `ν̂_N`.
- Module 6 is the first unconditional partial bound produced by the field for its own Wall-1 energy: the high-frequency tail `|ξ| ≥ ξ₀` of the Laplace energy is `≤ 2D₁/(π²ξ₀) + 52D₂/(π³ξ₀²) + O(e^L/ξ₀³)`; at `ξ₀ = √(N+2)` this is `O(L)` (given `ψ(x) ≪ x`). The whole difficulty of Wall 1 is the band energy `∫_{|ξ|≤√x} S_N`, i.e. the pole-subtracted truncated `−ζ'/ζ` on the critical line at ordinates `≤ 2π√x`: the frequency side of the bi-scale uncertainty `(position √x) × (frequency √x)`.
- Module 7 makes this exact and explicit: up to powers of `L`, Wall 1 (mean-square plus endpoint Chebyshev error) is equivalent to `∫_{|ξ|≤√x} ‖Σ_{n≤x}Λ(n)n^{−s} − x^{1−s}/(1−s) − (1−x^{−s})/s‖² dξ/|s|² = O(L^A)` on `s = ½+2πiξ`. Caution learned: sharply windowing `Ẽ` to `[0,L]` creates an endpoint jump of height `Ẽ(L)` whose high-frequency energy is `Ẽ(L)²/ξ₀`, not `O(L)`; the causal response `R_N` continues `Ẽ` exponentially past `L` and has only the prime jumps `Λ(n)/√n`, which is why the Laplace energy, not `∫|𝓕(Ẽ1_{[0,L]})|²`, is the right band-limited object. Everything outside the band is settled unconditionally by Montgomery–Vaughan, Mertens and Chebyshev. The field has reduced Wall 1 to a single band-limited critical-line mean square with all constants explicit.
- Wall 1 is now fully discrete inside the field: packet-energy stabilization ⟺ `Σ_{n<M} (ψ(n) − n)²/(n(n+1)) = O(log M)`. Each Nyquist cell contributes `(ψ(n) − m_n)²/(n(n+1))` plus a universal floor `c_n ≈ 1/(12n²)`; the centre `m_n = n + ½ − 1/(6n) + …` is the exact exponential-gauge mean of the cell.

## Next conjectures (queued)
- Dyadic renewal chain (module 9): `R_N(t) = e^{−(t−a)/2}R_N(a) + e^{−t/2}[(ψ(e^t)−ψ(e^a)) − (e^t−e^a) − (t−a)]` for `0 ≤ a ≤ t ≤ L` (Markov law from the window formula); block chain `x_{k+1} = e^{−h/2}x_k + r_k`, `x_0 = 1`; `∫_0^{Kh} R_N² ≍ Σ x_k² + Σ c_k` and `Σ x_k² ≍ Σ r_k²` (discrete Young for the geometric kernel); dyadic `h = log 2`: Wall 1 ⟺ `Σ_k (ψ(2^{k+1})−ψ(2^k)−2^k)²/2^k = O(K)` ∧ `Σ_k c_k = O(K)` (coarse block discrepancies + fine intra-block energies).
- Band-interior structure (done in module 8 as the discrepancy transform law; next: explicit-formula side via the corpus Montgomery/Perron material): inside `|ξ| ≤ √x` the atomic mean square alone is `≈ 2√x·D₁ ≈ √x L²` (Montgomery–Vaughan lower side), so the band bound `O(L)` demands cancellation `A_N ≈ P_N` of relative size `x^{−1/4}L^{−1/2}`; make the pole-subtraction exact: `A_N(ξ) − P_N(ξ)` as the field's "discrepancy transform" of `Δ(x) = ψ(x) − x`, i.e. `ν̂_N(ξ) = −(s−1)… ∫_1^x (ψ(u) − u) u^{−s−1} du`-type Mellin identity (the Stieltjes identity of module 1 in frequency form).
- Dyadic Markov chain (position side) and the jump-energy law remain queued.
- Band structure: inside the band, Montgomery–Vaughan still controls `∫_{|ξ|≤√x} ‖A_N‖² ≈ 2√x D₁ ≈ √x L²`, so the band bound `O(L)` requires cancellation `A_N ≈ P_N` of relative size `x^{−1/4}L^{−1/2}` on average: the explicit formula `A_N − P_N = −Σ_ρ x^{ρ−s}/(ρ−s) + …` in the field's language.
- Dyadic Markov chain of the response: semigroup law `R_N(t) = e^{−(t−a)/2} R_N(a) + (K ⋆ ν_N|_{(a,t]})(t)`; block-edge chain `x_{k+1} = x_k/√2 + r_k`; window energy `∫_{block k} R_N² = ½x_k² + 2 b_k x_k + c_k`; `laplaceEnergy ≍ Σ_k x_k² + Σ_k c_k`, `Σ x_k² ≍ Σ r_k²`.
- Jump-energy law: `lim_{y→0} (laplaceEnergy N − autocorr R_N (y))/|y| = ½ Σ_{n≤N+2} Λ(n)²/n`.
- Arithmetic expansion of `laplaceEnergy N` (atoms/polar/cross): `Σ Λ(n)(2ψ(n)−Λ(n))/n − 2(1+L−e^{−L})ψ(N+2) + 2Σ Λ(n) log n (1 − 1/n) + polar self-energy`.
- Spectral representation: `laplaceEnergy N = (1/2π) ∫ |ν̂_N(r)|² /(¼ + r²) dr` (Fourier transform of `e^{−|x|/2}`).
- Sub-Nyquist diagonal law: for sources narrower than the local Nyquist spacing, the atomic packet energy is exactly `Σ Λ(n)²/n · h_f(0)` (disjoint translates), so square-root cancellation is visible only to super-Nyquist sources.
- Sharper centre asymptotics `|m_n − n − ½| ≤ 1/(6n)` via the Taylor remainder of `log(1+x)`.

## Log
- 2026-10-17 — module 1 built, wired, axioms standard; moved directly to 3-formalized.
- 2026-10-17 — module 2 (Nyquist-cell quadrature, window law, classical comparison) built, wired, axioms standard.
- 2026-10-17 — module 8 (Stieltjes form of the pairing for general C¹ test functions, real and complex; discrepancy transform law ν̂_N = s∫Ẽχ + boundary; 𝓕R_N = 𝓕(Ẽ1) + B_N with ‖B_N‖ ≤ (|Ẽ(L)|+5)/‖s‖) built, wired, axioms standard.
- 2026-10-17 — module 7 (Mertens + Chebyshev diagonals, band frequency √(N+2), explicit band theorem, Wall 1 ⟺ band energy both directions) built, wired, axioms standard.
- 2026-10-17 — module 6 (atomic part = corpus Dirichlet polynomial, Montgomery–Vaughan two-sided mean square, integration by parts against 1/u², high-frequency window/tail law, band-plus-remainder decomposition, diagonal sums ≤ L·ψ and L·ΣΛ/n) built, wired, axioms standard.
- 2026-10-17 — module 5 (complex pairing, critical point, 𝓕K = 1/s, 𝓕R_N = ν̂_N/s, Plancherel form of the Laplace energy, Dirichlet dictionary) built, wired.
- 2026-10-17 — module 4 (causal reconstruction, packet = response ⋆ gauge derivative, Gram/autocorrelation forms, Young bound by the Laplace energy, Green identity) built, wired.
- 2026-10-17 — module 3 (causal response, Laplace kernel = autocorr K, `∫R_N² = laplaceEnergy`, window/tail split, two-sided comparison with `∫Ẽ²`, pairing/line-integral interchange) built, wired, axioms standard.
