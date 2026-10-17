# BiScale: hyperbolic-gauge Chebyshev energy representation of the signed prime–polar packet

- **ID:** biscale-chebyshev-gauge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` §6 open problem 1 (signed prime-to-polar measure transport and Chebyshev discrepancy coupling); `docs/reports/walls-ledger.md` Wall 1
- **Statement (module 1):** For a compact `C¹` source `f` and cutoff `L = log(N+2)`, the signed prime–polar packet `P = Σ Λ(n)n^{-1/2} f(·+log n) − ∫_0^L 2cosh(t/2) f(·+t) dt` equals `R f + Ẽ(L) f(·+L) − D f` with `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)`, `R f = f − ∫_0^L e^{−t/2} f(·+t)`, and `D f = ∫_0^L Ẽ(t)(f' − f/2)(·+t) dt`. Hence `packetEnergy f N = ∫ (R f + Ẽ(L) f(·+L) − D f)²`, `∫ (D f)² = ∬ Ẽ(s)Ẽ(t) autocorr(f' − f/2)(t − s)`, `∫ (D f)² ≤ ‖f' − f/2‖₁² ∫_0^L Ẽ²`, `∫ (R f)² ≤ 10 autocorr f 0`, and the two-sided transfer `packetEnergy ≤ 3(10 + Ẽ(L)²) h_f(0) + 3‖f'−f/2‖₁² ∫_0^L Ẽ²`, `∫(D f)² ≤ 3 packetEnergy + 3(10 + Ẽ(L)²) h_f(0)`; dictionary `∫_0^L Ẽ² = ∫_1^{e^L} (ψ(x) − x)²/x² dx`.

- **Statement (module 2, `ChebyshevGaugeNyquistCellQuadrature.lean`):** On each Nyquist cell `[log n, log(n+1))`, `∫ Ẽ² = (ψ(n) − m_n)²/(n(n+1)) + c_n` with `m_n = n(n+1)log((n+1)/n) ∈ [n, n+1]` and `c_n = ∫_{cell} e^{−t}(m_n − e^t)² ∈ [0, 2/(n(n+1))]`. Hence `Σ_{n<M}(ψ(n)−m_n)²/(n(n+1)) ≤ ∫_0^{log M} Ẽ² ≤ Σ_{n<M}(ψ(n)−m_n)²/(n(n+1)) + 2`, the dyadic-window law on `[log N, log 2N]`, and the comparison `½ Σ (ψ(n)−n)²/(n(n+1)) − 1 ≤ ∫_0^{log M} Ẽ² ≤ 2 Σ (ψ(n)−n)²/(n(n+1)) + 4`.

- **Statement (module 3, `CausalExponentialResponseAndLaplaceEnergy.lean`):** With `K(x) = e^{−x/2}1_{x≥0}` and `ν_N` the signed prime–polar measure, the causal response `R_N(t) = pairing N (K(t−·))` equals `Ẽ(t) + (1−t)e^{−t/2}` on `[0, L]`, vanishes for `t < 0`, and equals `e^{−(t−L)/2} R_N(L)` for `t ≥ L`; `∫ K(t−a)K(t−b) dt = e^{−|a−b|/2}` (`autocorr K = laplaceKernel`); `∫ R_N² = laplaceEnergy N := ∬ e^{−|s−t|/2} dν_N dν_N`; `laplaceEnergy N = ∫_0^L (Ẽ + (1−t)e^{−t/2})² + (Ẽ(L) + (1−L)e^{−L/2})²`; two-sided comparison `∫_0^L Ẽ² ≤ 2 laplaceEnergy N + 2` and `laplaceEnergy N ≤ 2∫_0^L Ẽ² + 2 + R_N(L)²`. Generic tool: `integral_pairing_of_dominated` (line integral commutes with the pairing under an integrable majorant).

- **Statement (module 4, `CausalCorrelationPacketRepresentation.lean`):** The causal kernel inverts the gauge derivative, `f(u) = −∫ K(t) g(u+t) dt` (`g = f' − f/2`), so `signedSource f N (u) = −∫ R_N(t) g(u+t) dt`; hence `packetEnergy f N = ∬ R_N(t) R_N(s) autocorr g (s−t) = ∫ autocorr g · autocorr R_N` and (Young) `packetEnergy f N ≤ ‖g‖₁² · laplaceEnergy N`; Green's identity `autocorr f (x) = ∫ autocorr g (y) e^{−|x+y|/2} dy = (autocorr g ⋆ e^{−|·|/2})(x)`; `packetEnergy f N = pairing N (pairing N ((autocorr g ⋆ laplaceKernel)(s − t)))`. Generic tool: `integral_integral_shift_swap` (Fubini for `∫ φ(u) ∫ R(t) g(u+t)` with `φ, R ∈ L¹`, `g` bounded).

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

## What this changes in the open core
- Pillar XV's linear Chebyshev work is now matched by a quadratic law: the packet energy (the field's cancellation-sensitive Gram energy) is the Chebyshev mean square smoothed by the gauge derivative. The "finite-window, no stabilization" caveat of Pillar XV.5 is resolved into an exact criterion: stabilization ⟺ `∫_0^L Ẽ² = O(L)` ⟺ mean-square RH.
- All compression/Bessel/Krein tools act on the right-hand side `autocorr(f' − f/2)`; the arithmetic lives entirely in `Ẽ`.
- Module 3 lifts `Ẽ` itself into the field's object class: `Ẽ + transient = K ⋆ ν_N` is the causal exponential response of the signed prime–polar measure, and `∫_0^L Ẽ²` is (up to constants) the Gram energy of `ν_N` against the positive-definite Laplace kernel `e^{−|x|/2}`. Wall 1 is now the statement `laplaceEnergy N = O(log N)`: a Gram energy of the field's own signed measure against the pole kernel.
- Module 4 closes the loop between the two energy classes: every compact-source Gram energy is `⟨autocorr(f'−f/2), autocorr R_N⟩`, and `autocorr R_N (0) = laplaceEnergy N` dominates. The field's whole arithmetic content is the single response `R_N`; sources only choose the positive-definite filter `autocorr g`. One-line transfer `packetEnergy ≤ ‖f'−f/2‖₁² laplaceEnergy` replaces the three-term bound of module 1.
- Wall 1 is now fully discrete inside the field: packet-energy stabilization ⟺ `Σ_{n<M} (ψ(n) − n)²/(n(n+1)) = O(log M)`. Each Nyquist cell contributes `(ψ(n) − m_n)²/(n(n+1))` plus a universal floor `c_n ≈ 1/(12n²)`; the centre `m_n = n + ½ − 1/(6n) + …` is the exact exponential-gauge mean of the cell.

## Next conjectures (queued)
- Spectral representation (module 5): `𝓕 R_N (ξ) = ν̂_N(ξ)/(½ + 2πiξ)` with `ν̂_N(ξ) = Σ Λ(n) n^{−(½+2πiξ)} − (e^{L(½−2πiξ)} − 1)/(½ − 2πiξ) − (1 − e^{−L(½+2πiξ)})/(½ + 2πiξ)`, hence by Plancherel (`HTGeometry.integral_norm_sq_fourier`) `laplaceEnergy N = ∫ ‖ν̂_N(ξ)‖²/(¼ + 4π²ξ²) dξ`: Wall 1 = weighted critical-line mean square of the pole-subtracted truncated `−ζ'/ζ`.
- Dyadic Markov chain of the response: semigroup law `R_N(t) = e^{−(t−a)/2} R_N(a) + (K ⋆ ν_N|_{(a,t]})(t)`; block-edge chain `x_{k+1} = x_k/√2 + r_k`; window energy `∫_{block k} R_N² = ½x_k² + 2 b_k x_k + c_k`; `laplaceEnergy ≍ Σ_k x_k² + Σ_k c_k`, `Σ x_k² ≍ Σ r_k²`.
- Jump-energy law: `lim_{y→0} (laplaceEnergy N − autocorr R_N (y))/|y| = ½ Σ_{n≤N+2} Λ(n)²/n`.
- Arithmetic expansion of `laplaceEnergy N` (atoms/polar/cross): `Σ Λ(n)(2ψ(n)−Λ(n))/n − 2(1+L−e^{−L})ψ(N+2) + 2Σ Λ(n) log n (1 − 1/n) + polar self-energy`.
- Spectral representation: `laplaceEnergy N = (1/2π) ∫ |ν̂_N(r)|² /(¼ + r²) dr` (Fourier transform of `e^{−|x|/2}`).
- Sub-Nyquist diagonal law: for sources narrower than the local Nyquist spacing, the atomic packet energy is exactly `Σ Λ(n)²/n · h_f(0)` (disjoint translates), so square-root cancellation is visible only to super-Nyquist sources.
- Sharper centre asymptotics `|m_n − n − ½| ≤ 1/(6n)` via the Taylor remainder of `log(1+x)`.

## Log
- 2026-10-17 — module 1 built, wired, axioms standard; moved directly to 3-formalized.
- 2026-10-17 — module 2 (Nyquist-cell quadrature, window law, classical comparison) built, wired, axioms standard.
- 2026-10-17 — module 4 (causal reconstruction, packet = response ⋆ gauge derivative, Gram/autocorrelation forms, Young bound by the Laplace energy, Green identity) built, wired.
- 2026-10-17 — module 3 (causal response, Laplace kernel = autocorr K, `∫R_N² = laplaceEnergy`, window/tail split, two-sided comparison with `∫Ẽ²`, pairing/line-integral interchange) built, wired, axioms standard.
