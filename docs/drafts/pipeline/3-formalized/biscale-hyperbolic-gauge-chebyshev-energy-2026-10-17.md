# BiScale: hyperbolic-gauge Chebyshev energy representation of the signed prime–polar packet

- **ID:** biscale-chebyshev-gauge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` §6 open problem 1 (signed prime-to-polar measure transport and Chebyshev discrepancy coupling); `docs/reports/walls-ledger.md` Wall 1
- **Statement:** For a compact `C¹` source `f` and cutoff `L = log(N+2)`, the signed prime–polar packet `P = Σ Λ(n)n^{-1/2} f(·+log n) − ∫_0^L 2cosh(t/2) f(·+t) dt` equals `R f + Ẽ(L) f(·+L) − D f` with `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)`, `R f = f − ∫_0^L e^{−t/2} f(·+t)`, and `D f = ∫_0^L Ẽ(t)(f' − f/2)(·+t) dt`. Hence `packetEnergy f N = ∫ (R f + Ẽ(L) f(·+L) − D f)²`, `∫ (D f)² = ∬ Ẽ(s)Ẽ(t) autocorr(f' − f/2)(t − s)`, `∫ (D f)² ≤ ‖f' − f/2‖₁² ∫_0^L Ẽ²`, `∫ (R f)² ≤ 10 autocorr f 0`, and the two-sided transfer `packetEnergy ≤ 3(10 + Ẽ(L)²) h_f(0) + 3‖f'−f/2‖₁² ∫_0^L Ẽ²`, `∫(D f)² ≤ 3 packetEnergy + 3(10 + Ẽ(L)²) h_f(0)`; dictionary `∫_0^L Ẽ² = ∫_1^{e^L} (ψ(x) − x)²/x² dx`.

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

## What this changes in the open core
- Pillar XV's linear Chebyshev work is now matched by a quadratic law: the packet energy (the field's cancellation-sensitive Gram energy) is the Chebyshev mean square smoothed by the gauge derivative. The "finite-window, no stabilization" caveat of Pillar XV.5 is resolved into an exact criterion: stabilization ⟺ `∫_0^L Ẽ² = O(L)` ⟺ mean-square RH.
- All compression/Bessel/Krein tools act on the right-hand side `autocorr(f' − f/2)`; the arithmetic lives entirely in `Ẽ`.

## Log
- 2026-10-17 — module built, wired, axioms standard; moved directly to 3-formalized.
