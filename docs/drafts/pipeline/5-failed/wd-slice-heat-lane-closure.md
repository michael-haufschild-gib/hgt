# WD slice-heat lane: closure by a named countermodel

- **ID:** wd-slice-heat-lane-closure
- **Stage:** 5-failed (route-level no-go for the heat lane as an RH mechanism)
- **Source:** `wd-goal-loop-2026-10-09.md` rows 292–299

## No-go statement
Heated slice positivity at heat κ/log t (any rate κ) is compatible with an off-line pair at every offset δ ≤ κ. Countermodel: F(z) = ((z−t₀)²+δ²)·√2 sin(L(z−t₀)/2 + π/4), with slice (δ²−x²)²cosh(Lx), heated coefficients ≥ 0 for λ ≥ δ/L (`RHTower/XiSliceHeatCoshCountermodel.hasSum_coshModelHeat`). Even the Lindelöf tier κ = ½ excludes nothing, so the heat lane cannot produce zero-free strips.

## Positive survivors (all [L])
- Everywhere heat rate κ = 1+δ (row 293, `XiSliceHeatRateOnePlusDelta`).
- Typical-height abscissa c/log t, exceptional proportion e^{−c/28} (row 294, `XiHorizontalAbsMonoCriticalScaleDensity`).
- Heat from abscissa λ* ≤ 100x₀² (row 295, `XiSliceHeatFromAbscissa`).
- Heated detection, perturbative (row 296, `XiSliceHeatedOffLineDetection`).
- Hermite-window detection, logarithmic in the envelope (row 297, `XiSliceHermiteWindowDetection`, `HTGeometry/HermiteGeneratingFunction`).

## Open residual
KKL-scale detection λ*(γ) ≳ δ/log γ. It is blocked unconditionally by local zero clustering (O(log γ) zeros within r₀ of γ, allowed by S(t) = O(log t)). It holds at ordinates with regular local counting (row 298).

## Log
- 2026-10-12 — closed (row 299).
