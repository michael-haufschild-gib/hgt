# BHR — the Rankin–Selberg integral of the cusp modes

- **ID:** bhr-cusp-rankin-selberg-integral
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** queued item "Rankin–Selberg continuation" of the ASH/BHR loop; first step (the convergent range).
- **Statement:** Let `g ∈ S(λ)`, `ν = i√(λ − ¼)`, Whittaker coefficients `ρ(n)`, and
  `G(s) = 2^{s−3} Γ((s+2ν)/2) Γ(s/2)² Γ((s−2ν)/2)/Γ(s)`. For `Re s > 1`:
  1. `∫_𝒟 |g|² Σ_{(c,d)} Im(M_{c,d}z)^s dμ = 2 G(s) Σ_n |ρ(n)|² (2π|n|)^{−s}` (absolutely convergent).
  2. If also `Im s ≠ 0`: `∫_𝒟 |g(z)|² E(s − ½; z) dμ = (2π)^{−s} G(s) Σ_{n≠0} |ρ(n)|² |n|^{−s}`
     `= π^{−s}/8 · Γ(s/2)² Γ(s/2+ν) Γ(s/2−ν)/Γ(s) · Σ |ρ(n)|²|n|^{−s}`.

## Paper proof
1. *Strip integrability.* In the chart `(y, x) ∈ (0,∞) × [0,1)` the integrand of `|g|² y^s dμ` is
   `y^{s−2}|g(x+iy)|²`; its fibre integrals are `y^{σ−2} m(y)` (`m` the horocycle mass), integrable on `(0,∞)`:
   `m ≤ sup|g|²` near `0` (`σ > 1`) and `m ≤ D y e^{−4πy}` for `y ≥ 1` (C14). Tonelli on the product.
2. *Unfolding.* `|g|² y^s` is `T`-periodic and integrable on the strip; the corpus unfolding
   `Σ_v ∫_𝒟 φ(M_v z) = 2∫_strip φ` with `φ(M_v z) = |g(z)|² Im(M_v z)^s` and absolute summability gives (1)'s left
   side `= 2∫_strip |g|² y^s`.
3. *Fubini on the strip:* `∫_strip |g|² y^s = ∫_0^∞ m(y) y^{s−2} dy`.
4. *Modes.* `m(y) = Σ_n |a_n(y)|²` and `|a_n(y)|² = |ρ(n)|² y K_ν(2π|n|y)²` (`K_ν` real for imaginary `ν`).
   Dominated convergence (bound `y^{σ−2}|a_n|²`, sum `y^{σ−2}m`) exchanges sum and integral.
   `∫_0^∞ y^{s−1}K_ν(cy)²dy = c^{−s}∫_0^∞ x^{s−1}K_ν(x)²dx = c^{−s}G(s)` (substitution; corpus two-K Mellin product).
5. For `Re s > 1`, `Im s ≠ 0`, `E(s − ½) = ½ Σ_v Im(M_v z)^s` (corpus); `(2π|n|)^{−s} = (2π)^{−s}|n|^{−s}`,
   `2^{s−3}(2π)^{−s} = π^{−s}/8`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheRankinSelbergIntegralOfTheCuspModes.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages. Axioms of `rankinSelberg_eisenstein`:
`propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspRSI`) |
|---|---|
| 1 | `integral_Ico_eq_slice`, `integrableOn_slice_weight`, `stripChart_rsStrip`, `integrableOn_rsStrip` |
| 2–3 | `two_mul_strip_eq`, `strip_eq_mellin` |
| 4 | `K_real`, `integral_scaled_KK`, `hasSum_mellin_slice`, `gammaFactor` |
| (1), (2) | `rankinSelberg_rowSum`, `rankinSelberg_eisenstein` |

## Scope
The Rankin–Selberg series of a cusp mode is the Eisenstein coefficient of its energy density in the convergent
range. Not formalized: holomorphy of `u ↦ ∫_𝒟 |g|²E(u; ·)` (needs locally uniform bounds of `E` in `u` on `𝒟`), hence
the meromorphic continuation of `Σ|ρ(n)|²|n|^{−s}` and the location of its poles at `s = 1` and the zeros of `ξ(2s)`.

## Log
- 2026-11-08 — created and formalized.
