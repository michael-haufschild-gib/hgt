# BHR — the ringdown rate of a pulse is the zero-free strip; the two horizon rates are one exponent

- **ID:** bhr-ringdown-rate-zero-free-strip
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0711 §2.10, "Explain the two RH rates, `e^{−t/4}` for resonant decay and `y^{3/4}` for horocycle
  thermalization, which read the same poles `ρ/2`"; B71.
- **Statement:** Let `𝓕_h(τ, z) = Π_h(τ, z) − 6a(−i/2)e^{τ/2}` be the image field of a compact pulse with its mean growth
  removed. For `0 < δ ≤ 1/4`:
  1. every zero of `ζ` with `Re ρ > 0` has `Re ρ ≤ 1 − 2δ` ⟺ for every pulse, point and `ε > 0`, `𝓕_h(τ, z) = O(e^{−(δ−ε)τ})`;
  2. RH ⟺ every pulse rings down at `e^{−(1/4−ε)τ}` for every `ε > 0`;
  3. (with `CountingHolography.zeroFreeStrip_iff_fareyCount_rate`) every pulse rings down at `e^{−(δ−ε)τ}` ⟺ every
     horocycle mean of a pseudo-Eisenstein series converges at `y^{1/2+δ−ε}`, for every `ε > 0`.

## Paper proof
**Forward.** `𝓕_h(τ) = ∫ a(ξ)E(iξ)e^{iξτ}dξ` (`pulseField_eq_packet`). Fix `0 < σ < δ`. On `−σ ≤ Re u ≤ 0`,
`ξ(1+2u) ≠ 0` (`Re(1+2u) ≥ 1−2σ > 1−2δ`). The three-circles bound in the zero-free half-plane gives
`|ζ(1+2u)|⁻¹ ≤ (2/κ)(1+|Im u|)` for `|Im u| ≥ 3`, so `E(u) = O((1+|Im u|)^M)` there; the rapid amplitude gives
`|a(−iu)E(u)| ≤ B/(1+Im²u)` on the strip, a compact box handling `|Im u| ≤ 3`. Shift the line to `Re u = −σ`:
`|𝓕_h(τ)| ≤ e^{−στ}·Bπ`.

**Converse.** Fix a zero `ρ`, `Re ρ > 1−2δ`, and `p = (ρ−1)/2`, so `−δ < Re p < 0`. Take the exciting pulse `h` and a point
`x` at height `1` with `a(−ip)N(p; x, 1) ≠ 0`.
1. *Causality.* Every image of a point of height `Y` has height `≤ max(Y, 1/Y)`, so `Π_h(τ) = 0` for `τ ≤ −T`.
2. *Laplace transform.* For `Re w > ½`, `∫ e^{−wτ}Π_h(τ)dτ = 2πa(−iw)E(w)`: the row `γ` contributes
   `y_γ^{½+w}∫h(S)e^{−wS}dS`, the sum is absolutely convergent, and `½Σ y_γ^{½+w}` is the Eisenstein series.
3. *Continuation.* `|𝓕_h| ≤ Ce^{−δτ}` on `τ > −T`, so `ℒ(w) = ∫_{τ>−T} e^{−wτ}𝓕_h` is holomorphic on `Re w > −δ`
   (half-line Laplace transform of an `L²` datum after the shift `e^{−s₀σ}`). Splitting step 2 at `−T`:
   `2πa(−iw)E(w) = ℒ(w) − m e^{(w−½)T}/(½−w)` on `Re w > ½`.
4. *Identity theorem.* `Φ₁ = ξ(1+2w)((2w−1)ℒ(w) + 2me^{(w−½)T})` and `Φ₂ = 2πa(−iw)·(2w−1)N(w)` (the latter entire)
   agree on `Re w > ½`, `Im w > 0`, hence on `Re w > −δ`. At `p`, `Φ₁(p) = 0`, so `a(−ip)N(p) = 0`: contradiction.

**One exponent.** (1) and the Farey reading of the horocycle (`zeroFreeStrip_iff_fareyCount_rate`,
`horocycle_rate_iff_fareyCount_rate`) at the same `δ`. The pole `ρ/2` of the Eisenstein series is the time mode
`e^{(ρ−1)τ/2}` and the space mode `y^{1−ρ/2} = y^{½}·e^{−(1−ρ)/2·log(1/y)}`: the long horocycle is the unit horocycle
pushed for time `log(1/y)`, with the length factor `y^{½}`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheRingdownRateIsTheZeroFreeStrip.lean` and
`TheTwoRatesOfTheHorizonAreOneExponent.lean`, wired into `BlackHoleRingdown.lean`, checked with `lake --old env lean`, no
messages. Axioms of `zeroFreeStrip_iff_pulse_ringdown`, `riemannHypothesis_iff_pulse_ringdown`,
`pulse_ringdown_iff_horocycle_rate`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.RingdownRate` unless noted) |
|---|---|
| Causality | `rowHgt_le`, `imageField_eq_zero_of_le` |
| Laplace transform of `Π_h` | `imageTerm_mul_exp`, `integral_exp_mul_imageField` |
| Holomorphy of Laplace transforms | `setIntegral_Ioi_shift`, `integrableOn_exp_mul_of_bound`, `differentiableOn_laplace` |
| Converse | `entireNumerator`, `entireNumerator_eq`, `re_le_of_pulse_ringdown` |
| Forward | `differentiableAt_normalizedEisenstein`, `xi_ne_zero_of_zeroFree`, `exists_amplitude_eisenstein_le`, `pulseField_decay_of_zeroFree` |
| (1), (2) | `zeroFreeStrip_iff_pulse_ringdown`, `riemannHypothesis_iff_pulse_ringdown` |
| (3) | `BlackHoleRingdown.pulse_ringdown_iff_horocycle_rate` |

## Scope
The rate is for the image field `Π_h` on the horizon; the black-hole fields are `e^{−3τ/2}` and `e^{−τ/2}/r` lifts of it.
Unconditionally (`δ → 0`) the theorem gives no exponential rate: the classical zero-free region gives no strip.

## Log
- 2026-11-08 — created and formalized.
