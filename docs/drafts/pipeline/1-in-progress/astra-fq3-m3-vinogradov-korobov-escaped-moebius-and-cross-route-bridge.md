# Unconditional Escaped Möbius Decay, Vinogradov–Korobov Rate, and Cross-Route Synthesis

**Stage:** `1-in-progress`
**Category:** `RH-core`
**Created:** 2026-10-27
**Updated:** 2026-10-27

## Statement
Deliver Milestone 3 of Focus Question 3 (`GrowingEndpointEscapedMoebiusLaw θ` & Escaped Boundary Laws) unconditionally:
1. **Unconditional Uniform Growing-Endpoint Escaped Möbius Vanishing:** For every `ε > 0`, there exists `M₀ : ℕ` such that for **all** horizons `N : ℕ`, multipliers `a ≥ 1`, and shifts `b ≤ N` with `M₀ ≤ (N - b) / a`,
   $$|\operatorname{escapedPairing}\; N\; a\; b\; (\operatorname{moebiusSource}\; N)\; (\operatorname{flatSource}\; N)| \le \varepsilon.$$
2. **Unconditional Quantitative Vinogradov–Korobov Escaped Möbius Bound (Zero Octave-Loss):** Using `exists_abs_sum_moebius_le_vk_rate` and a telescoping antiderivative `G(x) = exp(-(vkKappa / 48) * vkScale x)` across arbitrary `M₂ ≥ M₁`, there exist `C > 0` and `M₀ : ℕ` such that for **all** `N, a, b` with `1 ≤ a`, `b ≤ N`, and `M₀ ≤ (N - b) / a`,
   $$|\operatorname{escapedPairing}\; N\; a\; b\; (\operatorname{moebiusSource}\; N)\; (\operatorname{flatSource}\; N)| \le C \exp\!\left(-\frac{\kappa}{48}\, \sigma\!\left(\frac{N - b}{a}\right)\right).$$
3. **Unconditional Trans-Horizon Gauge/Flat Selectivity:** By contrast, at dyadic escape (`a = 2, b = 0`), `escapedPairing N 2 0 (flatSource N) (flatSource N) ≥ 1 / 2` for every `N ≥ 2`, proving unconditional trans-horizon separation between `moebiusSource` (`→ 0` at Vinogradov–Korobov rate) and `flatSource` (`≥ 1/2`).
4. **Master Cross-Route Unification Law:** Unify `GrowingEndpointEscapedMoebiusLaw θ`, `DyadicEscapedMoebiusLaw θ`, `zetaZeroAbscissa ≤ 1 - θ`, `BVI`'s `CentredPrimeBand (1 - θ)` / `receiverDampingRate`, and `TTPC`'s coalescent resonance threshold `θ(λ) = (λ - 1) / (2λ)` (`θ(4/3) = 1/8`, `θ(5/4) = 1/10`, `lim_{λ → ∞} θ(λ) = 1/2⁻ ⟹ RH`).

## Idea
Combine `sum_Ioc_moebius_div_eq_mertens_abel` with `deningerAbelCoefficient_summable` (for uniform convergence) and with the convexity/derivative comparison `-d/dx exp(-(κ/48) σ(x)) ≥ (1/(k+1)) exp(-(κ/24) σ(k))` (for telescoping the Abel tail over arbitrary `M₂ ≥ M₁` without losing `log(M₂/M₁)`).

## Dependencies
- `SelectivePositivityAndThresholdLaws/MoebiusEscapedPairingBoundaryLaw.lean`
- `RHTower/Deninger/DeningerMobiusHarmonic.lean`
- `BezoutValuationIncidence/ReceiverBoundedInTheVinogradovKorobovBand.lean`
- `BezoutValuationIncidence/TheCentredPrimeBandIsTheQuasiRiemannHypothesis.lean`

## Proof
See `logs/astra-2710-research.log` Part VI (Milestone 3).

## Audit
- [x] Proof complete (no gaps)
- [x] Dependencies verified
- [x] Checked against kills (`docs/reports/rh-killed-routes.md`)
- [ ] Formalised in Lean 4

## Lean
- Target: `formal/GaloisForLFunctions/BezoutValuationIncidence/UnconditionalEscapedMoebiusDecayAndCrossRouteBridge.lean`
- Umbrella: `formal/GaloisForLFunctions/BezoutValuationIncidence.lean`
