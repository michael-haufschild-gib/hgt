# TG — Gaussian-filtered central gap: height localization and light cone

- **ID:** TG-LC-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional expansion; RH criterion)
- **Statement:** F(ε,τ) = ∫_{u>0} G(u) exp(−(u−2ε)²/(2ε) − iτ(u−2ε)) du (G = central Gaussian gap in log scale).
  (a) ‖F(ε,τ) + √(2πε) Σ_ρ ½Γ((ρ−½)/2) e^{−ε w_ρ(τ)}‖ ≤ C(√(2πε) + e^{−2ε}), uniformly in τ, with
      w_ρ(τ) = −(2a + (a−iτ)²/2), a = (ρ−½)/2.
  (b) Re w = −((β−½) + ((β−½)²/4 − (γ/2−τ)²)/2): ≥ 0 for critical zeros; < 0 for an off-line zero at
      height 2τ; the light cone {Re w < 0} at fixed τ is finite; w determines ρ.
  (c) RH ⟺ ∀τ ∃C ∀ε ≥ 1: ‖F(ε,τ)‖ ≤ C√ε.

## Proof
Unconditional zero expansion (cycle 19) + bounded remainder on u>0; Gaussian integral of e^{au}·kernel over ℝ by
integral_cexp_quadratic = √(2πε)e^{ε(2a+(a−iτ)²/2)}; left tail ≤ e^{−2ε}; interchange by summable integral norms
(amplitudes ‖½Γ‖ summable, e^{u/4}-weighted window integrable). (c ⇐) corpus light-cone amplification
(HTGeometry/GaussianLightConeAmplification) at τ = Im ρ₀/2.

## Lean
`RHTower/GaussianCentralGapFilterLightCone.lean` (639 lines), wired after GaussianTopologicalGateTerminalState.
`exists_norm_filteredGap_add_zeroSeries_le`, `xiZero_eq_of_zeroLightConeExponent_eq`, `zeroBohrAmplitude_ne_zero`,
`riemannHypothesis_iff_filteredCentralGap_isBigO`. Axioms [propext, Classical.choice, Quot.sound].

## Reading
Unifies TG with the HCF light-cone receiver: a Gaussian window in the scale variable turns the Γ-damped TG gap into a
height-localized reader of zeros near 2τ, amplifying an off-line zero by exp(ε((β−½)+(β−½)²/8)). The producer target
is again an O(√ε) bound uniform in the window — wall 1 in HCF form; TG and HCF share one terminal producer.
