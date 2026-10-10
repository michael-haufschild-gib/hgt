# TG — Finite-range converse: every off-line zero breaks the budget at an explicit scale

- **ID:** TG-FR-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Statement:** ρ₀ = ½+δ₀+iγ₀ (δ₀>0) strictly maximizing Re ρ among zeros with |Im ρ − γ₀| < 4. ∃ g>0, ∃ absolute C:
  ∀ K≥0, ε≥1 with A e^{−εg} ≤ |c₀|/2 and K + C < (|c₀|/2)e^{ε(δ₀+δ₀²/8)} (c₀ = ½Γ((ρ₀−½)/2), A = Σ|½Γ((ρ−½)/2)|),
  the bound |G(u)| ≤ K fails somewhere on (0, 4ε].

## Proof
(1) |G(u)| ≤ C₁e^{u/4} unconditionally; budget on (0,4ε] + window tail beyond 4ε (≤ (4/3)C₁) ⇒ ‖F(ε,γ₀/2)‖ ≤ K√(2πε) + (4/3)C₁.
(2) Filtered zero expansion (cycle 31) ⇒ ‖Σ_q c_q e^{−εw_q}‖ ≤ K + 2C₀ + (4/3)C₁.
(3) Light-cone exponents at τ₀=γ₀/2: −Re w_q = δ_q + δ_q²/8 − (γ_q−γ₀)²/8; local strict maximality + |γ−γ₀|≥4 ⇒ ≤ Ψ₀ − g
    for q ≠ copies of ρ₀ (finite candidate set, Finset min). Copies of ρ₀ are equal terms (fiber finite, count ≥ 1):
    ‖Σ‖ ≥ e^{εΨ₀}(|c₀| − A e^{−εg}).

## Lean
`RHTower/GaussianCentralGapFiniteRangeConverse.lean` (404 lines), wired after GaussianCentralGapSimplicityGate.
`exists_abs_gaussianCentralGapLog_le_exp`, `norm_filteredCentralGap_le_of_budget`, `exists_lightCone_gap_of_localExtremalZero`,
`norm_lightConeSeries_ge`, `not_gaussianCentralGap_budget_of_localExtremalZero`. Axioms [propext, Classical.choice, Quot.sound].

## Reading
Completes the TG scale–height dictionary in both directions for locally extremal zeros: failure scale
4ε ≈ 4(log K + log(1/|c₀|) + log(2A/|c₀|)·Ψ₀/g)/Ψ₀ ≈ (4 log K + π|γ₀|)/δ₀ when the local gap g is not tiny.
Ties/clusters (non-strict local maxima) remain the Pintz/Turán case.

## Cycle 36: every off-line zero (no separation, no simplicity)
**Statement** (`not_gaussianCentralGap_budget_of_offLineZero`): for any zero ρ₀ with δ₀ > 0 there are a centre
τ ∈ [γ₀/2, γ₀/2 + √Ψ₀/2], a zero ρ₁, a gap g > 0 and an absolute C with E_{ρ₁}(τ) ≥ Ψ₀/2 such that |G| ≤ K fails
on (0, 4ε] once A e^{−εg} ≤ |c₁|/2 and K + C < (|c₁|/2)e^{εE_{ρ₁}(τ)}.
**Mechanism:** E_ρ(τ) = Ψ(δ) − (γ − 2τ)²/8 is a downward parabola with vertex γ/2. Distinct vertices ⇒ one
crossing (`lightCone_tie_eq`); equal vertices + equal values ⇒ equal δ (`lightCone_psi_injective`). Pick τ in
the interval off the finite crossing set of the zeros with ‖ρ−½‖ ≤ ‖ρ₀−½‖+6 (`Set.Icc_infinite`,
`exists_notMem_finset`); the maximizer is unique up to copies; zeros outside are negative
(`neg_re_zeroLightConeExponent_neg_of_far`); uniform gap via `exists_uniform_gap_of_finite`.
**Reading:** ties among equal real parts (the Turán/Pintz cluster obstruction for power sums) do not arise
for the Gaussian light cone: the exponent depends on height quadratically, so a generic centre separates.
Effective constants (g, |c₁|) are not explicit — the converse is qualitative in g.
