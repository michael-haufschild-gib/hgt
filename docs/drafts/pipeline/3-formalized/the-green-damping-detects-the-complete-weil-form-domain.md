# Green damping detects the complete Weil form domain

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: identify the closed form behind the arithmetic Green construction.

## Statement

For `f ∈ L²([-a,a]; ℂ)`, extended by zero, define

`J_r(f) = ∫₀∞ K_r(t) ‖f(·+t)−f‖₂² dt`,
`K_r(t) = exp(−t/2)/(1−r² exp(−2t))`, `0 ≤ r < 1`.

Every `J_r` is finite and continuous on physical `L²`. As `r ↑ 1`,
`J_r(f)` increases to an extended energy `J(f) ∈ [0,∞]`. Its exact domain is

`J(f) < ∞ ↔ f ∈ range(CCMArchimedeanFormToAperture a)
             ↔ HasLogarithmicEnergy f`.

If this condition fails, `J_r(f) → +∞`. If it holds and `f = J_a u`, then

`J(f) + ‖f‖₂² = ‖u‖_form²`.

Consequently the saturated Green expression

`Q_r(f) = J_r(f) + 2 gammaHardyPhaseRate(0) ‖f‖₂²
          + Re⟨P_a f,f⟩ − Re⟨A_a f,f⟩`

converges to the literal closed Weil form on its entire domain and diverges
to `+∞` outside it. Here `P_a` and `A_a` are the existing polar and finite
von Mangoldt translation operators. No smoothness or positivity of Weil's
form is assumed.

## Proof

Write `D_f(t)=‖f(·+t)−f‖₂²`. Translation is strongly continuous and isometric,
so `D_f` is continuous and `0 ≤ D_f(t) ≤ 4‖f‖₂²`. Each strict damping `K_r`
is integrable. These bounds give finiteness of `J_r` and, on every bounded
neighborhood in `L²`, an integrable bound uniform in `f`; dominated convergence
gives continuity. Pointwise monotonicity of `K_r` gives monotonicity of `J_r`.

For `t>0`, `K_r(t) ↑ archLevyDensity(t)`. Fatou's lemma and the reverse upper
bound `K_r ≤ archLevyDensity` prove extended convergence, including infinite
limits. This step assumes no finite critical energy.

Aperture support makes `f` integrable as well as square integrable. The corpus's
extended Gamma–Lévy identity and Plancherel therefore give

`J(f) = ∫ 2(γ'(2πξ)−γ'(0)) |Fourier(f)(ξ)|² dξ`

as an identity in `[0,∞]`. Since the complete Fourier weight is
`1+2(γ'(2πξ)−γ'(0))`, its extended weighted energy is exactly
`‖f‖₂²+J(f)`. The established equality of logarithmic and Gamma form domains,
and the established aperture range characterization, prove the stated domain
criterion. On an actual form vector, the weighted integral is its form norm.

The existing bounded remainder is
`B_a=(2γ'(0)−1)I+P_a−A_a`. Thus
`Q_r(f)=J_r(f)+‖f‖₂²+Re⟨B_a f,f⟩`.
For `f=J_a u`, the limit is `‖u‖_form²+Re⟨B_a J_a u,J_a u⟩`, exactly
`(ccmRestrictedWeilForm a u u).re`. The fixed bounded remainder cannot cancel
infinite critical energy. Uniqueness of limits in `[0,∞]` gives the converse:
existence of any finite Green limit forces admission to the complete form domain.

## Lean declarations and verification

Module: `HyperbolicArakelovTheory/TheGreenDampingDetectsTheCompleteWeilFormDomain.lean`.
Namespace: `GaloisForLFunctions.HyperbolicArakelovTheory`.

- `integrable_greenJumpEnergy`, `continuous_greenJumpEnergy`, `greenJumpEnergy_le`:
  finite continuous strict-damping forms with a physical L² bound.
- `greenJumpEnergy_mono`, `tendsto_greenJumpEnergy_extended`:
  ordered convergence retaining infinite critical energies.
- `weighted_energy_eq_mass_add_green`, `criticalGreenEnergy_form_norm`:
  exact extended Fourier and complete form-norm identities.
- `finite_green_limit_iff_form_range`, `finite_greenWeil_limit_iff_form_range`:
  finite convergence characterizes the entire source-defined Weil form domain.
- `tendsto_greenWeilEnergy_form`, `tendsto_greenWeilEnergy_atTop`:
  literal closed-form limit inside the domain; divergence outside it.

Final plain `lake --old env lean
GaloisForLFunctions/HyperbolicArakelovTheory/TheGreenDampingDetectsTheCompleteWeilFormDomain.lean`:
PASS. Seven main dependency audits contain only
`[propext, Classical.choice, Quot.sound]`. Umbrella import added.

## Boundary

This identifies the exact domain and closed form of Green damping with saturated
arithmetic terms. It does not identify a single invariant torus Robin kernel
with Weil's diagonal. The accepted gluing obstruction remains in force.
Strong and norm resolvent convergence are not asserted.
