# Integrable functional-equation defect at unit density

- **ID:** integrable-fe-defect-at-unit-density
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Γ74
- **Statement:** A discrete positive spectrum beginning at 1, with atom masses at least 1 and pole residue at most 1, is the positive-integer counting measure whenever its Riemann functional-equation defect is integrable.

## Mathematical target

Let `1 = λ₀ < λ₁ < …`, `aₙ ≥ 1`, and `Σ aₙ/λₙ² < ∞`. The completed Dirichlet transform has the same strip regularity as the existing Hamburger receiver. Write its pole term as `β Γℝ(s−1)`, so the Dirichlet residue is `2β`. Assume `β` real and `β ≤ 1/2`. An integrable uncompleted defect forces `β = 1/2`, `λₙ = n+1`, and `aₙ = 1`.

## Paper proof [PROVED HERE]

The existing critical-line inverse Mellin formula gives
`θ(x)=x⁻¹/²θ(1/x)−β+βx⁻¹/²+K_g(x)`.
Its Laplace transform is `L(z)=F(z)−β/(πz)+β+J_g(z)`, where
`L(z)=Σ aₙz/[π(λₙ²+z²)]` and `F(z)=Σ aₙe^(−2πλₙz)`.

The existing kernel estimate gives `|J_g(z)|≤(3/2π)|z|⁻¹/²‖g‖₁`.
For `z=ε+iτ`, `|z|≥ε`, so `|εJ_g(z)|≤(3/2π)√ε‖g‖₁→0`, uniformly in real `τ`.
The absolutely convergent partial-fraction series has radial residue zero at zero and at
positive non-frequencies separated from the spectrum, and residue `aₙ/(2π)` at `iλₙ`.
Consequently `C_τ(ε)=εΣaₙe^(−2πλₙε)cos(2πλₙτ)` tends to `β/π` at zero,
`aₙ/(2π)` at an atom, and zero in a spectral gap. Since `C_τ≤C_0`,
`1≤aₙ≤2β≤1`; thus `aₙ=1` and `β=1/2`.

For a complex pole coefficient, the stronger complex limit `εF(ε)→β/π` forces
`β` to be real, since every value on the positive real ray is real.

For `K=⌊λₘ⌋` and `f=λₘ−K`, the cosine inequality gives
`C_0−C_f≤2(C_0−C_λₘ)+2K²(C_0−C_1)→0`.
If `0<f<1`, the gap below the first frequency instead gives `C_f→0`, a contradiction.
Every frequency is therefore integral. If a positive integer `k` were missing,
`C_k=C_0` termwise, while the spectral gap at `k` gives `C_k→0`, another contradiction.
Strict ordering now gives `λₙ=n+1`.

All analytic inputs are existing proved Mellin, Laplace and residue identities; the new step
is that an integrable defect leaves every radial residue unchanged.

This addresses the unit-density boundary. The possibility of larger pole residue remains outside this statement; Γ74 stays partially solved unless that case is resolved.

## Lean

`formal/GaloisForLFunctions/ArithmeticPositiveDuality/IntegrableDefectsAtUnitDensityAreRigid.lean`:

- `tendsto_mul_integrable_defectLaplace`: every radial defect residue vanishes.
- `tendsto_mul_freqDual_zero_of_theta_defect`: the complex Abel limit recovers the pole coefficient.
- `pole_coefficient_real_of_theta_defect`: the pole coefficient is real.
- `integer_spectrum_of_integrable_theta_defect`: theta-transform formulation.
- `integer_spectrum_of_integrable_critical_line_defect`: critical-line functional-equation formulation.

Direct `lake --old env lean` check passed. Wired into `ArithmeticPositiveDuality.lean`.
Axiom checks skipped as requested. Γ74 remains partially solved.
