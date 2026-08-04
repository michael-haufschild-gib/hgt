# The energy estimate for the clock equation

- **ID:** hyperbolic-energy-estimate
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** child of `two-species-conformal-clock-scale-law`; the "hyperbolic energy theory, which
  mathlib does not have" named in the closing note of `finite-regularity-clock-probes`
- **Statement:** For a classical solution of `∂ₜ²u = Δu + Vu` with a bounded potential and uniformly
  compact spatial support, the energy `E(t) = ∫ (∂ₜu)² + |∇u|² + u²` satisfies
  `E(t) ≤ E(0)·exp((‖V‖_∞+1)|t|)`. Consequently the Cauchy problem has at most one such solution.

## Goal

Every probe construction in the corpus is an *existence* argument by Fourier synthesis, and each one
buys its solution at the price of derivatives: the Wiener route needs the potential's Fourier density
in a weighted `L¹`, which for a `C^k` potential costs `k > 2d+4`. The route that does not pay that
price is the energy method — the estimate that controls a solution by its data with no Fourier
transform at all. mathlib has no hyperbolic energy estimate, and the corpus has only its
one-dimensional shadow (`HillOscillatorEnergy`).

This card builds the estimate itself. It is the first half of the classical local theory: the
estimate gives uniqueness and the quantitative control on which any future existence proof (Galerkin,
or a fixed point in a Sobolev scale) rests, and it is stated for exactly the class of solutions the
clock programme uses — classical, real, with spatially compact support.

## The computation

With `∂ₜ²u = Δu + Vu`,

```
E'(t) = 2∫ (∂ₜu·∂ₜ²u + ⟨∇u, ∇∂ₜu⟩ + u·∂ₜu)
      = 2∫ (∂ₜu·(Δu + Vu) + ⟨∇u, ∇∂ₜu⟩ + u·∂ₜu)
      = 2∫ ((V+1)·u·∂ₜu)                                   [integration by parts]
      ≤ (‖V‖_∞+1)·E(t),
```

the middle step being `∫⟨∇u, ∇∂ₜu⟩ = -∫ Δu·∂ₜu`, valid because the spatial support is compact. The
last step is `2|ab| ≤ a² + b²`. Grönwall closes it.

## Approach

1. **Supports.** A function vanishing off a compact `K` for every time has all its partial
   derivatives vanishing off `K`; hence every integrand below is continuous with compact support,
   so integrable.
2. **Integration by parts.** mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` gives
   `∫ ∂ᵢf·g = -∫ f·∂ᵢg` in a fixed direction for integrable data. Summing over an orthonormal
   family gives the Green identity used above.
3. **Differentiation under the integral.** `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
   the dominating function supplied by continuity on a compact time interval times `K`.
4. **Grönwall.** `norm_le_gronwallBound_of_norm_deriv_right_le`, and its `f a = 0` corollary for
   uniqueness.

## Gates

- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Numbered statements

| # | statement | Lean name | state |
|---|---|---|---|
| 1 | supports of a coordinate partial derivative | `coordPartial_eq_zero_of_eventually`, `hasCompactSupport_coordPartial` | **built** |
| 2 | integration by parts on a spatial slice | `integral_mul_coordPartial` | **built** |
| 3 | the Green identity `∫(∑∂ᵢ∂ᵢf)·g = -∑∫∂ᵢf·∂ᵢg` | `integral_laplacian_mul` | **built** |
| 4 | directional derivatives of a field of events: smoothness, supports, slice bridges | `dirDeriv`, `contDiff_dirDeriv`, `dirDeriv_eq_zero_of_notMem`, `dirDeriv_timeDir_eq`, `dirDeriv_spaceDir_eq` | **built** |
| 5 | symmetry of the mixed second derivative | `dirDeriv_comm` | **built** |
| 6 | the clock equation and the energy density | `SolvesWaveEq`, `energyDensity` | **built** |
| 7 | product/sum rules for a directional derivative | `dirDeriv_mul`, `dirDeriv_sq`, `dirDeriv_add`, `dirDeriv_sum` | **built** |
| 8 | the pointwise expansion of `∂ₜ(energy density)` | `dirDeriv_energyDensity` | **built** |
| 9 | the flux identity `∫∂ₜ(energy density) = 2∫(V+1)·u·∂ₜu` | `integral_dirDeriv_energyDensity` (with `slice`, `contDiff_slice`, `hasCompactSupport_slice`, `dirDeriv_zero_of_notMem`) | **built** |
| 10 | differentiation under the integral | `waveEnergy`, `hasDerivAt_waveEnergy` (with `hasDerivAt_timeSlice`, `contDiff_energyDensity`, `energyDensity_zero_of_notMem`, `hasCompactSupport_energyDensity_slice`) | **built** |
| 11 | the Grönwall estimate | — | next |
| 12 | uniqueness for the Cauchy problem | — | next |

Modules: `WaveEnergyGreenIdentity.lean` (1–3), `WaveDirectionalCalculus.lean` (4–5),
`WaveEnergyFlux.lean` (6–9), `WaveEnergyDerivative.lean` (10). All wired into the umbrella; axioms
`[propext, Classical.choice, Quot.sound]`.

## State of the build

Statements 1–9 are complete, and 9 is the mathematical heart:

`∫ ∂ₜ(energy density) = 2 ∫ (V+1)·u·∂ₜu`

for a smooth field with spatial support in a fixed compact set solving `∂ₜ²u = Δu + Vu`. The two
derivative terms cancel exactly — the equation turns `∂ₜu·∂ₜ²u` into `∂ₜu·(Δu+Vu)`, `dirDeriv_comm`
turns `∑ᵢ∂ᵢu·∂ₜ∂ᵢu` into `∑ᵢ∂ᵢu·∂ᵢ∂ₜu`, and `integral_laplacian_mul` identifies the latter with
`-∫Δu·∂ₜu`. No derivative of `u` survives on the right, which is exactly what makes the estimate
closed.

Statement 10 is also complete: `hasDerivAt_waveEnergy` differentiates the energy under the integral
sign, the domination being `Set.indicator K (fun _ => C)` with `C` the supremum of the continuous
time derivative of the energy density on the compact `Icc (t-1) (t+1) ×ˢ K`.

What remains (11–12):

* combine 9 and 10 into `E'(t) = 2∫(V+1)·u·∂ₜu`, bound it pointwise by
  `2|(V+1)·u·∂ₜu| ≤ (M+1)·(u² + (∂ₜu)²) ≤ (M+1)·(energy density)` for `|V| ≤ M`, integrate
  (`norm_integral_le_integral_norm` and monotonicity), and apply
  `norm_le_gronwallBound_of_norm_deriv_right_le` with `ε = 0` to get
  `E(t) ≤ E(0)·exp((M+1)t)` for `t ≥ 0`;
* uniqueness: the difference of two solutions solves the same linear equation, has zero energy at
  `t = 0`, hence zero energy for all `t ≥ 0`; a nonnegative continuous integrand with zero integral
  vanishes, and the energy density dominates `u²`.

## Log
- 2026-08-04 — statement 10 (differentiation under the integral) formalized; 11–12 remain.
- 2026-08-04 — statement 9 (the flux identity) formalized; 10–12 remain.
- 2026-08-04 — statements 1–8 formalized in three modules (Green identity, directional calculus,
  pointwise flux expansion); 9–12 remain.
- 2026-08-04 — created in 1-in-progress; mathlib inputs verified present
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, `norm_le_gronwallBound_of_norm_deriv_right_le`).
