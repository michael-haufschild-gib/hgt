# The energy estimate for the clock equation

- **ID:** hyperbolic-energy-estimate
- **Stage:** 3-formalized
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
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized — four modules, every theorem unconditional
      (`[propext, Classical.choice, Quot.sound]`)
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
| 11 | the flux bound and the Grönwall estimate | `energyDensity_nonneg`, `waveEnergy_nonneg`, `integrable_energyDensity_slice`, `abs_integral_flux_le`, **`waveEnergy_le_exp`** | **built** |
| 12 | vanishing of a solution with zero initial energy | `energyDensity_eq_zero_of_waveEnergy_eq_zero`, **`eq_zero_of_waveEnergy_zero`** | **built** |
| 13 | linearity of the equation and uniqueness for the Cauchy problem | `dirDeriv_sub`, `solvesWaveEq_sub`, `waveEnergy_eq_zero_of_slice_zero`, **`eq_of_solvesWaveEq_of_data_eq`** | **built** |
| 14 | time-reflection invariance and two-sided uniqueness | `timeReflect`, `dirDeriv_comp_timeReflect`, `solvesWaveEq_comp_timeReflect`, **`eq_of_solvesWaveEq_of_data_eq_all`** | **built** |
| 15 | the estimate on both sides, and continuous dependence | `energyDensity_comp_timeReflect`, `waveEnergy_comp_timeReflect`, **`waveEnergy_le_exp_abs`**, **`waveEnergy_sub_le_exp_abs`** | **built** |
| 16 | the solutions of a fixed equation form a vector space | `dirDeriv_const_smul`, **`solvesWaveEq_add`**, **`solvesWaveEq_const_smul`**, `solvesWaveEq_zero` | **built** |

Modules: `WaveEnergyGreenIdentity.lean` (1–3), `WaveDirectionalCalculus.lean` (4–5),
`WaveEnergyFlux.lean` (6–9), `WaveEnergyDerivative.lean` (10–12), `WaveCauchyUniqueness.lean` (13), `WaveTimeReflection.lean` (14), `WaveEnergyTwoSided.lean` (15), `WaveSolutionSpace.lean` (16). All wired into the umbrella; axioms
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

Statements 11 and 12 close it. The flux is dominated by the energy,
`|2∫(V+1)·u·∂ₜu| ≤ (M+1)·E(t)` whenever `|V| ≤ M` — pointwise from `2|ab| ≤ a²+b²` and the fact that
the energy density dominates `u² + (∂ₜu)²` — so Grönwall gives

**`waveEnergy_le_exp`**: `E(t) ≤ E(0)·exp((M+1)·t)` for `t ≥ 0`,

and hence **`eq_zero_of_waveEnergy_zero`**: a solution whose energy vanishes at time `0` vanishes at
every later time. A nonnegative continuous integrand with vanishing integral is identically zero
(`Continuous.ae_eq_iff_eq` on a measure of full support), and the energy density dominates `u²`.

Statement 13 puts it in the form an inverse problem uses. The equation is linear
(`solvesWaveEq_sub`), a field vanishing on a slice together with its time derivative has zero energy
there (`waveEnergy_eq_zero_of_slice_zero`), and hence **`eq_of_solvesWaveEq_of_data_eq`**: *two
classical solutions with spatially compact support, the same bounded potential and the same Cauchy
data agree at every later time.*

Statement 14 removes the sign restriction. Only the *second* time derivative enters the equation, so
reflecting an event across the initial slice carries a solution of `V` to a solution of the
reflected potential (`solvesWaveEq_comp_timeReflect`), and uniqueness for `t ≥ 0` gives
**`eq_of_solvesWaveEq_of_data_eq_all`**: the two solutions agree at *every* time.

Statement 15 closes the layer symmetrically. The energy density is even in the time derivative, so
reflection turns the forward estimate into `E(t) ≤ E(0)·exp((M+1)|t|)`
(**`waveEnergy_le_exp_abs`**), and applying that to the difference of two solutions gives
**`waveEnergy_sub_le_exp_abs`**: *the energy of the difference at any time is controlled by the
energy of the difference of the Cauchy data.* That is continuous dependence — uniqueness in
quantitative form.

Statement 16 records what superposition arguments consume: the solutions of a fixed clock equation
are closed under sums, scalar multiples and differences, with the zero field a solution.

This is the uniqueness half of the classical local theory, in exactly the class the clock programme
uses: real classical solutions with spatially compact support. What it does *not* give is existence;
that is the Galerkin or Sobolev-scale half, and it is what would lower the regularity threshold of
`finite-regularity-clock-probes` below `C^{2d+5}`.

### The next brick

The natural next step is the **bridge to the corpus's Fourier-built probes**: identifying
`SolvesWaveEq u V` on `ℝ × (Fin d → ℝ)` with the corpus's `SolvesPotentialWaveAt (kgWaveOp d) V u`
on `Fin (d+1) → ℝ`. It needs two translations — the index shift `Fin (d+1) ↔ ℝ × Fin d`
(`kgEventInvCLM`, `kgSpatial`) and the change of norm between `Fin d → ℝ` and
`EuclideanSpace ℝ (Fin d)` (the two carry the same volume, `EuclideanSpace.volume_preserving_measurableEquiv`).
With it, every probe the corpus constructs by Fourier synthesis inherits the uniqueness and
stability statements above.

The expansion of the corpus operator is already available and is the entry point:
`kgWaveOp d = (SmoothPseudoMetric.ofSignature (kgEps d) (kgEps_ne_zero d)).chart.dalembert`, and
`SmoothPseudoMetric.ofSignature_dalembert_of_differentiableAt` rewrites it as
`∑ᵢ (kgEps d i)⁻¹ · ∂ᵢ∂ᵢu` under a differentiability hypothesis. With `kgEps d 0 = -1` and
`kgEps d i.succ = 1`, splitting that sum by `Fin.sum_univ_succ` gives exactly the shape of
`SolvesWaveEq`; what is left is the coordinate dictionary `coordPartial 0 ↔ dirDeriv (timeDir d)`
and `coordPartial i.succ ↔ dirDeriv (spaceDir d i)` along the linear map
`(t, x) ↦ Fin.cons t x`.

## Log
- 2026-08-04 — statement 16 (linearity of the solution space) formalized.
- 2026-08-04 — statement 15 (two-sided estimate, continuous dependence) formalized.
- 2026-08-04 — statement 14 (time reflection, two-sided uniqueness) formalized.
- 2026-08-04 — statement 13 (linearity and Cauchy uniqueness) formalized.
- 2026-08-04 — statements 11–12 formalized; the card is complete and moves to 3-formalized.
- 2026-08-04 — statement 10 (differentiation under the integral) formalized; 11–12 remain.
- 2026-08-04 — statement 9 (the flux identity) formalized; 10–12 remain.
- 2026-08-04 — statements 1–8 formalized in three modules (Green identity, directional calculus,
  pointwise flux expansion); 9–12 remain.
- 2026-08-04 — created in 1-in-progress; mathlib inputs verified present
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, `norm_le_gronwallBound_of_norm_deriv_right_le`).
