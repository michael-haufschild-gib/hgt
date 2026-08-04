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
| 17 | the coordinate dictionary between time-space and event coordinates | `eventCLM`, `eventCLM_timeDir`, `eventCLM_spaceDir`, `waveDirDeriv_timeDir_two_comp_eventCLM`, `waveDirDeriv_spaceDir_two_comp_eventCLM` | **built** |
| 18 | the bridge to the corpus's clock operator | **`kgWaveOp_eq_of_contDiff`**, **`solvesWaveEq_comp_eventCLM`** | **built** |
| 19 | the converse and the equivalence of the two formulations | `eventCLM_surjective`, `solvesPotentialWaveAt_of_solvesWaveEq`, **`solvesWaveEq_comp_eventCLM_iff`** | **built** |
| 20 | uniqueness in the corpus's own language | `tail_eventCLM`, **`eq_of_solvesPotentialWave_of_data_eq`** | **built** |
| 21 | the Green identity without compact support | `integral_mul_coordPartial_of_integrable`, **`integral_laplacian_mul_of_integrable`** | **built** |
| 22 | the flux identity without compact support | **`integral_dirDeriv_energyDensity_of_integrable`** | **built** |
| 23 | differentiating the energy without compact support | **`hasDerivAt_waveEnergy_of_dominated`** | **built** |
| 24 | the estimate for a decaying solution | `DecayingSolution`, `abs_integral_flux_le_of_integrable`, **`waveEnergy_le_exp_of_decaying`** | **built** |
| 25 | vanishing for a decaying solution | `energyDensity_eq_zero_of_waveEnergy_eq_zero_of_integrable`, **`eq_zero_of_waveEnergy_zero_of_decaying`** | **built** |
| 26 | the hypothesis class is inhabited: compact support implies it | `hasCompactSupport_slice_dirDeriv`, **`decayingSolution_of_hasCompactSupport`** | **built** |
| 27 | time reflection and the two-sided estimate for decaying solutions | `coordPartial_neg_fun`, `slice_dirDeriv_comp_timeReflect`, **`DecayingSolution.comp_timeReflect`**, **`waveEnergy_le_exp_abs_of_decaying`** | **built** |
| 28 | two-sided vanishing for decaying solutions | **`eq_zero_of_waveEnergy_zero_of_decaying_all`** | **built** |
| 29 | the decaying uniqueness in the corpus's own language | **`eq_zero_of_solvesPotentialWave_of_decaying`** | **built** |
| 30 | the decay hypothesis is a genuine restriction | `solvesWaveEq_one_field`, `not_integrable_energyDensity_one_field`, **`not_decayingSolution_one_field`** | **built** |
| 31 | a square-integrability criterion for the decay hypotheses | **`decayingSolution_of_memLp_two`** | **built** |
| 32 | the criterion is closed under differences | `coordPartial_sub_fun`, `memLp_two_slice_sub`, **`memLp_two_slice_dirDeriv_sub`**, **`memLp_two_coordPartial_slice_sub`** | **built** |
| 33 | two-solution uniqueness for square-integrable solutions | `L2Solution`, **`L2Solution.sub`**, **`eq_of_solvesWaveEq_of_memLp`** | **built** |
| 34 | the same, in the corpus's own language | **`eq_of_solvesPotentialWave_of_memLp`** | **built** |
| 35 | domination by products of square-integrable functions | **`integrable_of_dominated_by_memLp_two`**, **`integrable_of_dominated_by_sum_memLp_two`** | **built** |
| 36 | the dominating function from factor-wise bounds | **`exists_bound_of_factor_memLp`** | **built** |
| 37 | factor-wise domination is closed under differences | `abs_sub_le_add`, **`exists_bound_of_factor_memLp_sub`** | **built** |
| 38 | uniqueness with every hypothesis on one solution at a time | `FactorDominated`, **`eq_of_solvesWaveEq_of_memLp_of_factorDominated`** | **built** |
| 39 | the same, in the corpus's own language | **`eq_of_solvesPotentialWave_of_memLp_of_factorDominated`** | **built** |
| 40 | continuous dependence in the square-integrable class | `decayingSolution_sub_of_memLp_of_factorDominated`, **`waveEnergy_sub_le_exp_abs_of_memLp`** | **built** |
| 41 | the inhomogeneous equation and its pointwise energy identity | `SolvesWaveEqSource`, `solvesWaveEqSource_zero`, `solvesWaveEq_of_solvesWaveEqSource`, **`waveDirDeriv_energyDensity_source`** | **built** |
| 42 | the energy dominates the `L²` norms of the field and its time derivative | **`integral_sq_dirDeriv_le_waveEnergy`**, **`integral_sq_le_waveEnergy`** | **built** |
| 43 | the integrated flux identity with a source | **`integral_dirDeriv_energyDensity_source`** | **built** |
| 44 | the source pairing is dominated by the energy | **`abs_integral_source_le`** | **built** |
| 45 | the inhomogeneous energy estimate | **`waveEnergy_le_gronwall_source`** | **built** |
| 46 | the algebra of bounded multiplication operators on `Lᵖ` | `lpBoundedMulCLM_comp`, `lpBoundedMulCLM_eq_id`, `lpBoundedMulCLM_add`, `lpBoundedMulCLM_eq_zero` | **built** |
| 47 | Plancherel as a continuous linear map, and the bounded Fourier multiplier | `fourierL2`, `fourierL2inv`, `norm_fourierL2_apply`, `fourierMulCLM`, **`norm_fourierMulCLM_le`**, `fourierMulCLM_comp`, `fourierMulCLM_eq_id`, `fourierMulCLM_eq_zero`, `fourierMulCLM_add` | **built** |
| 48 | strong continuity of a pointwise convergent family of uniformly bounded multipliers | `lintegral_enorm_rpow_two_ne_top`, **`tendsto_lpBoundedMulCLM_apply`**, **`tendsto_fourierMulCLM_apply`** | **built** |
| 49 | a uniformly bounded strongly continuous family of operators is jointly continuous | **`continuous_uncurry_of_strong`**, `continuous_of_strong_comp` | **built** |
| 50 | the symbols of the energy rotation and their regularity | `kgSinPhase`, `kgFreqInv`, `norm_kgSinPhase_le`, `norm_kgFreqInv_le`, `continuous_kgFreq`, `measurable_kgCosSymbol`, `measurable_kgSinPhase`, `measurable_kgFreqInv`, `continuous_kgCosSymbol_time`, `continuous_kgSinPhase_time` | **built** |
| 51 | the scalar propagators on `L²` | `kgCosOp`, `kgSinOp`, `kgFreqInvOp`, `norm_kgCosOp_le`, `norm_kgSinOp_le`, `norm_kgFreqInvOp_le`, **`continuous_kgCosOp_apply`**, **`continuous_kgSinOp_apply`**, `kgCosOp_zero`, `kgSinOp_zero` | **built** |
| 52 | the free propagator on the Hilbert energy space | `KGEnergy` (= `WithLp 2 (L² × L²)`), `kgPair`, `kgFst`, `kgSnd`, `kgRowOne`, `kgRowTwo`, `kgPropagator`, `norm_kgPropagator_le`, **`continuous_kgPropagator_uncurry`**, `continuous_kgPropagator_comp`, `kgPropagator_zero_apply` | **built** |
| 53 | the Volterra equation with a strongly continuous kernel | `StrongKernel`, `StrongKernel.of_continuous`, `continuous_volterraSolution_of_strong`, **`volterraSolution_eq_of_strong`**, **`volterra_eq_of_eq_of_eq_of_strong`**, **`norm_volterraSolution_le_of_strong`** | **built** |
| 54 | the potential as a bounded perturbation in energy coordinates | `kgPotentialOp`, **`norm_kgPotentialOp_le`** | **built** |
| 55 | the Duhamel data and its strong continuity | `kgFreeCurve`, `kgDuhamelKernel`, `norm_kgFreeCurve_le`, `norm_kgDuhamelKernel_le`, **`strongKernel_kgDuhamelKernel`** | **built** |
| 56 | **global well-posedness for a bounded measurable potential** | `kgMildSolution`, `continuous_kgMildSolution`, **`kgMildSolution_eq`**, **`kgMildSolution_zero`**, **`norm_kgMildSolution_le`**, **`eq_kgMildSolution_of_duhamel`**, **`exists_unique_kgMildSolution`** | **built** |
| 57 | the addition laws for the propagator symbols, and the group law | `lpBoundedMulCLM_neg`, `fourierMulCLM_neg`, `kgCosOp_eq`, `kgSinOp_eq`, **`kgCosOp_add`**, **`kgSinOp_add`**, **`kgPropagator_add`** | **built** |
| 58 | a multiplication or Fourier multiplier with a real symbol is self-adjoint on `L²` | **`inner_lpBoundedMulCLM_real`**, `inner_fourierL2`, **`inner_fourierMulCLM_real`**, `inner_kgCosOp`, `inner_kgSinOp` | **built** |
| 59 | the Pythagorean identity and the commutation, at the operator level | **`kgCosOp_sq_add_kgSinOp_sq`**, **`kgCosOp_comp_kgSinOp_comm`**, `norm_kgCosOp_sq_add_norm_kgSinOp_sq`, `inner_kgCosOp_kgSinOp_comm` | **built** |
| 60 | **exact conservation of the free Klein–Gordon energy** | `kgEnergy`, `kgEnergy_eq_norm_sq`, `kgEnergy_nonneg`, **`kgEnergy_kgPropagator`**, **`norm_kgPropagator_apply`**, **`norm_kgPropagator_le_one`** | **built** |
| 61 | **the energy estimate for the constructed solution** | **`kgEnergy_kgMildSolution_le`** | **built** |
| 62 | the multiplier algebra completed: difference and scalar multiple | `lpBoundedMulCLM_sub`, `lpBoundedMulCLM_smul`, `fourierMulCLM_sub`, `fourierMulCLM_smul` | **built** |
| 63 | the symbols of the regularised propagator and their difference quotients | `kgCosOverFreq`, `kgSinOverFreq`, `kgCosSlope`, `kgSinSlope`, `norm_kgCosSlope_le`, `norm_kgSinSlope_le`, `tendsto_kgCosSlope`, `tendsto_kgSinSlope` | **built** |
| 64 | the regularised propagators as multipliers, and their difference quotients | `kgCosOp_comp_kgFreqInvOp`, `kgSinOp_comp_kgFreqInvOp`, `slope_kgCosOp_freqInv`, `slope_kgSinOp_freqInv` | **built** |
| 65 | **the propagator is differentiable on regular data** | **`hasDerivAt_kgCosOp_freqInv`**, **`hasDerivAt_kgSinOp_freqInv`**, `kgRegular`, `kgPropagator_kgRegular`, **`hasDerivAt_kgPropagator_regular`** | **built** |
| 66 | the propagators commute with `⟨D⟩⁻¹` | `kgFreqInvOp_comp_kgCosOp`, `kgFreqInvOp_comp_kgSinOp`, `kgFreqInvOp_kgCosOp`, `kgFreqInvOp_kgSinOp` | **built** |
| 67 | the free field of a doubly regular datum, and its two derivatives | `kgFreeField`, `kgFreeVelocity`, **`hasDerivAt_kgFreeField`**, **`hasDerivAt_kgFreeVelocity`**, `deriv_kgFreeField`, `deriv_deriv_kgFreeField`, `kgFreeField_eq` | **built** |
| 68 | **the strong `L²` solution of the free Klein–Gordon equation** | **`kgFreeField_kleinGordon`**, `kgFreeField_zero`, `kgFreeVelocity_zero`, **`exists_kgFreeField`** | **built** |
| 69 | **energy conservation for the strong solution** | `kgFreeGradient`, `kgFreqInvOp_kgFreeGradient`, `kgPropagator_kgFreeState`, **`kgFreeField_energy_const`** | **built** |

Modules: `WaveEnergyGreenIdentity.lean` (1–3), `WaveDirectionalCalculus.lean` (4–5),
`WaveEnergyFlux.lean` (6–9), `WaveEnergyDerivative.lean` (10–12), `WaveCauchyUniqueness.lean` (13), `WaveTimeReflection.lean` (14), `WaveEnergyTwoSided.lean` (15), `WaveSolutionSpace.lean` (16), `WaveEventCoordinates.lean` (17), `WaveOperatorBridge.lean` (18–19), `WaveUniquenessEventForm.lean` (20), `WaveGreenIdentityIntegrable.lean` (21), `WaveEnergyFluxIntegrable.lean` (22), `WaveEnergyDerivativeIntegrable.lean` (23), `WaveEnergyDecaying.lean` (24–25), `WaveDecayingCompactSupport.lean` (26), `WaveDecayingReflection.lean` (27–28), `WaveDecayingEventForm.lean` (29), `WaveDecayingSharp.lean` (30), `WaveDecayingL2.lean` (31), `WaveDecayingL2Sub.lean` (32), `WaveL2Uniqueness.lean` (33), `WaveL2EventForm.lean` (34), `WaveDominationL2.lean` (35), `WaveDominationFactors.lean` (36), `WaveDominationSub.lean` (37), `WaveL2Capstone.lean` (38), `WaveL2CapstoneEvent.lean` (39), `WaveSourceFlux.lean` (41), `L2FourierMultiplier.lean` (46–47),
`L2MultiplierContinuity.lean` (48), `KleinGordonL2Propagator.lean` (49–52),
`VolterraStrongKernel.lean` (53), `KleinGordonMildSolution.lean` (54–56),
`KleinGordonL2Propagator.lean` and `L2FourierMultiplier.lean` again (57),
`KleinGordonEnergyConservation.lean` (58–60), `KleinGordonMildSolution.lean` again (61),
`L2FourierMultiplier.lean` again (62), `KleinGordonPropagatorDerivative.lean` (63–65),
`KleinGordonStrongSolution.lean` (66–69). All wired into the umbrella; axioms
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

### The bridge, built

Statements 17 and 18 close it. `kgWaveOp_eq_of_contDiff` expands the corpus operator as
`-∂₀∂₀u + ∑ᵢ∂ᵢ₊₁∂ᵢ₊₁u` for a smooth field, and `solvesWaveEq_comp_eventCLM` turns a solution of the
corpus's `SolvesPotentialWaveAt (kgWaveOp d) V u` into a solution of `SolvesWaveEq` in time-space
coordinates. So every probe the corpus constructs by Fourier synthesis — including the
finite-regularity ones — inherits the energy estimate, the two-sided estimate, uniqueness and
continuous dependence, provided it has spatially compact support.

Statement 19 makes the bridge an equivalence. Every event is `eventCLM d (y 0, Fin.tail y)`
(`Fin.cons_self_tail`), so the converse holds too and **`solvesWaveEq_comp_eventCLM_iff`** records
that the two formulations of the clock equation are the same statement. Results proved in either
language now transfer both ways.

Statement 20 states the capstone in the corpus's own language:
**`eq_of_solvesPotentialWave_of_data_eq`** — *two smooth fields with spatially compact support, both
solving `SolvesPotentialWaveAt (kgWaveOp d) V`, with `V` continuous and bounded, and agreeing on the
initial slice together with their time derivatives there, agree at every event.* No time-space
coordinates appear in the statement; the bridge is used only inside the proof.

### The compact-support hypothesis, and how far it can go

There is an honest limitation to record. The estimate assumes the field has spatially compact
support, which is what a cut-off potential supplies but **not** what a Fourier synthesis supplies:
the corpus's constructed probes decay, they do not vanish outside a compact set. The bridge
transports the *equation* to them, but the estimate itself does not yet apply.

Compact support is used in exactly two places, and statement 21 removes the first: mathlib's
integration by parts asks only that the three relevant products be integrable, so
**`integral_laplacian_mul_of_integrable`** proves the Green identity for integrable data with the
differentiability supplied by smoothness alone. Statement 22 carries that through the whole cancellation:
**`integral_dirDeriv_energyDensity_of_integrable`** proves `∫∂ₜ(energy density) = 2∫(V+1)·u·∂ₜu`
from four families of integrability hypotheses — the three the Green identity consumes and one for
the zeroth-order term — with no support hypothesis anywhere.

Statement 23 removes the second and last use: **`hasDerivAt_waveEnergy_of_dominated`** differentiates
the energy under the integral sign given an integrable dominating function on a time interval and
integrability of the energy density on the slice — no support hypothesis. For a compactly supported
field the dominating function is manufactured from the supremum on a compact set (statement 10); for
a decaying field it is supplied.

So every step of the layer — Green identity, flux identity, differentiation of the energy — runs on
integrability and domination alone, and statement 24 assembles them. The structure
`DecayingSolution` collects exactly what replaces compact support: smoothness, the equation,
integrability of the energy density and of the three Green products and the zeroth-order term on
every slice, and a local dominating function in time. With it,

**`waveEnergy_le_exp_of_decaying`**: `E(t) ≤ E(0)·exp((M+1)t)` for `t ≥ 0`, for a **decaying**
solution — no compact support anywhere.

Statement 25 carries the uniqueness half across as well:
**`eq_zero_of_waveEnergy_zero_of_decaying`** — a decaying solution whose energy vanishes at one time
vanishes at every later time.

That is the form the corpus's Fourier-built probes can meet: they decay rather than vanish outside a
compact set, and each field of `DecayingSolution` is an integrability statement about a synthesis
integral. Discharging those fields for a concrete constructed probe is the remaining bookkeeping.

Statement 26 settles the non-vacuity question that any new hypothesis class has to answer.
**`decayingSolution_of_hasCompactSupport`**: every smooth solution with spatially compact support
satisfies all seven conditions of `DecayingSolution` — each integrand is continuous with compact
support, and the dominating function is the supremum on the compact box `Icc (t-1) (t+1) ×ˢ K`,
supported on `K`. So the decaying layer **subsumes** the compactly supported one rather than
trading it for an empty class, and everything proved in statements 1–20 is a special case of
24–25.

Statement 27 makes the decaying layer symmetric. Reversing time carries a decaying solution to a
decaying solution of the reflected potential — every integrand of the seven-field bundle changes at
most by a sign, and the energy density not at all — so **`waveEnergy_le_exp_abs_of_decaying`** gives
`E(t) ≤ E(0)·exp((M+1)|t|)` on both sides of the initial slice, and statement 28
**`eq_zero_of_waveEnergy_zero_of_decaying_all`** — a decaying solution with vanishing initial energy
vanishes at *every* time, not only later ones.

With that the decaying layer has the same four theorems as the compactly supported one — estimate,
vanishing, two-sidedness, and (statement 26) the inclusion of one class in the other — with compact
support nowhere in the hypotheses.

Statement 29 states it in the corpus's own language, which is the point of the whole arc:
**`eq_zero_of_solvesPotentialWave_of_decaying`** — *a smooth field on events whose pullback to
time-space coordinates satisfies the decay conditions, and whose value and time derivative vanish on
the initial slice, vanishes at every event.* The hypotheses and the conclusion are stated on
`Fin (d+1) → ℝ` with `coordPartial 0` and `Fin.cons 0 x`; the bridge, the reflection and the whole
energy machinery live inside the proof.

### A caveat that has to be stated plainly

Statement 30 bounds the reach of the whole layer from the other side. The constant field `1` solves
the free clock equation, and its energy density is the constant `1`, which is not integrable over a
space of positive dimension — so **`not_decayingSolution_one_field`**: solving the equation does not
imply the decay hypotheses. Finiteness of the energy is an assumption about the solution.

This matters for the corpus's own probes. A Fourier synthesis against an `L¹` density produces a
*bounded* continuous field, and boundedness is not decay: the constant field is exactly such a
synthesis. So the earlier claim that the estimate "applies to the corpus's Fourier-built probes"
should be read as conditional — it applies to those probes **once their energy and Green products
are shown integrable**, which is an extra `L²`-type statement about the density and not a corollary
of the construction. Statement 26 gives one sufficient condition (compact support); statement 31 gives the practical one.
**`decayingSolution_of_memLp_two`**: every integrability field of the bundle is a product of two
functions, so square integrability of each factor supplies all of them by Cauchy–Schwarz
(`MemLp.integrable_mul`), and the energy density is a sum of squares (`MemLp.integrable_sq`). What
has to be supplied is `MemLp … 2` for the slices, their spatial derivatives, their second spatial
derivatives, the time derivative and its spatial derivatives — plus continuity and boundedness of
the potential and the local domination in time.

That is the form a Fourier construction can meet, because Plancherel turns square integrability of a
synthesis into square integrability of its density.

Statement 32 repairs the structural defect noted below. The *bundle* is not closed under
differences, but the *criterion* is: `MemLp _ 2` is a linear condition, so square integrability of
the slices, of their directional derivatives and of the spatial derivatives of the slices all pass
to a difference (`memLp_two_slice_sub`, `memLp_two_slice_dirDeriv_sub`,
`memLp_two_coordPartial_slice_sub`, the last using `coordPartial_sub_fun`). Two solutions meeting
the criterion therefore have a difference that meets it, and the vanishing theorem applies to them —
which is the two-solution uniqueness statement the bundle alone could not support.

Statement 33 assembles it. `L2Solution` collects the six square-integrability conditions,
**`L2Solution.sub`** proves the class closed under differences, and
**`eq_of_solvesWaveEq_of_memLp`**: *two square-integrable solutions of the same clock equation, with
a continuous bounded potential, a local dominating function for the difference, and the same Cauchy
data, agree at every event.* This is the uniqueness theorem in the class a Fourier construction can
meet — no compact support, only decay expressed as square integrability. Statement 34 states it on
events: **`eq_of_solvesPotentialWave_of_memLp`** — *two smooth fields solving
`SolvesPotentialWaveAt (kgWaveOp d) V`, whose pullbacks to time-space coordinates are square
integrable, with the same value and time derivative on the initial slice, agree at every event.*
That is the theorem the clock programme can quote directly.

### The one hypothesis that is still not an `L²` statement

`hdom` — the local dominating function for the time derivative of the energy density — is the last
hypothesis of statements 33 and 34 that is not itself square integrability. Statement 35 supplies
the tool for removing it: that derivative is
`2(∂ₜu·∂ₜ²u + ∑ᵢ∂ᵢu·∂ₜ∂ᵢu + u·∂ₜu)`, a **sum of products of two factors**, and
**`integrable_of_dominated_by_sum_memLp_two`** turns square-integrable dominating functions for the
factors into an integrable dominating function for the whole. Statement 36 does exactly that. **`exists_bound_of_factor_memLp`** takes square-integrable
dominating functions for the five factors — `u`, `∂ₜu`, `∂ₜ²u`, each `∂ᵢu`, each `∂ₜ∂ᵢu`, uniformly
for `s` in a unit time interval — and produces the integrable dominating function
`2·g_T·g_TT + ∑ᵢ 2·g_S,i·g_ST,i + 2·g_U·g_T` that `hdom` asks for.

So every hypothesis of the uniqueness theorem is now expressible as square integrability plus
uniform-in-time domination of the solution and its first two derivatives — no compact support, and
nothing about the potential beyond continuity and boundedness.

### The final assembly

Statement 37 closes it. The `hdom` hypothesis of statements 33–34 is about the **difference** of the
two solutions, while statement 36 produces a dominating function from factor bounds for a **single**
field. **`exists_bound_of_factor_memLp_sub`** bridges them: a difference is bounded by the sum of
the bounds (`abs_sub_le_add`, with `waveDirDeriv_sub` and `waveDirDeriv_sub_fun` for the first and
second derivatives), and `MemLp` is closed under addition, so the five families of dominating
functions add and feed straight into statement 36 for `u₁ - u₂`.

Statement 38 is the resulting theorem. `FactorDominated` packages the five families of
uniform-in-time square-integrable dominating functions, and
**`eq_of_solvesWaveEq_of_memLp_of_factorDominated`** reads:

> two solutions of the same clock equation, each square integrable (`L2Solution`) and each
> factor-dominated (`FactorDominated`), with a continuous bounded potential and the same Cauchy
> data, agree at every event.

Every hypothesis is about **one solution at a time**, and each is either square integrability or
uniform-in-time domination by a square-integrable function. Compact support has disappeared from the
layer entirely.

Statement 39 states it on events — **`eq_of_solvesPotentialWave_of_memLp_of_factorDominated`** —
which is the theorem the clock programme quotes: two smooth solutions of
`SolvesPotentialWaveAt (kgWaveOp d) V`, each with square-integrable and factor-dominated pullback,
sharing their value and time derivative on the initial slice, agree at every event.

Statement 40 gives the quantitative companion. The difference of two square-integrable,
factor-dominated solutions is a decaying solution
(`decayingSolution_sub_of_memLp_of_factorDominated`), so
**`waveEnergy_sub_le_exp_abs_of_memLp`**: the energy of the difference at any time is bounded by its
value on the initial slice times `exp((M+1)|t|)`. Uniqueness is the special case of vanishing
initial data; this is the stability statement, and it completes the table — estimate, uniqueness and
continuous dependence, in each of the three hypothesis classes.

(The decaying-bundle row has no separate stability entry on purpose: the bundle is not closed under
differences, so the statement for a pair would be a restatement of the single-solution estimate
applied to the difference, not a theorem with new content. The `L²` class is where the pair
statement has content, because there the class *is* closed.)

### The entry point to existence

The layer proves uniqueness and stability; existence is the other half and is what would lower the
regularity threshold of `finite-regularity-clock-probes`. Its entry point is the **inhomogeneous**
estimate. For `∂ₜ²u = Δu + Vu + f` the same computation gives

`∫ ∂ₜ(energy density) = 2∫((V+1)·u·∂ₜu + f·∂ₜu)`,

whose only new term is the source pairing; bounding it by `2‖f(t)‖_{L²}·E(t)^{1/2}` turns Grönwall
into `d/dt √E ≤ ((M+1)/2)√E + ‖f(t)‖_{L²}`, which is exactly the estimate a Picard iteration on the
Duhamel formula consumes. Statement 41 lays the first of those bricks. `SolvesWaveEqSource` is the inhomogeneous equation,
`solvesWaveEqSource_zero` places the homogeneous one inside it, and
**`waveDirDeriv_energyDensity_source`** is the pointwise energy identity carrying the extra source
term. `solvesWaveEq_of_solvesWaveEqSource` records the elementary but useful fact that off the zero
set of the field a source is just a modification of the potential, `V + f/u`.

Statement 42 supplies the comparison the source bound needs:
**`integral_sq_dirDeriv_le_waveEnergy`** and **`integral_sq_le_waveEnergy`** — the energy of a slice
dominates the `L²` norms of the time derivative and of the field there, since the energy density is
the sum of those two squares and the gradient square.

Statement 43 integrates it: **`integral_dirDeriv_energyDensity_source`** proves

`∫ ∂ₜ(energy density) = 2∫(V+1)·u·∂ₜu + 2∫f·∂ₜu`

from the same four families of integrability hypotheses as statement 22, plus one for the source
pairing. The Green cancellation is untouched — the source rides along as a fifth summand.

Statement 44 bounds the new term: **`abs_integral_source_le`** gives
`|2∫f·∂ₜu| ≤ ‖f(t)‖²_{L²} + E(t)`. Using `2|ab| ≤ a² + b²` instead of Cauchy–Schwarz keeps the
estimate free of square roots — the price is `‖f‖² + E` in place of the sharp `2‖f‖·√E`, and the
gain is that Grönwall can be run on `E` itself rather than on `√E`, with no extra machinery.

Statement 45 is that assembly. **`waveEnergy_le_gronwall_source`**: given the flux identity as the
derivative of the energy and the two bounds on its size, Grönwall yields

`E(t) ≤ gronwallBound (E(0)) (M+2) S t`  for `t ≥ 0`,

with `S` a bound for the source term `‖f(s)‖²_{L²}` on the interval. Taking `S = 0` recovers the
homogeneous estimate; the inhomogeneous form is what a Picard iteration on the Duhamel formula
consumes, since it converts a bound on the source into a bound on the energy of the iterate.

That completes the *estimate* side of the existence programme. What is still missing for existence
itself is the construction: a solution operator for the free equation on the energy space and a
fixed point for the Duhamel map. The corpus already owns the free evolution in its Fourier form
(`kgCosSymbol`, `kgSinSymbol`, `memSobolev_kgCosSymbol`), so the remaining work is to run the
Volterra iteration of `VolterraLinearIntegralEquation.lean` in the energy space rather than in the
Wiener space — the estimate above being exactly the bound that makes that iteration converge.

The interface to target is, in `VolterraLinearIntegralEquation.lean`, for a Banach space `X`:

* `volterraSolution (f : ℝ → X) (K : ℝ → ℝ → X →L[ℝ] X) : ℝ → X` — the Picard series;
* `volterraSolution_eq` — it satisfies `u t = f t + ∫ s in 0..t, K t s (u s)`;
* `continuous_volterraSolution`, `norm_volterraSolution_le` — continuity and
  `‖u t‖ ≤ F·exp(M|t|)`,

each requiring only: `f` and `K` continuous, `‖K t s‖ ≤ M`, `‖f t‖ ≤ F`. So the construction reduces
to exhibiting the Duhamel data — `X` the energy space, `f` the free evolution of the Cauchy data,
`K t s` the multiplication-by-`V` operator conjugated by the free propagator — and checking those
four bounds. The corpus already has the free propagator as a bounded Fourier multiplier
(`memSobolev_kgCosSymbol`, `memSobolev_kgSinSymbol`), which is what supplies `‖K t s‖ ≤ M`.

One structural note for whoever continues: `DecayingSolution` is **not** closed under differences —
each of its integrability fields is a product of a derivative of the field with a derivative of its
time derivative, so the difference of two solutions produces cross terms that the hypotheses for the
two solutions separately do not cover. The two-solution uniqueness statement therefore has to assume
`DecayingSolution` *of the difference*, exactly as statement 25 is phrased. That is not a defect of
the formalisation: it is the honest content of the estimate for non-compactly-supported data.


### The existence half, built

Statements 46–56 close the other half of the classical local theory: the estimate is now accompanied
by a construction. The route is the one the card specified — the Volterra iteration of
`VolterraLinearIntegralEquation.lean` run in the energy space — and three things had to be built for
it.

**The energy variables.** Writing `w = (⟨D⟩u, ∂ₜu)` turns the second-order equation
`∂ₜ²u = -⟨D⟩²u + Vu` into the first-order system `∂ₜw = Jw + Nw` with

`N (w₁, w₂) = (0, V ⟨D⟩⁻¹ w₁)`.

Since `⟨ξ⟩⁻¹ ≤ 1`, the operator `⟨D⟩⁻¹` is a contraction of `L²`, so `N` is a **bounded** operator
of norm at most `‖V‖_∞` (statement 54). This is the whole point of the energy variables: in the
field variables the perturbation is unbounded relative to the space, and no fixed-point argument
runs; in the energy variables it is bounded, and the perturbation series converges with no smallness
hypothesis whatever.

**The free propagator.** On the Fourier side the free evolution in these variables is the rotation
by `t⟨ξ⟩`, whose four entries `cos(t⟨ξ⟩)`, `±sin(t⟨ξ⟩)` are bounded by one *uniformly in time* — the
plain sine, not the corpus's `kgSinSymbol`, whose factor `⟨ξ⟩⁻¹` is what makes it grow like `|t|`.
Each entry is therefore a Fourier multiplier on `L²` of norm at most one (statement 47, built on
mathlib's Plancherel isometry `Lp.fourierTransformₗᵢ` and the corpus's `lpBoundedMulCLM`), and
`kgPropagator t` is bounded by `2` for every `t` (statement 52).

**Strong, not norm, continuity.** No nontrivial propagator group is continuous in the operator norm,
so the corpus's Volterra layer — which asks for a norm continuous kernel — does not apply as it
stands. Statement 48 proves what is true: a family of symbols bounded by one constant and converging
pointwise gives multiplication operators converging *strongly*, by dominated convergence for the
Lebesgue integral of `|φᵢ - ψ|²|f|²`. Statement 49 upgrades strong continuity plus a uniform bound to
joint continuity in the time and the vector, and statement 53 re-runs the whole perturbation series
under the resulting weaker hypothesis `StrongKernel` — the bounds are unchanged, because the kernel
is only ever applied to the iterates, which are continuous by construction.

With those three, the Duhamel data are admissible and the capstone follows:

**`exists_unique_kgMildSolution`**: *for a measurable potential bounded by `b` and any datum `w₀` in
the energy space there is exactly one continuous curve `w : ℝ → L² × L²` with*

`w(t) = U(t)w₀ + ∫₀ᵗ U(t-s) N w(s) ds`,

*it starts at `w₀` (`kgMildSolution_zero`), and it obeys `‖w(t)‖ ≤ 2‖w₀‖ e^{2b|t|}`
(`norm_kgMildSolution_le`).*

The hypotheses on the potential are measurability and boundedness — no continuity, no decay, no
smoothness, no sign, no time-independence of the construction's inputs beyond the statement's own.
That is far below the `C^{2d+5}` that the Fourier synthesis of `finite-regularity-clock-probes`
consumes, and it is global in time.

What this gives is the *mild* solution. Identifying it with a classical solution of the pointwise
equation — differentiating the Duhamel integral, which needs the group law of the propagator and a
regularity hypothesis on the datum — is the next brick, and it is what would let the uniqueness
half of this card (statements 1–45) and the existence half meet on the same object.


### The propagator is a group, and the energy is exactly conserved

Statements 57–60 replace the two crude facts the existence proof was content with — that the
propagator is bounded by `2` and that it starts at the identity — by the two sharp ones.

Statement 57 is the group law. The addition formulas `cos((t+s)c) = cos(tc)cos(sc) - sin(tc)sin(sc)`
and `sin((t+s)c) = sin(tc)cos(sc) + cos(tc)sin(sc)` are, through Plancherel, operator identities
between composites of Fourier multipliers, and assembling the four entries of the rotation gives
**`kgPropagator_add`**: `U(t+s) = U(t)U(s)`. With `kgPropagator_zero_apply` the propagator is a
one-parameter group, which is what a Duhamel formula has to be compatible with.

Statements 58–60 give the exact energy identity. A multiplication operator with a **real** symbol is
self-adjoint on `L²` (**`inner_lpBoundedMulCLM_real`**, from `L2.inner_def` and nothing else), and
Plancherel — which preserves the inner product, `Lp.inner_fourier_eq` — carries that to Fourier
multipliers (**`inner_fourierMulCLM_real`**). Both propagator symbols are real, so `C_t` and `S_t`
are self-adjoint. Two further symbol identities become operator identities the same way:

`C_t² + S_t² = 1` (**`kgCosOp_sq_add_kgSinOp_sq`**, the Pythagorean identity), and
`C_t S_t = S_t C_t` (**`kgCosOp_comp_kgSinOp_comm`**, commutativity of multiplication).

Expanding `‖C v₁ + S v₂‖² + ‖-S v₁ + C v₂‖²` by the polarization expansion, the two cross terms are
`re⟪v₁, C S v₂⟫` and `re⟪v₁, S C v₂⟫` after moving the operators across the inner product, so they
cancel; the four diagonal terms collapse in pairs by the Pythagorean identity. That is

**`kgEnergy_kgPropagator`**: `‖U(t)v‖₁² + ‖U(t)v‖₂² = ‖v₁‖² + ‖v₂‖²` — *the free Klein–Gordon
evolution conserves the energy exactly, for every datum in the energy space and every time.*

No integral is computed anywhere in the proof: the whole identity is operator algebra over the two
symbol identities. Note the norm used is the Hilbert one `‖v₁‖² + ‖v₂‖²`, not the product-space sup
norm that `KGEnergy` carries; the sup norm is what the Volterra layer's bounds are stated in, and the
factor `2` in `‖U(t)‖ ≤ 2` is exactly the discrepancy between the two.


### The two halves state the same inequality

The existence layer was first built on the product space with its supremum norm, which cost a factor
`2` in every bound. That factor is not real, and statements 52 and 60 remove it: the energy space is
now `WithLp 2 (L² × L²)`, whose norm is the *square root of the energy* rather than the maximum of
the two components. On that space

`‖U(t)v‖ = ‖v‖`  (**`norm_kgPropagator_apply`**),

so `‖U(t)‖ ≤ 1`, and the perturbation `N` is bounded by the supremum of the potential with no factor
at all (**`norm_kgPotentialOp_le`**, because `‖⟨D⟩⁻¹‖ ≤ 1` and `‖(0, x)‖ = ‖x‖` in the Hilbert
norm). The Volterra layer then runs with `M = b` and `F = ‖w₀‖` instead of `2b` and `2‖w₀‖`, and the
conclusion is the sharp one:

**`norm_kgMildSolution_le`**: `‖w(t)‖ ≤ ‖w₀‖ · e^{b|t|}`, i.e. squaring,

**`kgEnergy_kgMildSolution_le`**: `E(t) ≤ E(0) · e^{2b|t|}`.

That is the same shape as the card's headline estimate — energy at time `t` controlled by energy of
the data, exponentially, at a rate set by the supremum of the potential alone. The uniqueness half
(statements 1–45) proves it for classical solutions with an integrability hypothesis; the existence
half (46–61) now proves it for a solution that is *constructed*, from a potential asked only to be
measurable and bounded. The two halves of the classical local theory finally assert the same
inequality about the same kind of object.

What is still open is the identification of the two objects: the mild solution is a curve in `L² × L²`
satisfying an integral equation, and showing that for regular data it is a classical solution of the
pointwise equation needs the generator of the propagator group — an unbounded operator — and is the
next brick.


### The generator, and why it is not an obstruction

The propagator group is generated by an *unbounded* operator — `⟨D⟩` sits in the off-diagonal
entries — so `t ↦ U(t)v` is differentiable only on a domain, and that domain is what statements
63–65 identify and exploit.

The domain is the range of `⟨D⟩⁻¹`. On it the derivative is again a bounded expression, because the
`⟨ξ⟩` that the chain rule produces cancels the `⟨ξ⟩⁻¹` carried by the datum:

`d/dt [cos(t⟨ξ⟩)/⟨ξ⟩] = -sin(t⟨ξ⟩)`,  `d/dt [sin(t⟨ξ⟩)/⟨ξ⟩] = cos(t⟨ξ⟩)`.

So the whole statement stays inside the bounded-multiplier calculus, and the limit that defines the
derivative in `L²` is exactly the strong convergence of statement 48. The difference quotient of
`cos(s⟨ξ⟩)/⟨ξ⟩` at `t` is bounded by **one** uniformly in `s` — the cosine is `1`-Lipschitz, and the
`⟨ξ⟩` in `|cos(s⟨ξ⟩) - cos(t⟨ξ⟩)| ≤ |s-t|⟨ξ⟩` cancels the `⟨ξ⟩⁻¹` — and it converges pointwise to
`-sin(t⟨ξ⟩)`. Statement 48 turns that into convergence in `L²`, which is

**`hasDerivAt_kgCosOp_freqInv`**: `d/dt (C_t ⟨D⟩⁻¹g) = -S_t g`, and
**`hasDerivAt_kgSinOp_freqInv`**: `d/dt (S_t ⟨D⟩⁻¹g) = C_t g`.

Assembling the four entries gives **`hasDerivAt_kgPropagator_regular`**: for `v = (⟨D⟩⁻¹g₁, ⟨D⟩⁻¹g₂)`
the curve `t ↦ U(t)v` is differentiable in the energy space, with derivative

`(-S_t g₁ + C_t g₂, -C_t g₁ - S_t g₂)`,

which is `J U(t)v` written without ever naming the unbounded `J`. That is the free equation, solved
in the strong sense by the free evolution of a regular datum. What remains for the full
mild-implies-classical statement is the Duhamel term: differentiating
`∫₀ᵗ U(t-s)Nw(s) ds` under the integral sign, for which this file supplies the differentiability of
the propagator and the group law supplies the rest.


### The equation itself, solved strongly

Differentiating the propagator once costs one power of `⟨D⟩⁻¹` in the datum; differentiating it twice
costs two. So on the range of `⟨D⟩⁻²` the free evolution is twice differentiable *as a curve in `L²`*,
and statements 66–69 assemble that into a solution of the equation rather than of the first-order
system.

For `f, h` arbitrary in `L²`, the field

`u(t) = C_t ⟨D⟩⁻²f + S_t ⟨D⟩⁻²h`

has `∂ₜu(t) = -S_t ⟨D⟩⁻¹f + C_t ⟨D⟩⁻¹h` and `∂ₜ²u(t) = -(C_t f + S_t h)`, each an identity between
elements of `L²` — no distributions and no unbounded operators appear at any point. Since
`u(t) = ⟨D⟩⁻²(C_t f + S_t h)` (the propagators commute with `⟨D⟩⁻¹`, statement 66), that is

**`kgFreeField_kleinGordon`**: `⟨D⟩⁻²(∂ₜ²u) = -u`,

which for a doubly regular field is exactly `∂ₜ²u + ⟨D⟩²u = 0`; and `⟨ξ⟩² = 1 + ‖ξ‖²` is the symbol of
`1 - (2π)⁻²Δ`, so this is the physical field equation. With the initial values
`u(0) = ⟨D⟩⁻²f`, `∂ₜu(0) = ⟨D⟩⁻¹h`, **`exists_kgFreeField`** states the Cauchy problem's solvability
in the strong `L²` sense for every datum in the range of `⟨D⟩⁻²` with velocity in the range of
`⟨D⟩⁻¹`.

Statement 69 closes the circle with the beginning of the card. The pair `(⟨D⟩u(t), ∂ₜu(t))` is
exactly `U(t)` applied to `(⟨D⟩u(0), ∂ₜu(0))` (**`kgPropagator_kgFreeState`**), so the abstract
isometry of statement 60 becomes the *classical* conservation law

**`kgFreeField_energy_const`**: `‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖²` is independent of `t`.

That is the energy of the card's opening paragraph — `∫ (∂ₜu)² + |∇u|² + u²`, in the Fourier
normalisation where `⟨ξ⟩²` carries both the gradient and the mass — now proved conserved for a
solution the corpus constructs, not merely bounded for a solution assumed to exist.

### Historical note on the plan

The step was originally recorded as: identifying
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
- 2026-08-04 — statements 66–69: the strong `L²` solution of the free Klein–Gordon equation on
  doubly regular data, and exact conservation of `‖⟨D⟩u‖² + ‖∂ₜu‖²` for it.
- 2026-08-04 — statements 62–65: the domain of the generator is the range of `⟨D⟩⁻¹`, and on it
  the propagator is differentiable with a bounded derivative — proved with the strong-convergence
  machinery alone, no unbounded-operator theory.
- 2026-08-04 — statement 61 and the sharpening of 52/54–56/60: the energy space is now the Hilbert
  space `WithLp 2 (L² × L²)`, the propagator is an isometry, and the constructed solution obeys
  `E(t) ≤ E(0)e^{2b|t|}` — the same inequality the uniqueness half proves for classical solutions.
- 2026-08-04 — statements 57–60: the propagator group law, self-adjointness of real multipliers,
  the Pythagorean and commutation identities, and **exact conservation of the free energy**.
- 2026-08-04 — statements 46–56: **the existence half**. Bounded Fourier multipliers on `L²`, the
  free Klein–Gordon propagator on the energy space, the Volterra layer with a strongly continuous
  kernel, and global well-posedness of the Cauchy problem for a bounded measurable potential.
  Six new modules, every theorem unconditional.
- 2026-08-04 — recorded the exact `volterraSolution` interface the construction step has to meet.
- 2026-08-04 — wiring audit: every `Wave*` module in `HTGeometry/` is imported by the area umbrella
  (35 files checked, none missing).
- 2026-08-04 — statement 45: the inhomogeneous energy estimate. The estimate side of the existence
  programme is complete; what remains is the construction (free evolution + Duhamel fixed point).
- 2026-08-04 — statement 44 (the source pairing is dominated by the energy); the square-root
  Grönwall is avoidable.
- 2026-08-04 — statement 43 (the integrated flux identity with a source).
- 2026-08-04 — statement 42 (the energy dominates the L² norms of the field and its time
  derivative).
- 2026-08-04 — statement 41: the inhomogeneous equation and its pointwise energy identity.
- 2026-08-04 — the entry point to existence (inhomogeneous estimate) specified on the card.
- 2026-08-04 — statement 40 (continuous dependence in the L² class); the three-class table is
  complete.
- 2026-08-04 — statement 39: the capstone in event coordinates. The layer is complete.
- 2026-08-04 — statement 38: the capstone. Uniqueness with hypotheses on each solution separately.
- 2026-08-04 — statement 37: the final assembly built. `hdom` for a difference now follows from
  factor bounds for each solution separately.
- 2026-08-04 — statement 36 (dominating function from factor-wise L² bounds); the last non-L²
  hypothesis is now derivable.
- 2026-08-04 — statement 35 (domination by products of square-integrable functions) formalized; the
  tool for making the last non-L² hypothesis an L² one.
- 2026-08-04 — statement 34 (square-integrable uniqueness in event coordinates) formalized.
- 2026-08-04 — statement 33 (two-solution uniqueness for square-integrable solutions) formalized.
- 2026-08-04 — statement 32 (the L² criterion is closed under differences) formalized.
- 2026-08-04 — statement 31 (square-integrability criterion for the decay bundle) formalized.
- 2026-08-04 — statement 30 (the decay hypothesis is not implied by solving the equation); the
  claim that the estimate reaches the corpus's Fourier probes is corrected to a conditional one.
- 2026-08-04 — statement 29 (decaying uniqueness in event coordinates) formalized.
- 2026-08-04 — statement 28 (two-sided vanishing for decaying solutions) formalized; the decaying
  layer now mirrors the compactly supported one completely.
- 2026-08-04 — statement 27 (reflection of a decaying solution, two-sided estimate) formalized.
- 2026-08-04 — statement 26 (compact support implies the decaying hypotheses) formalized; the class
  is inhabited and the new layer subsumes the old.
- 2026-08-04 — statement 25 (vanishing for decaying solutions) formalized.
- 2026-08-04 — statement 24 (Grönwall estimate for decaying solutions) formalized; the layer no
  longer needs compact support at any step.
- 2026-08-04 — statement 23 (dominated differentiation of the energy) formalized; compact support is
  no longer used anywhere in the layer's analytic core.
- 2026-08-04 — statement 22 (flux identity for integrable data) formalized; only the dominating
  function for differentiation under the integral still uses compact support.
- 2026-08-04 — statement 21 (Green identity for integrable data) formalized; the first of the two
  compact-support uses is removed.
- 2026-08-04 — statement 20 (uniqueness in event coordinates) formalized.
- 2026-08-04 — statement 19 (converse bridge, equivalence of the two formulations) formalized.
- 2026-08-04 — statements 17–18 (coordinate dictionary and operator bridge) formalized.
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
