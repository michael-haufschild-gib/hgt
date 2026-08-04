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
| 70 | `⟨D⟩⁻¹` is self-adjoint, and the two calculus helpers | **`inner_kgFreqInvOp`**, `hasDerivAt_clm`, `hasDerivAt_norm_sq` | **built** |
| 71 | the strong solution class and its conserved energy | `SolvesKG`, `kgStrongEnergy`, `kgStrongEnergy_nonneg`, **`hasDerivAt_kgStrongEnergy`**, **`kgStrongEnergy_const`** | **built** |
| 72 | **uniqueness for the strong Cauchy problem** | **`eq_zero_of_solvesKG`**, `SolvesKG.sub`, **`eq_of_solvesKG`** | **built** |
| 73 | **well-posedness: the constructed field is the solution** | **`solvesKG_kgFreeField`**, **`eq_kgFreeField_of_solvesKG`** | **built** |
| 74 | strong solutions with a bounded perturbation | `SolvesKGSource`, `solvesKGSource_zero`, **`hasDerivAt_kgStrongEnergy_source`** | **built** |
| 75 | the energy derivative is dominated by the energy | **`abs_deriv_kgStrongEnergy_le`** | **built** |
| 76 | **the Grönwall estimate for the perturbed equation** | **`kgStrongEnergy_le_exp`** | **built** |
| 77 | time reflection and two-sided uniqueness | `SolvesKGSource.comp_neg`, **`eq_zero_of_solvesKGSource`**, **`eq_of_solvesKGSource`** | **built** |
| 78 | **uniqueness for a bounded measurable potential** | **`eq_of_solvesKGSource_potential`** | **built** |
| 79 | reflection and the two-sided Grönwall estimate | `kgStrongEnergy_comp_neg`, **`kgStrongEnergy_le_exp_abs`** | **built** |
| 80 | **continuous dependence in the perturbed strong class** | `SolvesKGSource.sub`, **`kgStrongEnergy_sub_le_exp_abs`** | **built** |
| 81 | the Volterra equation with a vanishing kernel | `volterraIterate_zero_kernel`, **`volterraSolution_zero_kernel`** | **built** |
| 82 | **the two constructions agree where they overlap** | **`kgMildSolution_of_ae_zero`** | **built** |
| 83 | the half-order propagator `sin(t⟨D⟩)/⟨D⟩` | `kgSinFreqOp`, `norm_kgSinFreqOp_le`, `kgSinFreqOp_zero`, **`continuous_kgSinFreqOp_apply`**, `continuous_kgSinFreqOp_comp` | **built** |
| 84 | the field-level Duhamel data | `kgFieldFree`, `kgFieldFree_zero`, `norm_kgFieldFree_le`, `kgFieldKernel`, `norm_kgFieldKernel_le`, **`strongKernel_kgFieldKernel`** | **built** |
| 85 | **well-posedness of the field equation for arbitrary `L²` data** | `kgFieldMild`, `continuous_kgFieldMild`, **`kgFieldMild_eq`**, `kgFieldMild_zero`, **`norm_kgFieldMild_le`**, `eq_kgFieldMild_of_duhamel`, **`exists_unique_kgFieldMild`** | **built** |
| 86 | **the strong field is the mild field** | `kgFieldMild_zero_op`, `kgSinFreqOp_eq_comp`, `kgFreeField_eq_kgFieldFree`, **`kgFreeField_eq_kgFieldMild`** | **built** |
| 87 | **the velocity datum needs no regularity** | `kgSinFreqOp_apply`, **`hasDerivAt_kgSinFreqOp`**, **`hasDerivAt_kgFieldFree`**, `deriv_kgFieldFree_zero` | **built** |
| 88 | **linearity of the field solution and continuous dependence** | `kgFieldFree_sub`, `intervalIntegrable_kgFieldKernel`, **`kgFieldMild_sub`**, **`norm_kgFieldMild_sub_le`** | **built** |
| 89 | the subtraction law for the half-order propagator | **`kgSinFreqOp_sub`**, `continuous_kgCosOp_comp` | **built** |
| 90 | **the Duhamel term with observation and source times separated** | **`intervalIntegral_kgFieldKernel_separated`**, **`kgFieldMild_eq_separated`** | **built** |
| 91 | **the product rule for a strongly differentiable operator family** | **`hasDerivAt_strong_apply`** | **built** |
| 92 | the Duhamel integral of the half-order propagator is regular | `kgSinFreqOp_eq_freqInv_comp`, `kgSinFreqOp_apply_freqInv`, **`intervalIntegral_kgSinFreqOp_eq`** | **built** |
| 93 | the endpoint derivatives of the two Duhamel integrals | **`hasDerivAt_intervalIntegral_kgCosOp`**, **`hasDerivAt_intervalIntegral_kgSinOp`** | **built** |
| 94 | the subtraction law for the cosine propagator, and the commutation | **`kgCosOp_sub`**, **`kgSinFreqOp_comm_kgCosOp`** | **built** |
| 95 | the derivatives of the two halves of the separated term | **`hasDerivAt_kgDuhamelFirst`**, **`hasDerivAt_kgDuhamelSecond`** | **built** |
| 96 | **the Duhamel term is differentiable, with the classical derivative** | **`hasDerivAt_kgDuhamel`**, **`kgDuhamel_deriv_eq`** | **built** |
| 97 | **the mild field solution is differentiable, with the classical velocity** | **`hasDerivAt_kgFieldMild`**, **`deriv_kgFieldMild`** | **built** |
| 98 | **the `C¹` Cauchy problem is solved with the prescribed data** | `kgFieldMild_at_zero`, **`deriv_kgFieldMild_at_zero`**, **`exists_kgFieldMild_c1`** | **built** |
| 99 | the subtraction law for the energy-coordinate sine | **`kgSinOp_sub`** | **built** |
| 100 | the two integrals of a regular source, and their recombination | `intervalIntegral_kgCosOp_freqInv`, `intervalIntegral_kgSinOp_freqInv`, **`kgSinDuhamel_recombine`** | **built** |
| 101 | the endpoint contributions add up to the source | `kgCosOp_sq_add_kgSinOp_sq_apply`, **`kgEndpoint_sum`** | **built** |
| 102 | **the velocity integral is differentiable for a regular source** | **`hasDerivAt_kgCosDuhamel`** | **built** |
| 103 | the smoothing perturbation | `kgSmoothingOp`, `norm_kgSmoothingOp_le`, `kgSinFreqOp_freqInv` | **built** |
| 104 | the solution, its velocity and its acceleration | `kgSmoothMild`, `kgSmoothVel`, `kgSmoothAcc`, **`hasDerivAt_kgSmoothMild`**, **`hasDerivAt_kgSmoothVel`** | **built** |
| 105 | the solution is doubly regular, with explicit regularising vector | **`kgSmoothMild_eq`** | **built** |
| 106 | **a smoothing perturbation makes the mild solution strong** | **`solvesKGSource_kgSmoothMild`**, **`kgStrongEnergy_kgSmoothMild_le`** | **built** |
| 107 | the constructed solution starts at the prescribed data | `kgSmoothMild_at_zero`, `kgSmoothVel_at_zero` | **built** |
| 108 | **well-posedness of the strong problem with a smoothing perturbation** | **`eq_kgSmoothMild_of_solvesKGSource`**, **`wellPosed_solvesKGSource_smoothing`** | **built** |
| 109 | **the clock equation with a smoothed bounded measurable potential** | **`solvesKGSource_kgSmoothMild_potential`**, **`kgStrongEnergy_kgSmoothMild_potential_le`** | **built** |
| 110 | the initial energy, and the estimate in terms of the data | `kgStrongEnergy_kgSmoothMild_zero`, **`kgStrongEnergy_kgSmoothMild_le_data`**, **`norm_kgSmoothMild_le`** | **built** |
| 111 | **linearity in the data and continuous dependence for the constructed solution** | **`kgSmoothMild_sub`**, **`norm_kgSmoothMild_sub_le`** | **built** |
| 112 | a multiplier with a nowhere vanishing symbol is injective | **`lpBoundedMulCLM_injective`**, `kgFreqInv_ne_zero`, `fourierL2_injective`, **`kgFreqInvOp_injective`** | **built** |
| 113 | **the regularity hypotheses are not restrictive: the regular data are dense** | `denseRange_of_inner_eq_zero`, **`denseRange_kgFreqInvOp`**, **`denseRange_kgFreqInvOp_two`** | **built** |
| 114 | a pointwise bound valid only on the support still bounds the multiplier | **`norm_lpBoundedMulCLM_apply_le_of_ae`** | **built** |
| 115 | the high-frequency test function | `kgBallFun`, `kgBallFun_ne_zero`, **`norm_kgFreqInvOp_kgBallFun_le`**, `exists_norm_eq` | **built** |
| 116 | **the regularity restriction is genuine: `⟨D⟩⁻¹` is not surjective** | **`not_surjective_kgFreqInvOp`** | **built** |
| 117 | the sinc symbol and its limit | `kgSinc`, `norm_kgSinc_le`, **`tendsto_kgSinc`**, `continuous_kgSinc` | **built** |
| 118 | the regularised difference quotient is the sinc multiplier | **`kgFreqInvOp_slope_kgSinOp`** | **built** |
| 119 | **the regularity hypothesis is exactly the domain of differentiability** | **`mem_range_kgFreqInvOp_of_hasDerivAt`**, **`hasDerivAt_kgSinOp_iff`** | **built** |
| 120 | the addition law for the half-order propagator | **`kgSinFreqOp_add`** | **built** |
| 121 | **the free field evolution is a flow** | `kgFieldFreeVel`, `hasDerivAt_kgFieldFree'`, **`kgFieldFree_flow`** | **built** |
| 122 | the free field restarted from an accumulated state | **`kgFieldFree_restart`** | **built** |
| 123 | **the perturbed evolution is an evolution family** | **`kgFieldMild_flow`** | **built** |
| 124 | the free part carries the regularising factor | **`kgFieldFree_freqInv`** | **built** |
| 125 | **the field solution is regular at every time** | `kgFieldReg`, **`kgFieldMild_freqInv`** | **built** |
| 126 | **the restarted solution has a velocity, so the family iterates** | **`hasDerivAt_kgFieldMild_restart`** | **built** |
| 127 | the field bounded by the raw data | **`norm_kgFieldMild_le_data`** | **built** |
| 128 | **an exponential bound on the velocity of the field solution** | **`norm_deriv_kgFieldMild_le`** | **built** |
| 129 | the velocity is linear in the Cauchy data | **`deriv_kgFieldMild_sub`** | **built** |
| 130 | **stability of the whole propagated state** | `norm_kgFieldMild_sub_le_data`, **`norm_deriv_kgFieldMild_sub_le`**, **`kgFieldMild_state_stability`** | **built** |
| 131 | parity of the propagators, and reversibility of the free field | **`kgCosOp_neg`**, **`kgSinFreqOp_neg`**, **`kgFieldFree_neg`** | **built** |
| 132 | **the field evolution is reversible** | **`kgFieldMild_neg`** | **built** |
| 133 | the solution is additive and homogeneous in the data | `kgFieldFree_add`, `kgFieldFree_smul`, **`kgFieldMild_add`**, **`kgFieldMild_smul`** | **built** |
| 134 | **the solution operator, as a continuous linear map** | `kgSolutionLM`, **`kgSolutionCLM`**, `kgSolutionCLM_apply`, **`norm_kgSolutionCLM_le`** | **built** |
| 135 | the difference of two solutions with different potentials, in Duhamel form | **`kgFieldMild_sub_potential`** | **built** |
| 136 | **the solution is Lipschitz in the perturbation** | `norm_kgFieldMild_sub_potential_le_of_nonneg`, **`norm_kgFieldMild_sub_potential_le`** | **built** |
| 137 | the Lipschitz constant is uniform on bounded data and bounded times | **`norm_kgFieldMild_sub_potential_le_of_le`** | **built** |
| 138 | **the field depends continuously on the potential** | **`tendsto_kgFieldMild_of_tendsto_potential`** | **built** |
| 139 | the Duhamel term of an arbitrary continuous source is differentiable | `intervalIntegral_kgSinFreqOp_separated`, **`hasDerivAt_intervalIntegral_kgSinFreqOp`** | **built** |
| 140 | the cosine Duhamel term has derivative `g(0)` at the origin | **`hasDerivAt_intervalIntegral_kgCosOp_zero`** | **built** |
| 141 | a continuous source with vanishing Duhamel term vanishes at the origin | **`eq_zero_of_intervalIntegral_kgSinFreqOp_eq_zero`** | **built** |
| 142 | **the potential is determined by the field it produces** | **`eq_of_kgFieldMild_eq`**, **`kgFieldMild_injective_potential`** | **built** |
| 143 | **a source with no Duhamel term vanishes at every time** | `intervalIntegral_kgCosOp_eq_zero_of_kgSinFreqOp_eq_zero`, `intervalIntegral_kgSinFreqOp_shift`, **`eq_zero_of_intervalIntegral_kgSinFreqOp_eq_zero'`** | **built** |
| 144 | the Duhamel kernel of a time-dependent perturbation is strongly continuous | `kgFieldKernelT`, `norm_kgFieldKernelT_le`, **`strongKernel_kgFieldKernelT`** | **built** |
| 145 | **well-posedness with a time-dependent perturbation** | `kgFieldMildT`, `continuous_kgFieldMildT`, **`kgFieldMildT_eq`**, `kgFieldMildT_zero`, **`norm_kgFieldMildT_le`**, `eq_kgFieldMildT_of_duhamel`, **`exists_unique_kgFieldMildT`** | **built** |
| 146 | the autonomous theory is the constant case | `kgFieldKernelT_const`, `kgFieldMildT_const` | **built** |
| 147 | linearity in the data, and the solution operator | `kgFieldMildT_linear`, `kgFieldMildT_add`, `kgFieldMildT_smul`, `kgFieldMildT_sub`, `norm_kgFieldMildT_sub_le`, `kgSolutionTLM`, **`kgSolutionTCLM`**, `norm_kgSolutionTCLM_le` | **built** |
| 148 | **the solution is `C¹`, with the classical velocity** | `kgFieldMildT_eq_separated`, **`hasDerivAt_kgFieldMildT`**, `deriv_kgFieldMildT`, `kgFieldMildT_at_zero`, `deriv_kgFieldMildT_at_zero`, **`exists_kgFieldMildT_c1`** | **built** |
| 149 | **reversibility, with the time-reflected potential** | **`kgFieldMildT_neg`** | **built** |
| 150 | **the solution is Lipschitz in the moving background** | `kgFieldMildT_sub_potential`, `norm_kgFieldMildT_sub_potential_le_of_nonneg`, **`norm_kgFieldMildT_sub_potential_le`** | **built** |
| 151 | **the moving background is determined along the history of the field** | **`kgFieldMildT_potential_apply_eq`**, **`eq_zero_of_kgFieldMildT_eq`** | **built** |
| 152 | **the non-autonomous evolution is an evolution family** | **`kgFieldMildT_flow`** | **built** |
| 153 | **every regular vector is reached at every time** | **`exists_kgFieldMildT_eq`** | **built** |
| 154 | **the moving background is determined by the field it produces** | **`eq_of_kgFieldMildT_eq`**, **`kgFieldMildT_injective_potential`** | **built** |

Modules: `WaveEnergyGreenIdentity.lean` (1–3), `WaveDirectionalCalculus.lean` (4–5),
`WaveEnergyFlux.lean` (6–9), `WaveEnergyDerivative.lean` (10–12), `WaveCauchyUniqueness.lean` (13), `WaveTimeReflection.lean` (14), `WaveEnergyTwoSided.lean` (15), `WaveSolutionSpace.lean` (16), `WaveEventCoordinates.lean` (17), `WaveOperatorBridge.lean` (18–19), `WaveUniquenessEventForm.lean` (20), `WaveGreenIdentityIntegrable.lean` (21), `WaveEnergyFluxIntegrable.lean` (22), `WaveEnergyDerivativeIntegrable.lean` (23), `WaveEnergyDecaying.lean` (24–25), `WaveDecayingCompactSupport.lean` (26), `WaveDecayingReflection.lean` (27–28), `WaveDecayingEventForm.lean` (29), `WaveDecayingSharp.lean` (30), `WaveDecayingL2.lean` (31), `WaveDecayingL2Sub.lean` (32), `WaveL2Uniqueness.lean` (33), `WaveL2EventForm.lean` (34), `WaveDominationL2.lean` (35), `WaveDominationFactors.lean` (36), `WaveDominationSub.lean` (37), `WaveL2Capstone.lean` (38), `WaveL2CapstoneEvent.lean` (39), `WaveSourceFlux.lean` (41), `L2FourierMultiplier.lean` (46–47),
`L2MultiplierContinuity.lean` (48), `KleinGordonL2Propagator.lean` (49–52),
`VolterraStrongKernel.lean` (53), `KleinGordonMildSolution.lean` (54–56),
`KleinGordonL2Propagator.lean` and `L2FourierMultiplier.lean` again (57),
`KleinGordonEnergyConservation.lean` (58–60), `KleinGordonMildSolution.lean` again (61),
`L2FourierMultiplier.lean` again (62), `KleinGordonPropagatorDerivative.lean` (63–65),
`KleinGordonStrongSolution.lean` (66–69), `KleinGordonStrongUniqueness.lean` (70–73),
`KleinGordonPotentialStrong.lean` (74–78), `KleinGordonStrongStability.lean` (79–82),
`KleinGordonFieldMild.lean` (83–86), `KleinGordonFieldRegularity.lean` (87–88),
`KleinGordonDuhamelSeparation.lean` (89–90), `KleinGordonDuhamelDerivative.lean` (91–93),
`KleinGordonDuhamelFirstDerivative.lean` (94–96), `KleinGordonFieldVelocity.lean` (97–98),
`KleinGordonDuhamelSecondDerivative.lean` (99–102), `KleinGordonSmoothingStrong.lean` (103–106),
`KleinGordonSmoothingWellPosed.lean` (107–109), `KleinGordonSmoothingData.lean` (110–111),
`KleinGordonRegularDense.lean` (112–113), `KleinGordonFreqInvNotSurjective.lean` (114–116), `KleinGordonRegularitySharp.lean` (117–119),
`KleinGordonFieldFlow.lean` (120–121), `KleinGordonFieldEvolutionFamily.lean` (122–123),
`KleinGordonFieldRegularAlways.lean` (124–126), `KleinGordonFieldVelocityBound.lean` (127–128), `KleinGordonFieldStateStability.lean` (129–130), `KleinGordonFieldReversible.lean` (131–132), `KleinGordonFieldSolutionMap.lean` (133–134), `KleinGordonPotentialStability.lean` (135–138), `KleinGordonPotentialUniqueness.lean` (139–142), `KleinGordonSourceVanishing.lean` (143),
`KleinGordonTimePotential.lean` (144–147), `KleinGordonTimePotentialVelocity.lean` (148–149),
`KleinGordonTimePotentialStability.lean` (150–151), `KleinGordonTimePotentialFlow.lean` (152–154).
All wired into the umbrella; axioms `[propext, Classical.choice, Quot.sound]`.

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


### The energy method, in `L²`

The card opens with the energy method for pointwise solutions: differentiate
`E = ∫ (∂ₜu)² + |∇u|² + u²`, integrate the Laplacian by parts, and Grönwall. Statements 70–73 run the
same argument for the strong `L²` solutions of statement 68, and the whole of it — supports,
integration by parts, domination, differentiation under the integral — collapses to a single fact:
`⟨D⟩⁻¹` is **self-adjoint**, because its symbol `⟨ξ⟩⁻¹` is real (**`inner_kgFreqInvOp`**).

The conserved quantity needs no more derivatives than the equation supplies:

`F(t) = ‖⟨D⟩⁻¹∂ₜu(t)‖² + ‖u(t)‖²`.

Differentiating gives `2 Re⟪⟨D⟩⁻¹∂ₜu, ⟨D⟩⁻¹∂ₜ²u⟫ + 2 Re⟪u, ∂ₜu⟫`; moving one `⟨D⟩⁻¹` across the inner
product turns the first term into `2 Re⟪∂ₜu, ⟨D⟩⁻²∂ₜ²u⟫`, which the equation makes `-2 Re⟪∂ₜu, u⟫`,
cancelling the second. So **`kgStrongEnergy_const`**: `F` is constant. With vanishing Cauchy data
`F ≡ 0`, and since `F` dominates `‖u‖²`,

**`eq_zero_of_solvesKG`**: a strong solution with vanishing Cauchy data vanishes at every time,

and by linearity of the class (`SolvesKG.sub`), **`eq_of_solvesKG`**: two strong solutions with the
same field and velocity at time zero agree everywhere. Statement 73 closes the loop:
**`solvesKG_kgFreeField`** says the constructed field is such a solution — the class is inhabited,
not vacuous — and **`eq_kgFreeField_of_solvesKG`** says every strong solution with those Cauchy data
*is* the constructed field.

That is well-posedness of the strong Cauchy problem for the free equation: existence (68), the
estimate (69), and uniqueness (72), all three proved for the same class of objects, with the energy
argument of the card's opening paragraph carried out in `L²` rather than pointwise.


### The potential, in the strong theory

Statements 74–78 put the potential back. A bounded operator `W` on `L²` is added to the equation,

`∂ₜ²u = -⟨D⟩²u + Wu`,

and the free energy `F = ‖⟨D⟩⁻¹∂ₜu‖² + ‖u‖²` stops being conserved — but its derivative is controlled
*by itself*. The computation of statement 71 now leaves one surviving term,

`F'(t) = 2 Re⟪∂ₜu, ⟨D⟩⁻²(Wu)⟫`,

and the point is which side to move the two factors of `⟨D⟩⁻¹` to. Moving them **left**, onto `∂ₜu`,
gives `2 Re⟪⟨D⟩⁻²∂ₜu, Wu⟫`, whose first argument is a contraction of `⟨D⟩⁻¹∂ₜu` — one of the two terms
of `F` itself. So `|F'| ≤ 2‖⟨D⟩⁻¹∂ₜu‖·‖W‖·‖u‖ ≤ ‖W‖ F` (**`abs_deriv_kgStrongEnergy_le`**), and
mathlib's Grönwall closes it:

**`kgStrongEnergy_le_exp`**: `F(t) ≤ F(0)·e^{‖W‖t}` for `t ≥ 0`.

Moving them right instead would have produced `‖∂ₜu‖`, which `F` does not control — the estimate would
not close. That asymmetry is the whole content of the perturbed case.

Time reflection (`SolvesKGSource.comp_neg`) makes the estimate two-sided, so a solution with vanishing
Cauchy data vanishes at *every* time (**`eq_zero_of_solvesKGSource`**), and by linearity

**`eq_of_solvesKGSource`**: two strong solutions of `∂ₜ²u = -⟨D⟩²u + Wu` with the same Cauchy data
agree everywhere;

**`eq_of_solvesKGSource_potential`**: the same for `W` = multiplication by a measurable potential
bounded by `b` — no continuity, decay or smoothness of `V` anywhere.

That is the card's headline theorem — *"the Cauchy problem has at most one such solution"* — proved
for the clock equation with a genuinely rough potential, in a class of solutions the corpus can also
construct.


### Closing the perturbed theory, and one honest limit

Statements 79–82 finish the perturbed strong layer. Reflecting time carries a solution to a solution
and leaves the energy unchanged (`kgStrongEnergy_comp_neg`), so the Grönwall estimate holds on both
sides of the initial slice (**`kgStrongEnergy_le_exp_abs`**); the class is linear, so applying it to a
difference turns uniqueness into **continuous dependence** (**`kgStrongEnergy_sub_le_exp_abs`**) — the
same upgrade statement 15 makes for the pointwise theory. Statement 82 checks the two constructions
against each other: a potential vanishing almost everywhere collapses the perturbation series to its
first term, so **`kgMildSolution_of_ae_zero`** says the mild solution of the first-order system *is*
the propagator.

What is **not** available, and should not be claimed, is strong existence with a rough potential. The
Duhamel term of the second-order equation is `∫₀ᵗ (sin((t-s)⟨D⟩)/⟨D⟩) Wu(s) ds`; differentiating once
is harmless, but the second differentiation produces `∫₀ᵗ ⟨D⟩ sin((t-s)⟨D⟩) Wu(s) ds`, whose integrand
is **unbounded** unless `Wu(s)` is itself regular — and multiplication by a merely measurable bounded
`V` destroys frequency localisation, so `Vu(s)` is not. This is not a gap in the formalisation: a mild
solution with a rough potential genuinely need not be a strong one. The estimate (76), uniqueness (78)
and stability (80) hold for whatever strong solutions exist; existence at that regularity is the mild
theory of statements 54–56, and the bridge between them requires a smoothing hypothesis on `W`.


### The Duhamel formula one level down

The mild theory of statements 54–56 lives in the energy space, on pairs `(⟨D⟩u, ∂ₜu)`. Statements
83–86 write it where the classical theory writes it — for the field itself:

`u(t) = cos(t⟨D⟩)f + (sin(t⟨D⟩)/⟨D⟩)h + ∫₀ᵗ (sin((t-s)⟨D⟩)/⟨D⟩) W u(s) ds`.

Every operator here is a Fourier multiplier with symbol bounded by **one**, uniformly in time:
`|sin(r⟨ξ⟩)/⟨ξ⟩| ≤ ⟨ξ⟩⁻¹ ≤ 1`. That is the same cancellation which made the propagator differentiable
on regular data (statement 65), used here for a different purpose — it makes the half-order
propagator `kgSinFreqOp` a contraction, so the Volterra layer applies with **no regularity hypothesis
on the data at all**. `f` and `h` are arbitrary elements of `L²`:

**`exists_unique_kgFieldMild`**: for every `f, h ∈ L²` there is exactly one continuous curve
satisfying the Duhamel formula above; it starts at `f` (`kgFieldMild_zero`) and obeys

**`norm_kgFieldMild_le`**: `‖u(t)‖ ≤ (‖f‖+‖h‖)e^{‖W‖|t|}`.

Statement 86 identifies the two constructions of this card. `sin(t⟨D⟩)/⟨D⟩` is the energy-coordinate
sine composed with `⟨D⟩⁻¹` (`kgSinFreqOp_eq_comp`), so the strong field of statement 68 with datum
`(f, h)` is the field-level *free* solution with datum `(⟨D⟩⁻²f, ⟨D⟩⁻¹h)`, and hence

**`kgFreeField_eq_kgFieldMild`**: the strong solution **is** the mild solution of its own Cauchy
data.

So the card now carries the same equation in three registers — pointwise classical (1–45), first-order
mild in the energy space (46–61), and second-order strong and mild for the field (62–86) — with the
identifications between them proved wherever both are defined.


### How little regularity the first derivative needs

Statement 87 sharpens the differentiability hypothesis. Statement 67 differentiated the free field
*twice*, and for that both data had to be regularised. For the **first** derivative the velocity
datum needs nothing at all: `d/dt [sin(t⟨ξ⟩)/⟨ξ⟩] = cos(t⟨ξ⟩)` is bounded, so

**`hasDerivAt_kgSinFreqOp`**: `d/dt (sin(t⟨D⟩)/⟨D⟩)h = cos(t⟨D⟩)h` for **every** `h ∈ L²`,

and only the position datum has to carry one power of `⟨D⟩⁻¹` (**`hasDerivAt_kgFieldFree`**). With
`deriv_kgFieldFree_zero` the Cauchy data are read off exactly: the free field starts at the position
datum with velocity the velocity datum, and the velocity datum is arbitrary.

Statement 88 completes the field-level well-posedness triple. The Duhamel formula is linear in its
data, so the difference of two solutions is *itself* a solution — of the difference of the data
(**`kgFieldMild_sub`**, by uniqueness, once the two Duhamel integrals are subtracted, which needs the
interval integrability supplied by the strong continuity of the kernel). Applying the exponential
bound to that difference gives

**`norm_kgFieldMild_sub_le`**: `‖u₁(t) - u₂(t)‖ ≤ (‖f₁-f₂‖ + ‖h₁-h₂‖)e^{‖W‖|t|}`,

continuous dependence at the level of the field, for arbitrary `L²` data and any bounded
perturbation.


### Unentangling the two times

What blocks a naive differentiation of the Duhamel term is that the observation time `t` appears
*twice*: in the upper limit of the integral and inside the propagator `sin((t-s)⟨D⟩)/⟨D⟩`. Statements
89–90 unentangle them, and the tool is again the addition formula:

`sin((t-s)⟨ξ⟩)/⟨ξ⟩ = (sin(t⟨ξ⟩)/⟨ξ⟩)·cos(s⟨ξ⟩) - cos(t⟨ξ⟩)·(sin(s⟨ξ⟩)/⟨ξ⟩)`,

which at the operator level is **`kgSinFreqOp_sub`**. Substituting it and pulling the two
`t`-dependent factors out of the Bochner integral — legitimate precisely because they are *bounded*,
via `ContinuousLinearMap.intervalIntegral_comp_comm` — gives

**`intervalIntegral_kgFieldKernel_separated`**:
`∫₀ᵗ (sin((t-s)⟨D⟩)/⟨D⟩)g(s) ds = (sin(t⟨D⟩)/⟨D⟩)(∫₀ᵗ cos(s⟨D⟩)g(s) ds) - cos(t⟨D⟩)(∫₀ᵗ (sin(s⟨D⟩)/⟨D⟩)g(s) ds)`,

and hence the Duhamel formula itself in separated form (**`kgFieldMild_eq_separated`**). The
observation time now sits only in two fixed operators and in the upper limits; the source time only
inside the integrals. That is the shape in which the remaining differentiations become ordinary: the
upper limits fall to the fundamental theorem of calculus, and the two operators to the derivative
lemmas of statements 65 and 87.


### The three inputs the differentiation needs

With the times separated, the Duhamel term is `T₁(t)A(t) - T₂(t)B(t)` with `A, B` depending on `t`
only through their upper limits. Differentiating it needs three things, and statements 91–93 supply
all three.

**The product rule for a strongly differentiable family** (91). The operator families here are
*never* differentiable in the operator norm, only when applied to a fixed vector, so the usual product
rule does not apply as stated. But the splitting

`T(s)y(s) - T(t)y(t) = T(s)(y(s) - y(t)) + (T(s) - T(t))y(t)`

works: divided by `s-t`, the first term is `T(s)` applied to the slope of `y`, which converges by the
*joint* continuity of a uniformly bounded strongly continuous family (statement 49), and the second is
the slope of `s ↦ T(s)y(t)` at a fixed vector, which converges by hypothesis. That is
**`hasDerivAt_strong_apply`**, and it is the piece of infrastructure the whole differentiation rests
on.

**The regularity of the integrals** (92). The product rule's hypothesis is a derivative at the fixed
vector `y(t)`, and for the cosine propagator that vector has to lie in the range of `⟨D⟩⁻¹`. It does:
`sin(s⟨D⟩)/⟨D⟩ = ⟨D⟩⁻¹ ∘ sin(s⟨D⟩)`, and `⟨D⟩⁻¹` is *bounded*, so it passes through the Bochner
integral — **`intervalIntegral_kgSinFreqOp_eq`** exhibits `∫₀ᵗ (sin(s⟨D⟩)/⟨D⟩)g(s) ds` as `⟨D⟩⁻¹`
applied to another integral.

**The endpoint derivatives** (93), which are the fundamental theorem of calculus for a continuous
Banach-valued integrand.


### The Duhamel term differentiated

Statements 94–96 carry out the differentiation. Applying the product rule of statement 91 to each
half of the separated term gives four contributions:

`d/dt[(sin(t⟨D⟩)/⟨D⟩)A(t)] = (sin(t⟨D⟩)/⟨D⟩)(cos(t⟨D⟩)g(t)) + cos(t⟨D⟩)A(t)`,
`d/dt[cos(t⟨D⟩)B(t)] = cos(t⟨D⟩)(⟨D⟩⁻¹ sin(t⟨D⟩)g(t)) - sin(t⟨D⟩)C(t)`,

the second using that `B(t) = ⟨D⟩⁻¹C(t)` is regular (statement 92), which is exactly what the cosine
propagator's derivative asks for. Subtracting, the **endpoint contributions cancel**: they are
`(sin(t⟨D⟩)/⟨D⟩)cos(t⟨D⟩)g(t)` and `cos(t⟨D⟩)(sin(t⟨D⟩)/⟨D⟩)g(t)`, equal because the multipliers
commute (**`kgSinFreqOp_comm_kgCosOp`**). What survives is

`cos(t⟨D⟩)A(t) + sin(t⟨D⟩)C(t)`,

and the cosine subtraction law `cos((t-s)⟨ξ⟩) = cos(t⟨ξ⟩)cos(s⟨ξ⟩) + sin(t⟨ξ⟩)sin(s⟨ξ⟩)`
(**`kgCosOp_sub`**) recombines it into one integral. So

**`hasDerivAt_kgDuhamel`** with **`kgDuhamel_deriv_eq`**:
`d/dt ∫₀ᵗ (sin((t-s)⟨D⟩)/⟨D⟩)g(s) ds = ∫₀ᵗ cos((t-s)⟨D⟩)g(s) ds`,

the classical formula, for any continuous `g` and with no regularity hypothesis whatever. The
cancellation of the endpoint terms is why the first derivative is free; it is the *second*
differentiation, where `⟨D⟩ sin((t-s)⟨D⟩)` appears with nothing to absorb the `⟨D⟩`, that needs `g`
itself to be regular.


### The variation-of-constants formula for the velocity

Adding the derivative of the free field (statement 87) to the derivative of the Duhamel term
(statement 96) gives the velocity of the mild solution in closed form:

**`deriv_kgFieldMild`**: `∂ₜu(t) = -sin(t⟨D⟩)g + cos(t⟨D⟩)h + ∫₀ᵗ cos((t-s)⟨D⟩) W u(s) ds`

for the Cauchy data `u(0) = ⟨D⟩⁻¹g`, `∂ₜu(0) = h`. One power of `⟨D⟩⁻¹` on the position datum is the
*only* regularity used anywhere: the velocity datum `h` and the perturbation `W` are arbitrary.

At `t = 0` the integral vanishes, `sin(0⟨D⟩) = 0` and `cos(0⟨D⟩) = 1`, so the formula returns `h`
(**`deriv_kgFieldMild_at_zero`**). Together with `kgFieldMild_at_zero` that is

**`exists_kgFieldMild_c1`**: *for every `g, h ∈ L²` and every bounded perturbation there is a
differentiable curve satisfying the field-level Duhamel formula, with position datum `⟨D⟩⁻¹g` and
velocity datum `h`* — the Cauchy problem solved in the `C¹` sense with the data one prescribes,
uniqueness already being statement 85.

The programme of the card is now closed in the direction it was opened. The estimate of statements
1–45 controls a solution by its data; statements 46–98 construct that solution — mild in the energy
space, mild and `C¹` at the level of the field, strong for regular data — and prove for each
construction the same three theorems the pointwise theory has: existence, the exponential energy
bound, and uniqueness.


### Where the regularity of the source is finally used

The velocity carries the integral `∫₀ᵗ cos((t-s)⟨D⟩)k(s) ds`, and differentiating it once more is the
step the card recorded as blocked. Statements 99–102 unblock it, and identify exactly what the
blockage was.

Separating the times again writes the integral as `cos(t⟨D⟩)P(t) + sin(t⟨D⟩)Q(t)` with
`P(t) = ∫₀ᵗ cos(s⟨D⟩)k`, `Q(t) = ∫₀ᵗ sin(s⟨D⟩)k`. The product rule of statement 91 now needs `P(t)`
and `Q(t)` in the range of `⟨D⟩⁻¹` — and they are there **exactly when `k` is**, because a bounded
operator passes through the integral (statement 100). That is the whole obstruction: a merely bounded
potential does not put `Vu(s)` in that range.

For `k = ⟨D⟩⁻¹k₀` the computation closes, and closes beautifully. The two endpoint contributions are
`cos(t⟨D⟩)⟨D⟩⁻¹cos(t⟨D⟩)k₀(t)` and `sin(t⟨D⟩)⟨D⟩⁻¹sin(t⟨D⟩)k₀(t)`, whose sum is `⟨D⟩⁻¹k₀(t) = k(t)` by
the **Pythagorean identity** of statement 59 (**`kgEndpoint_sum`**); the two surviving terms recombine
by the sine subtraction law (**`kgSinOp_sub`**, **`kgSinDuhamel_recombine`**). So

**`hasDerivAt_kgCosDuhamel`**:
`d/dt ∫₀ᵗ cos((t-s)⟨D⟩)k(s) ds = k(t) - ∫₀ᵗ sin((t-s)⟨D⟩)k₀(s) ds`  for `k = ⟨D⟩⁻¹k₀`.

The `k(t)` is the source term of the equation appearing from the endpoint, exactly as the classical
derivation predicts, and the remaining integral is the one the second derivative of the field needs.


### Mild becomes strong, and the perturbed theory closes

Statements 103–106 build the bridge the card recorded as missing. The obstruction was that the
second differentiation of the Duhamel term produces `⟨D⟩ sin((t-s)⟨D⟩)Wu(s)` with nothing to absorb
the `⟨D⟩`. What absorbs it is a factor `⟨D⟩⁻¹` in the perturbation itself:

`W = ⟨D⟩⁻¹W₀`,  `W₀` bounded (**`kgSmoothingOp`**, of norm at most `‖W₀‖`).

With Cauchy data `⟨D⟩⁻²g₀` and `⟨D⟩⁻¹h₀`, the field-level mild solution is differentiable
(statement 97), and its velocity is differentiable too because the source `Wu(s) = ⟨D⟩⁻¹(W₀u(s))` is
regular — that is statement 102 applied verbatim (**`hasDerivAt_kgSmoothVel`**). Statement 105 then
exhibits the solution as doubly regular,

`u(t) = ⟨D⟩⁻²(cos(t⟨D⟩)g₀ + sin(t⟨D⟩)h₀ + ∫₀ᵗ sin((t-s)⟨D⟩)W₀u(s) ds)`,

which is what turns the derivative identity into the equation. The result is

**`solvesKGSource_kgSmoothMild`**: *the constructed field is a strong solution of
`⟨D⟩⁻²(∂ₜ²u) = -u + ⟨D⟩⁻²(Wu)`.*

So the perturbed strong theory is no longer about a hypothetical class. Its estimate (76), its
uniqueness (78) and its stability (80) now apply to an object the corpus builds, and
**`kgStrongEnergy_kgSmoothMild_le`** states the first of these for it directly:
`F(t) ≤ F(0)e^{‖W₀‖|t|}`. Existence, estimate and uniqueness hold together, for the same solution, in
the perturbed second-order equation — which is what the card set out to prove, in the one regularity
class where all three are true.


### The three theorems, about one object

Statements 107–109 state the conclusion in one place. The constructed solution starts at the
prescribed Cauchy data (`kgSmoothMild_at_zero`, `kgSmoothVel_at_zero`), so the uniqueness of the
perturbed strong theory identifies it: every strong solution with those data *is* it
(**`eq_kgSmoothMild_of_solvesKGSource`**). Collecting existence, the estimate and uniqueness:

**`wellPosed_solvesKGSource_smoothing`**: *for `W = ⟨D⟩⁻¹W₀` with `W₀` bounded by `b`, and every
`g₀, h₀ ∈ L²`, there are `u, v, a` with `SolvesKGSource W u v a`, `u(0) = ⟨D⟩⁻²g₀`,
`v(0) = ⟨D⟩⁻¹h₀`, `F(t) ≤ F(0)e^{b|t|}`, and every strong solution with those data equals `u`.*

Statement 109 instantiates it at the case the clock programme cares about: `W₀` = multiplication by a
bounded **measurable** potential, so `W = ⟨D⟩⁻¹M_V`. No continuity, decay or smoothness of `V` is
used anywhere — one power of `⟨D⟩⁻¹` is the entire price of passing from the mild theory, where
nothing is assumed, to the strong theory, where the equation holds pointwise in time as an identity
in `L²`.

This is the card's original sentence — *the energy is controlled by the data, and the Cauchy problem
has at most one such solution* — with the missing third clause supplied: **and it has one**.


### Stated in the data one prescribes

Statements 110–111 finish the arc by removing the last place where a theorem referred to the solution
rather than to the data. The energy at time zero is explicit,
`F(0) = ‖⟨D⟩⁻²h₀‖² + ‖⟨D⟩⁻²g₀‖²`, so the Grönwall estimate becomes

**`kgStrongEnergy_kgSmoothMild_le_data`**: `F(t) ≤ (‖⟨D⟩⁻²h₀‖² + ‖⟨D⟩⁻²g₀‖²)e^{b|t|}`,

a bound by the prescribed Cauchy data alone, and `norm_kgSmoothMild_le` does the same for the field.
The construction is linear in the data (**`kgSmoothMild_sub`**: the difference of two solutions is the
solution of the difference), so the same bound applied to a difference is

**`norm_kgSmoothMild_sub_le`**: `‖u₁(t) - u₂(t)‖ ≤ (‖⟨D⟩⁻²(g₁-g₂)‖ + ‖⟨D⟩⁻¹(h₁-h₂)‖)e^{b|t|}`.

With that the card carries the classical local theory of the clock equation in full, in every
register it can be stated in, with existence, the exponential energy estimate, uniqueness and
continuous dependence proved for each — and with the one honest limit (a rough, unsmoothed potential
gives a mild solution that need not be strong) recorded as the mathematical fact it is.


### How large the regular class is

Every strong statement here asks the Cauchy data to lie in the range of `⟨D⟩⁻¹` or `⟨D⟩⁻²`. That is a
genuine restriction — `⟨D⟩⁻¹` is not surjective — and a development that never measured it would be
open to the charge that its hypothesis class is thin. Statements 112–113 measure it.

The argument is the one running through the whole card, used a third time. The symbol `⟨ξ⟩⁻¹` is
**nowhere vanishing**, which makes the multiplier injective (**`kgFreqInvOp_injective`**), and it is
**real**, which makes the multiplier self-adjoint (statement 70). An injective self-adjoint operator
on a Hilbert space has dense range: a vector orthogonal to the range satisfies `⟪f, Ag⟫ = 0` for every
`f`, hence `Ag = 0`, hence `g = 0`. So

**`denseRange_kgFreqInvOp`**, and by composition **`denseRange_kgFreqInvOp_two`**: the singly and
doubly regular vectors are **dense** in `L²`.

The strong solutions of statements 68 and 106 are therefore constructed on a dense set of Cauchy data,
and the continuous dependence of statement 111 propagates them from there as far as any solution
concept allows. The hypothesis class is not thin; it is dense, and the mild theory — which assumes
nothing — is what covers the rest.


### The restriction is genuine, not just non-trivial

Statement 113 says the regular data are dense. That leaves the opposite question, and a docstring
claiming `⟨D⟩⁻¹` is not surjective would be an unproved assertion sitting inside a formalisation.
Statements 114–116 prove it.

Were `⟨D⟩⁻¹` surjective it would be bijective — injectivity is statement 112 — and the open mapping
theorem would give a bounded inverse, hence `‖x‖ ≤ K‖⟨D⟩⁻¹x‖` for all `x`. But the multiplier shrinks
by `⟨R⟩⁻¹` anything living at frequencies of size at least `R`: the witness is the indicator of the
unit ball around a frequency of norm `K+1`, which has positive finite measure and is therefore a
nonzero element of `L²` (**`kgBallFun_ne_zero`**), pulled back through Plancherel. Taking `R = K`
gives `K < √(1+K²)`, and the two inequalities contradict each other.

**`not_surjective_kgFreqInvOp`**: *on a space of positive dimension, `⟨D⟩⁻¹` is not surjective.*

The hypothesis `0 < dim` is not decoration: in dimension zero `⟨ξ⟩ ≡ 1` and the operator *is* the
identity. So the strong theory is strictly narrower than the mild one, exactly as the mild-versus-
strong discussion of statement 82 requires — and the dense-range statement 113 says how much
narrower: not much, but not nothing.


### The hypothesis is the domain, not a convenience

Statement 65 differentiates `t ↦ sin(t⟨D⟩)x` for `x` in the range of `⟨D⟩⁻¹`, and every regularity
hypothesis downstream descends from it. Statements 117–119 show that hypothesis is not an artifact of
the proof: it is *exactly* the set on which the curve is differentiable.

The mechanism is the sinc function. The difference quotient of `sin(t⟨ξ⟩)` at the origin is
`sin(t⟨ξ⟩)/t`, unbounded in `ξ` — which is why the derivative can fail to exist. But one power of
`⟨D⟩⁻¹` turns it into `sin(t⟨ξ⟩)/(t⟨ξ⟩)`, bounded by **one** and converging pointwise to **one**
(**`tendsto_kgSinc`**). So statement 48 makes `⟨D⟩⁻¹` applied to the difference quotient converge to
the datum itself; and if a derivative `L` exists, continuity of `⟨D⟩⁻¹` makes it converge to
`⟨D⟩⁻¹L`. Uniqueness of limits gives

**`mem_range_kgFreqInvOp_of_hasDerivAt`**: `⟨D⟩⁻¹L = k` — the datum is regular, and the derivative is
its regularising vector,

and with statement 65 for the converse, **`hasDerivAt_kgSinOp_iff`**: *the curve `t ↦ sin(t⟨D⟩)k` is
differentiable at the origin if and only if `k` lies in the range of `⟨D⟩⁻¹`.*

Together with statements 113 and 116 the regular class is now completely described: it is dense
(113), it is not everything (116), and it is precisely the domain of the derivative the whole strong
theory is built on (119).


### The evolution is a flow

The equation is autonomous, so a solution restarted from its own state at an intermediate time should
continue the same solution. Statements 120–121 prove that for the free field, and the proof is again
the addition laws — this time all three of them at once.

Expanding `kgFieldFree (⟨D⟩⁻¹g) h (t+s)` and the restarted solution
`kgFieldFree (u(s)) (∂ₜu(s)) t`, the position datum is moved by the cosine addition law
(`kgCosOp_add`), the velocity datum by the **half-order** sine addition law
(**`kgSinFreqOp_add`**, new here), and the two cross terms match because
`(sin(t⟨D⟩)/⟨D⟩)sin(s⟨D⟩)g = sin(t⟨D⟩)sin(s⟨D⟩)⟨D⟩⁻¹g` — the commutation of the multipliers, which is
what lets the `⟨D⟩⁻¹` migrate from the propagator to the datum. Hence

**`kgFieldFree_flow`**: `u(t+s) = [the solution with data (u(s), ∂ₜu(s))](t)`.

The position datum must carry one power of `⟨D⟩⁻¹` — not for the identity itself but because the
velocity at the intermediate time is only defined there (statement 119 shows that is exactly the
domain); the velocity datum is arbitrary.


### The perturbed evolution is an evolution family

Statement 121 makes the free evolution a flow. Statements 122–123 do the same with a perturbation
present, and the proof is uniqueness rather than algebra.

The shifted curve `τ ↦ u(τ+s)` is continuous, so it is enough to check that it satisfies the Duhamel
formula with data `(u(s), ∂ₜu(s))`. Splitting `∫₀^{τ+s}` at `s` separates two contributions. The late
part, `∫_s^{τ+s}`, becomes the Duhamel integral of the shifted curve by the change of variable
`r = ρ + s`. The early part combines with the free field: **`kgFieldFree_restart`** shows that the
free field at `τ+s` plus the accumulated source `∫₀^s (sin((τ+s-r)⟨D⟩)/⟨D⟩)k(r)dr` is exactly the free
field restarted from the accumulated state — the flow identity of statement 121 for the datum, and
the addition law `kgSinFreqOp_add` applied *under the integral sign* for the source, with `t` and
`s-r` as its two arguments.

Uniqueness (statement 85) then gives

**`kgFieldMild_flow`**: `u(t+s) = [the solution with data (u(s), ∂ₜu(s))](t)`,

for any bounded perturbation and any `L²` velocity datum. The solution operator is an evolution
family, which is the last structural property the classical theory asks of it.


### The regularity propagates

The evolution family of statement 123 restarts the solution from its state at time `s`. For that to
be iterable the restarted position datum must itself be regular — otherwise the velocity at the next
restart is undefined and the family stops after one step. Statements 124–126 show it always is.

Both terms of the Duhamel formula carry the factor. The free part is
`cos(t⟨D⟩)⟨D⟩⁻¹g + (sin(t⟨D⟩)/⟨D⟩)h = ⟨D⟩⁻¹(cos(t⟨D⟩)g + sin(t⟨D⟩)h)` (**`kgFieldFree_freqInv`**), and
the Duhamel integrand is `(sin((t-r)⟨D⟩)/⟨D⟩)Wu(r) = ⟨D⟩⁻¹(sin((t-r)⟨D⟩)Wu(r))`, whose `⟨D⟩⁻¹` passes
through the Bochner integral because it is bounded. So

**`kgFieldMild_freqInv`**: `u(t) = ⟨D⟩⁻¹(cos(t⟨D⟩)g + sin(t⟨D⟩)h + ∫₀ᵗ sin((t-r)⟨D⟩)Wu(r)dr)`

— the solution never leaves the range of `⟨D⟩⁻¹`, and the regularising curve is explicit. Hence
**`hasDerivAt_kgFieldMild_restart`**: the restarted solution has a velocity at every time, and the
evolution family can be iterated indefinitely.

This also closes a loop with statement 119: the domain of differentiability is exactly the range of
`⟨D⟩⁻¹`, and the evolution preserves it. The hypothesis is not just dense (113) and genuine (116) —
it is *invariant*.


### The velocity is bounded too

Statement 85 bounds the field; nothing so far bounded its velocity, which is the other half of the
state the evolution family carries. Statements 127–128 close that.

The closed formula of statement 97 makes it immediate once the pieces are named. The two propagator
terms `-sin(t⟨D⟩)g + cos(t⟨D⟩)h` are contractions of the data, contributing `‖g‖ + ‖h‖`. The Duhamel
term `∫₀ᵗ cos((t-s)⟨D⟩)Wu(s)ds` is estimated by the supremum of its integrand: `cos` is a contraction,
`‖W‖ ≤ b`, and `‖u(s)‖ ≤ (‖g‖+‖h‖)e^{b|t|}` for `s` between `0` and `t` (**`norm_kgFieldMild_le_data`**,
the field bound rewritten in the raw data). That contributes a factor `b|t|`, and `1 + x ≤ eˣ` absorbs
it:

**`norm_deriv_kgFieldMild_le`**: `‖∂ₜu(t)‖ ≤ (‖g‖ + ‖h‖)e^{2‖W‖|t|}`.

So the full state `(u(t), ∂ₜu(t))` — the object the evolution family of statement 123 propagates and
the object statement 126 shows stays regular — is bounded by its data, exponentially, at a rate set by
the perturbation alone.


### Both components of the state are stable

The evolution family propagates the pair `(u(t), ∂ₜu(t))`. Statement 88 made the position depend
continuously on the data; statements 129–130 do the same for the velocity, and state the two
together.

The construction is linear in the data (statement 88), so the difference of two solutions *is* the
solution of the difference. Uniqueness of derivatives then transfers that to the velocities
(**`deriv_kgFieldMild_sub`**): the difference of the two velocities is the velocity of the difference
solution. The bound of statement 128 applied to it gives

**`norm_deriv_kgFieldMild_sub_le`**: `‖∂ₜu₁(t) - ∂ₜu₂(t)‖ ≤ (‖g₁-g₂‖ + ‖h₁-h₂‖)e^{2‖W‖|t|}`,

and **`kgFieldMild_state_stability`** collects it with the position estimate in one statement. So the
field-level theory now has, for the *whole* state and in the raw Cauchy data, all four classical
properties: existence (85), uniqueness (85), the exponential bounds (85, 128), and continuous
dependence (130) — with the flow structure (123) and the invariance of the regular class (126) on
top.


### Reversibility

The equation contains only the second time derivative, so reversing time must carry a solution to a
solution with the velocity reversed. Statements 131–132 prove it.

At the level of the propagators this is the parity of the trigonometric functions: the cosine symbol
is even (**`kgCosOp_neg`**) and the half-order sine symbol is odd (**`kgSinFreqOp_neg`**), so the free
field satisfies `u(-t) = [the solution with datum (f, -h)](t)` (**`kgFieldFree_neg`**).

For the mild solution the Duhamel integral must be reversed too, and the change of variable `r ↦ -r`
does it: **two** sign changes appear — one from the orientation of the interval, one from the oddness
of the propagator — and they cancel. So the reflected curve satisfies the Duhamel formula with the
reflected data, and uniqueness gives

**`kgFieldMild_neg`**: `u(-t) = [the solution with data (f, -h)](t)`,

for any bounded perturbation and arbitrary `L²` data — no regularity, since no derivative appears in
the statement. With the flow property of statement 123 this makes the solution operator a genuine
*group* in the free case and a reversible evolution family in general.


### The solution operator

Everything so far speaks of *a* solution for given data. Statements 133–134 turn the correspondence
itself into an object. The Duhamel formula is additive and homogeneous in its data
(**`kgFieldMild_add`**, **`kgFieldMild_smul`** — each proved the way every structural property here
is proved: the candidate curve is continuous, satisfies the Duhamel formula with the corresponding
data, and uniqueness identifies it), so for each time

**`kgSolutionCLM`**: `(f, h) ↦ u(t)` is a **continuous linear map** `L² × L² → L²`,

with **`norm_kgSolutionCLM_le`**: `‖S(t)‖ ≤ 2e^{‖W‖|t|}`. Composed with the flow property (123), the
reversibility (132) and the derivative formula (97), the whole classical structure of the equation is
now carried by a single family of bounded operators indexed by time.

### Varying the equation instead of the data

Every stability statement up to 130 varies the Cauchy data and holds the equation fixed. Statements
135–138 do the opposite, which is the variation an inverse problem actually cares about: the datum is
known and the potential is not.

Subtracting the two Duhamel formulas and splitting

`W₁u₁ - W₂u₂ = (W₁-W₂)u₁ + W₂(u₁-u₂)`

separates the two effects (**`kgFieldMild_sub_potential`**). The first term is a genuine source, of
size `‖W₁-W₂‖·‖u₁(s)‖`, and the a-priori bound of statement 85 makes it uniform on a compact time
interval; the second is the same memory term the solution already had, of size `‖W₂‖·‖u₁(s)-u₂(s)‖`.
So `d(x) := ‖u₁(x)-u₂(x)‖` satisfies

`d(x) ≤ δ·(‖f‖+‖h‖)·e^{bt}·t + ∫₀ˣ b·d(s) ds`

on `[0,t]`, and the corpus's integral Grönwall inequality (`le_mul_exp_integral_of_le_add_integral`)
closes it. The constant that comes out is sharp in the only sense that matters here — it vanishes at
`t = 0` and is linear in `t` for short times:

**`norm_kgFieldMild_sub_potential_le`**: `‖u₁(t) - u₂(t)‖ ≤ ‖W₁-W₂‖·(‖f‖+‖h‖)·|t|·e^{2‖W‖|t|}`.

The negative-time half is not a second argument: reversibility (132) turns it into the positive-time
statement with the velocity datum negated, and `‖-h‖ = ‖h‖` leaves the constant untouched.

Two consequences. On a bounded set of data and a bounded time interval the estimate is uniform
(**`norm_kgFieldMild_sub_potential_le_of_le`**), so the map `W ↦ u` is Lipschitz there with an
explicit constant. And a net of uniformly bounded potentials converging in operator norm produces a
net of fields converging in `L²` at every time (**`tendsto_kgFieldMild_of_tendsto_potential`**) — the
forward map of the inverse problem is continuous, which is the statement that has to be in place
before any question of recovering `W` from observations of `u` can be posed. The estimate is
one-sided by construction: it says nothing about the inverse, and the exponential factor is exactly
the room in which ill-posedness lives.

### The forward map is injective

Statements 139–142 close the other half. Suppose two bounded perturbations produce the *same* field
from every Cauchy datum, and write `A := W₁ - W₂`. Statement 135 collapses: the memory term is
`W₂` applied to a difference that is identically zero, so what is left is

`∫₀ˣ (sin((x-s)⟨D⟩)/⟨D⟩) A(u(s)) ds = 0` for every `x`,

with `u := u(W₁, f, 0)` the common solution. This is a statement about the Duhamel term of an
arbitrary continuous source, so it wants the source-level versions of the differentiation results the
card already has. Instantiating the separated form (90) at the identity operator gives them for free
(**`hasDerivAt_intervalIntegral_kgSinFreqOp`**): differentiating once, again with no hypothesis on
the source beyond continuity,

`∫₀ˣ cos((x-s)⟨D⟩) A(u(s)) ds = 0` for every `x`.

The second differentiation is the delicate one, and it is where the whole card's obstruction lives:
away from the origin the derivative of the cosine Duhamel term produces `⟨D⟩ sin((x-s)⟨D⟩)`, which is
unbounded, and that is precisely what forced the smoothing hypothesis of statements 103–109. At the
origin the obstruction is absent, because the only surviving contribution is the endpoint one. The
proof of **`hasDerivAt_intervalIntegral_kgCosOp_zero`** is therefore elementary and does not use the
machinery of 99–102 at all: `cos(0·⟨D⟩) = I`, so on `[0,x]` the integrand differs from `g(0)` by

`cos((x-s)⟨D⟩)(g(s)-g(0)) + (cos((x-s)⟨D⟩) - I)g(0)`,

whose two terms are controlled by the continuity of `g` at `0` and the strong continuity of the
cosine propagator at `0` — the first because the propagator is a contraction, the second because
`|x-s| ≤ 2|x|` on the interval. Both are uniform in `s ∈ [0,x]`, so the integral is `x·g(0) + o(x)`
and the derivative at the origin is `g(0)`.

Applying it to the identically vanishing integral gives `A(u(0)) = 0`, and `u(0) = f`. Since `f` was
arbitrary,

**`eq_of_kgFieldMild_eq`**: `(∀ f, h, t, u_{W₁}(t) = u_{W₂}(t)) → W₁ = W₂`.

With the Lipschitz estimate this makes `W ↦ u` a continuous injection on every operator-norm ball:
the observations determine the equation, and they determine it stably in the forward direction. What
remains genuinely open — and is not a Lean gap but a mathematical one — is the modulus of continuity
of the inverse, which no argument on this card bounds.

### The background may move

A clock does not read a static field. Statements 144–151 replace the fixed operator `W` by a curve of
them, `∂ₜ²u = -⟨D⟩²u + W(t)u`, which is the equation an observer in a time-varying background
actually solves.

Nothing in the Volterra layer ever used the autonomy of the kernel — it is stated for an arbitrary
strongly continuous, uniformly bounded family `K(t,s)` — so existence, uniqueness and the exponential
bound transfer once the kernel `sin((t-s)⟨D⟩)/⟨D⟩ ∘ W(s)` is shown strongly continuous. The
hypotheses on `W` that do it are the corpus's own idiom for a propagator family: a uniform norm bound
and strong continuity. The autonomous theory is the constant case, definitionally
(**`kgFieldMildT_const`** is `rfl`).

Three structural facts survive the move, each with a proof that is the autonomous one with the
perturbation evaluated at the source time.

*Differentiability.* The velocity formula costs nothing extra, because the derivative of the Duhamel
term (statement 139) was proved for an **arbitrary** continuous source, and `s ↦ W(s)u(s)` is
continuous exactly under the two hypotheses already assumed. So the Cauchy problem is again solved in
the `C¹` sense with the data one prescribes (**`exists_kgFieldMildT_c1`**).

*Reversibility.* Here the statement genuinely changes: reversal acts on the equation, not only on the
datum. Running the solution backwards is running the solution of the **time-reflected** equation
`r ↦ W(-r)` forwards, with the velocity datum negated (**`kgFieldMildT_neg`**). It degenerates to the
autonomous statement when `W` is constant.

*Stability and injectivity.* Grönwall gives the same Lipschitz constant as before, now with `δ` a
uniform bound on `‖W₁(r)-W₂(r)‖` (**`norm_kgFieldMildT_sub_potential_le`**). The injectivity half is
sharper here than in the autonomous case, and the reason is statement 143: the vanishing theorem for
Duhamel sources holds at **every** time, not only at the origin. That upgrade is algebraic rather
than analytic — translating the source by `r` changes its Duhamel term by an off-diagonal piece which
the addition law `sinFreq(y + a) = cos(y)sinFreq(a) + sinFreq(y)cos(a)` splits into `cos(y⟨D⟩)`
applied to the sine Duhamel term at `r` plus `sin(y⟨D⟩)/⟨D⟩` applied to the cosine one, and both of
those vanish (the first by hypothesis, the second because it is its derivative). So the translated
source again has a vanishing Duhamel term and the origin statement applies to it. The consequence is

**`kgFieldMildT_potential_apply_eq`**: if two moving backgrounds produce the same field from every
Cauchy datum, then `W₁(r)` and `W₂(r)` agree on the state the field occupies at time `r`, for every
`r` and every datum

— a statement about the whole history rather than one instant. At `r = 0` the state is the datum
itself, so `W₁(0) = W₂(0)` unconditionally (**`eq_zero_of_kgFieldMildT_eq`**).

### Reaching every state, and closing the inverse problem

Statement 151 identifies `W₁(r)` with `W₂(r)` only on the states the field actually occupies at time
`r`. Statements 152–154 show that set is dense, which upgrades it to `W₁ = W₂`.

The instrument is the evolution-family property, and for a non-autonomous equation it has to restart
the equation as well as the state: seen from time `s`, the potential is `W(· + s)`, so

**`kgFieldMildT_flow`**: `u(t+s) = u_{W(·+s), (u(s), ∂ₜu(s))}(t)`.

The proof is the autonomous one (statement 123) with the potential evaluated at the source time —
split the Duhamel integral at `s`, recombine the early part with the free field by the addition law
`sinFreq(t + a) = cos(t)sinFreq(a) + sinFreq(t)cos(a)`, change variables in the late part, and let
uniqueness identify the shifted curve.

Run it backwards and it produces data. Given a regular target `v = ⟨D⟩⁻¹g` and a time `r`, solve the
*forward-shifted* equation `W(r + ·)` from `v` with zero velocity, obtaining a curve `z` with
`z(0) = v`; restart `z` at time `-r` and the shifted potential `ρ ↦ W(r + (ρ - r))` is `W` again, so
the restarted curve solves the *original* equation and passes through `v` at time `r`:

**`exists_kgFieldMildT_eq`**: `∀ g, ∀ r, ∃ f h, u_{f,h}(r) = ⟨D⟩⁻¹g`.

This is worth noting for what it is not: the free map `(f,h) ↦ cos(r⟨D⟩)f + (sin(r⟨D⟩)/⟨D⟩)h` is
**not** surjective onto `L²`, because inverting the second symbol costs a factor `⟨ξ⟩`. Exactly that
factor is the regularity `⟨D⟩⁻¹g` carries, and running the equation backwards supplies the datum
without any frequency decomposition.

The regular vectors are dense (statement 113), the two perturbations are continuous, and they agree
on a dense set — so

**`eq_of_kgFieldMildT_eq`**: two uniformly bounded, strongly continuous moving backgrounds producing
the same field from every Cauchy datum are equal at every time.

Together with statement 150 this makes the forward map of the inverse problem a continuous injection
on moving backgrounds (**`kgFieldMildT_injective_potential`**), and it contains statement 142 as the
constant case. What remains open is the same thing as in the autonomous case and is not a Lean gap:
the modulus of continuity of the inverse.

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
- 2026-08-04 — statements 152–154: **the inverse problem closes for moving backgrounds.** The
  non-autonomous evolution family restarts the equation as well as the state; run backwards it
  reaches every regular vector at every time, so the reachable set is dense and `W₁ = W₂` follows
  from agreement on it. The free propagator alone is *not* surjective — the regularity of the target
  is exactly the factor `⟨ξ⟩` that inverting `sin(r⟨ξ⟩)/⟨ξ⟩` costs.
- 2026-08-04 — statements 143–151: **the background may move.** The Volterra layer never used the
  autonomy of the kernel, so well-posedness, `C¹` regularity, reversibility (with the time-reflected
  potential) and Lipschitz stability all transfer to `∂ₜ²u = -⟨D⟩²u + W(t)u`. Statement 143 upgrades
  the source-vanishing theorem from the origin to every time by an addition-law identity, and with it
  the moving background is determined along the whole history of the field.
- 2026-08-04 — statements 139–142: **the potential is determined by the field it produces.** The
  Duhamel term of an arbitrary continuous source is differentiable, and the cosine Duhamel term has
  derivative `g(0)` at the origin — where the unbounded-generator obstruction of 99–109 is absent
  because only the endpoint term survives. Hence `W ↦ u` is injective, and with 135–138 a continuous
  injection.
- 2026-08-04 — statements 135–138: the solution is Lipschitz in the **perturbation**, not only in the
  data — `‖u₁(t)-u₂(t)‖ ≤ ‖W₁-W₂‖(‖f‖+‖h‖)|t|e^{2b|t|}` by the corpus's integral Grönwall inequality;
  hence the forward map of the inverse problem is continuous.
- 2026-08-04 — statements 133–134: linearity of the solution in its data, and the solution operator
  as a continuous linear map with an explicit operator-norm bound.
- 2026-08-04 — statements 131–132: parity of the propagators and reversibility of the field
  evolution; the two sign changes in the reversed Duhamel integral cancel.
- 2026-08-04 — statements 129–130: the velocity is linear in the data, and the whole propagated
  state depends continuously on it.
- 2026-08-04 — statements 127–128: an exponential bound on the velocity of the field solution, so
  the whole propagated state is controlled by its data.
- 2026-08-04 — statements 124–126: the regularity of the position datum propagates in time, so the
  evolution family iterates. The regular class is invariant under the evolution.
- 2026-08-04 — statements 122–123: the perturbed evolution is an evolution family; the restarted
  solution is identified by uniqueness after splitting the Duhamel integral.
- 2026-08-04 — statements 120–121: the half-order addition law, and the flow property of the free
  field evolution.
- 2026-08-04 — statements 117–119: the regularity hypothesis of statement 65 is **exactly** the
  domain of differentiability, by the sinc limit. The regular class is now fully described.
- 2026-08-04 — statements 114–116: `⟨D⟩⁻¹` is **not** surjective in positive dimension, so the
  strong theory's regularity restriction is genuine. The card's prose claim is now a theorem.
- 2026-08-04 — statements 112–113: the regular Cauchy data are **dense**, so the strong theory's
  hypothesis class is measured, not merely inhabited.
- 2026-08-04 — audit: every corpus identifier named on the eight clocks cards (1146 distinct)
  resolves to a declaration in `formal/`; the only unresolved names are mathlib's.
- 2026-08-04 — statements 110–111: the estimates restated in the prescribed data, and continuous
  dependence for the constructed strong solution. The arc is complete.
- 2026-08-04 — statements 107–109: well-posedness of the smoothed strong problem in one theorem,
  and its instantiation at a bounded measurable potential smoothed by `⟨D⟩⁻¹`.
- 2026-08-04 — statements 103–106: **mild becomes strong** for a smoothing perturbation. The
  perturbed strong theory now has a constructed solution; existence, estimate and uniqueness meet.
- 2026-08-04 — statements 99–102: the second differentiation of the Duhamel term, for a regular
  source. The endpoint contributions add to the source by the Pythagorean identity.
- 2026-08-04 — statements 97–98: the variation-of-constants formula for the velocity, and the `C¹`
  Cauchy problem solved with the prescribed data. The construction programme is closed.
- 2026-08-04 — statements 94–96: the Duhamel term differentiated. Endpoint contributions cancel by
  commutation; the survivors recombine by the cosine subtraction law into the classical integral.
- 2026-08-04 — statements 91–93: the product rule for a strongly differentiable operator family,
  the regularity of the Duhamel integrals, and their endpoint derivatives.
- 2026-08-04 — statements 89–90: the subtraction law for the half-order propagator, and the Duhamel
  term rewritten with the observation and source times separated.
- 2026-08-04 — statements 87–88: the velocity datum needs no regularity for the first derivative;
  linearity of the field solution in its data, and continuous dependence at the field level.
- 2026-08-04 — statements 83–86: the field-level Duhamel formula. Well-posedness for arbitrary `L²`
  data (no regularity), and the identification of the strong field with the mild one.
- 2026-08-04 — statements 79–82: two-sided estimate, continuous dependence, and the agreement of
  the mild and free constructions. The obstruction to strong existence with a rough potential is
  recorded as a mathematical fact, not a gap.
- 2026-08-04 — statements 74–78: the potential returns. Grönwall for the perturbed strong equation
  and two-sided uniqueness for a bounded measurable potential.
- 2026-08-04 — statements 70–73: uniqueness and well-posedness for the strong `L²` Cauchy problem.
  The whole energy method reduces to the self-adjointness of `⟨D⟩⁻¹`.
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
