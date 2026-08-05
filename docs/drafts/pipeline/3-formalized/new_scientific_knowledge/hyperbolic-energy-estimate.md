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
| 155 | the high-pass perturbation, and its exact operator norm | `kgHighPass`, **`kgHighPassOp`**, `norm_kgHighPassOp_le`, `le_norm_kgHighPassOp`, **`norm_kgHighPassOp`** | **built** |
| 156 | **a perturbation above frequency `R` is damped by `⟨R⟩⁻¹`** | **`norm_kgSinFreqOp_comp_kgHighPassOp`** | **built** |
| 157 | its field is uniformly close to the free field | **`norm_kgFieldMild_kgHighPassOp_sub_free_le`** | **built** |
| 158 | **the forward map is not bounded below** | **`exists_norm_eq_and_kgFieldMild_close`** | **built** |
| 159 | **the inverse problem is ill-posed** | **`exists_potentials_field_closer_than`**, `exists_norm_eq_and_kgFieldMildT_close` | **built** |
| 160 | a multiplier obeys every bound its symbol obeys | `norm_lpBoundedMulCLM_le_of_bound`, **`norm_fourierMulCLM_le_of_bound`** | **built** |
| 161 | **the half-order propagator is bounded by the elapsed time** | `norm_kgSinOverFreq_le_abs`, **`norm_kgSinFreqOp_le_abs`**, `norm_kgSinFreqOp_apply_le_abs` | **built** |
| 162 | **the perturbation contributes only at second order in time** | **`norm_kgFieldMild_sub_free_le_sq`**, **`norm_kgFieldMildT_sub_free_le_sq`** | **built** |
| 163 | `\|cos a − 1\| ≤ a²/2` and `\|sin a − a\| ≤ \|a\|³/6` | `abs_cos_sub_one_le`, **`abs_sin_sub_self_le`** | **built** |
| 164 | the low-pass projection | `kgLowPass`, **`kgLowPassOp`**, `norm_kgLowPassOp_le`, `norm_kgLowPassOp_apply_le` | **built** |
| 165 | **the propagators are Taylor-accurate below a fixed frequency** | **`norm_kgCosOp_lowPass_sub_le`**, **`norm_kgSinFreqOp_lowPass_sub_smul_le`** | **built** |
| 166 | a solution from rest at a low-frequency datum leaves it at second order | **`norm_kgFieldMild_sub_data_le`** | **built** |
| 167 | the Duhamel source integral is quadratic in the probing time | `intervalIntegral_ofReal_sub_smul`, **`norm_kgSource_sub_smul_le`** | **built** |
| 168 | **conditional stability: on low-pass perturbations the forward map is bounded below** | **`norm_sub_le_of_lowPass`** | **built** |
| 169 | an admissible probing time always exists | **`exists_probe_time`** | **built** |
| 170 | **conditional stability with an explicit constant** | **`norm_sub_le_of_lowPass_explicit`** | **built** |
| 171 | **band stability, both directions** | **`lowPass_band_stability`** | **built** |
| 172 | a solution in a moving background leaves a low-frequency datum at second order | **`norm_kgFieldMildT_sub_data_le`** | **built** |
| 173 | the source integral of a moving background is quadratic in the probing time | `continuous_kgPotentialDiffSource`, **`norm_kgSourceT_sub_smul_le`** | **built** |
| 174 | **conditional stability for a moving background** | **`norm_sub_zero_le_of_lowPassT`** | **built** |
| 175 | the optimum of `A/x² + Bx` | `exists_balance_probe`, **`balance_probe_eq`**, `inv_sq_add_linear_at_balance`, **`inv_sq_add_linear_le_of_balance`** | **built** |
| 176 | **the optimal reconstruction error, and the cube-root law** | **`norm_sub_zero_le_optimal`** | **built** |
| 177 | no probing time does better | **`kgProbe_bound_optimal`** | **built** |
| 178 | the source of the energy-space equation, and its norm | `kgEnergy_ext`, `kgSourceOp`, **`norm_kgSourceOp_le`** | **built** |
| 179 | **the state equation in the energy space, and its sharp bound** | `kgStateKernel`, `strongKernel_kgStateKernel`, `kgStateMild`, `kgStateMild_eq`, **`norm_kgStateMild_le`**, `eq_kgStateMild_of_duhamel` | **built** |
| 180 | the gradient and the velocity of the mild solution, in closed form | `kgFieldGrad`, `kgFieldVel`, `kgFieldVel_eq_deriv`, **`kgFreqInvOp_kgFieldGrad`** | **built** |
| 181 | the state of the mild solution solves the energy-space equation | `kgFieldState`, **`kgFieldState_duhamel`**, **`kgFieldState_eq_kgStateMild`** | **built** |
| 182 | **the hyperbolic energy estimate, sharp, for an arbitrary bounded perturbation** | **`kgFieldEnergy_le`** | **built** |
| 183 | **the free field conserves the energy exactly**, so the constant one is sharp | `kgFieldGrad_zero_op`, `kgFieldVel_zero_op`, **`kgFieldEnergy_zero_op`** | **built** |
| 184 | the energy-space equation with a moving background | `kgStateKernelT`, **`strongKernel_kgStateKernelT`**, `kgStateMildT`, `kgStateMildT_eq`, **`norm_kgStateMildT_le`**, `eq_kgStateMildT_of_duhamel` | **built** |
| 185 | the gradient and velocity in a moving background | `kgFieldGradT`, `kgFieldVelT`, `kgFieldVelT_eq_deriv`, **`kgFreqInvOp_kgFieldGradT`**, `kgFieldStateT`, **`kgFieldStateT_eq_kgStateMildT`** | **built** |
| 186 | **the hyperbolic energy estimate in a moving background** | **`kgFieldEnergyT_le`** | **built** |
| 187 | the energy space is a Hilbert space; the propagator is **unitary** | `inner_kgEnergy`, `kgPropagatorIsom`, **`inner_kgPropagator`**, `hasDerivAt_norm_sq_energy` | **built** |
| 188 | **the reduced state is an ordinary integral, and differentiable** | `kgReducedState`, `kgFieldState_zero`, **`kgReducedState_eq`**, **`hasDerivAt_kgReducedState`** | **built** |
| 189 | **the total energy of a self-adjoint perturbation is exactly conserved** | `kgTotalEnergy`, **`hasDerivAt_kgTotalEnergy`**, **`kgTotalEnergy_const`**, **`kgFieldEnergy_conserved`** | **built** |
| 190 | the potential term is controlled by the energy (the mass gap in operator form) | `abs_re_inner_potential_le`, **`norm_kgFieldMild_sq_le_energy`** | **built** |
| 191 | **a small real potential gives an energy bounded uniformly in time** | **`kgFieldEnergy_uniform`** | **built** |
| 192 | **a confining real potential needs no smallness at all** | **`kgFieldEnergy_le_of_nonpos`**, `norm_kgFieldMild_le_of_nonpos` | **built** |
| 193 | **multiplication by a bounded real potential is self-adjoint** | `kgMulOp`, `norm_kgMulOp_le`, **`inner_kgMulOp`** | **built** |
| 194 | conservation and the uniform bound, for a real potential | **`kgRealPotential_energy_conserved`**, **`kgRealPotential_energy_uniform`** | **built** |
| 195 | the potential term is `∫V\|u\|²` | **`re_inner_kgMulOp`** | **built** |
| 196 | **an attractive potential keeps the field bounded for all time** | **`kgRealPotential_energy_le_of_nonpos`**, **`kgRealPotential_norm_le_of_nonpos`** | **built** |
| 197 | the reduced state of a moving background | `kgReducedStateT`, `kgFieldStateT_zero`, **`kgReducedStateT_eq`**, **`hasDerivAt_kgReducedStateT`** | **built** |
| 198 | **the differentiated energy identity for a moving background** | **`hasDerivAt_normSq_kgFieldStateT`** | **built** |
| 199 | **the work–energy identity**: the energy changes at the rate the background does | `kgAdiabaticEnergy`, **`hasDerivAt_kgAdiabaticEnergy`** | **built** |
| 200 | the energy dominates the state, and its derivative | `kgAdiabaticEnergy_lower`, `kgAdiabaticEnergy_nonneg`, **`abs_deriv_kgAdiabaticEnergy_le`** | **built** |
| 201 | **the adiabatic estimate** | **`kgAdiabaticEnergy_le`**, **`kgFieldEnergyT_le_adiabatic`** | **built** |
| 202 | **the exact work integral** | `continuous_kgWorkDensity`, **`kgAdiabaticEnergy_sub`**, **`abs_kgAdiabaticEnergy_sub_le`** | **built** |
| 203 | a background switched on by a scalar profile | `kgScaledPotential`, `norm_kgScaledPotential`, **`inner_kgScaledPotential`**, **`hasDerivAt_kgScaledPotential`** | **built** |
| 204 | **the adiabatic estimate for a switched background** | **`kgScaledPotential_energy_le`** | **built** |
| 205 | the potential term of a switched background | **`re_inner_kgScaledPotential`** | **built** |
| 206 | **a real potential of varying strength**, as a moving background | `kgSwitchedPotential`, `norm_kgSwitchedPotential_le`, **`inner_kgSwitchedPotential`**, **`hasDerivAt_kgSwitchedPotential`** | **built** |
| 207 | its work density is the switching rate times `∫V\|u\|²` | **`re_inner_kgSwitchedPotential`** | **built** |
| 208 | **the adiabatic estimate and the exact work accounting, fully concrete** | **`kgSwitchedPotential_energy_le`**, **`kgSwitchedPotential_work`** | **built** |
| 209 | **the low-pass projection is an idempotent self-adjoint projection** | **`kgLowPassOp_comp_self`**, `kgLowPassOp_idem`, **`inner_kgLowPassOp`** | **built** |
| 210 | the band compression of a perturbation | `kgBandOp`, `norm_kgBandOp_le`, **`inner_kgBandOp`**, `kgBandOp_sub`, **`kgBandOp_lowPass_dom`**, **`kgBandOp_lowPass_ran`** | **built** |
| 211 | **conditional stability for band-limited perturbations** | **`norm_kgBandOp_sub_le`** | **built** |
| 212 | **the band compression of a real potential conserves the energy exactly** | **`kgBandOp_real_energy_conserved`** | **built** |
| 213 | each frequency is eventually below the cut-off | `norm_one_le_one`, **`tendsto_kgLowPass`** | **built** |
| 214 | **the low-pass projections converge strongly to the identity** | **`tendsto_kgLowPassOp_apply`** | **built** |
| 215 | **the band compressions converge strongly to the perturbation** | **`tendsto_kgBandOp_apply`** | **built** |
| 216 | **a perturbation is determined by its band compressions** | **`eq_of_kgBandOp_eq`** | **built** |
| 217 | the projection commutes with the propagators | **`kgCosOp_kgLowPassOp`**, **`kgSinFreqOp_kgLowPassOp`**, `kgLowPassOp_kgFieldFree` | **built** |
| 218 | **the projection passes through the perturbed evolution** | **`kgLowPassOp_kgFieldMild`** | **built** |
| 219 | **the band is invariant under the evolution** | **`kgFieldMild_lowPass_invariant`**, `kgBandOp_dom`, `kgBandOp_ran`, **`kgBandOp_lowPass_invariant`** | **built** |
| 220 | **on a band the frequency obstruction disappears** | `kgFreqSqLow`, **`kgFreqSqLowOp`**, `norm_kgFreqSqLowOp_le`, **`kgFreqInvOp_sq_kgFreqSqLowOp`** | **built** |
| 221 | **`⟨D⟩` restricted to a band**, as a bounded operator | `kgFreqLow`, **`kgFreqLowOp`**, `norm_kgFreqLowOp_le` | **built** |
| 222 | **every band-limited vector carries one power of `⟨D⟩⁻¹`** | **`kgFreqInvOp_kgFreqLowOp`**, `kgLowPassOp_kgFreqLowOp`, `kgFreqLowOp_kgLowPassOp`, `kgFreqLowOp_kgFreqLowOp` | **built** |
| 223 | **on a band the sine propagator is the half-order one composed with the frequency** | **`kgSinOp_kgLowPassOp`** | **built** |
| 224 | the band-restricted frequency commutes with the propagators | **`kgCosOp_kgFreqLowOp`**, **`kgFreqSqLowOp_kgCosOp`**, **`kgFreqSqLowOp_kgSinFreqOp`** | **built** |
| 225 | the band-restricted `⟨D⟩²` of the solution, in closed form | **`kgFreqSqLowOp_kgFieldMild`** | **built** |
| 226 | **the mild solution on a band is a strong solution, with no smoothing hypothesis** | **`hasDerivAt_kgFieldVel_band`** | **built** |
| 227 | **the band solution is a strong solution in the corpus's own sense** | **`solvesKGSource_band`** | **built** |
| 228 | uniqueness of the strong solution on a band | **`eq_of_solvesKGSource_band`** | **built** |
| 229 | **the strong Cauchy problem on a band is well posed** | **`exists_unique_solvesKGSource_band`** | **built** |
| 230 | the band-restricted frequency turns the half-order propagator into the sine one | **`kgFreqLowOp_kgSinFreqOp`** | **built** |
| 231 | **on a band the abstract gradient is `⟨D⟩_R u`** | **`kgFieldGrad_band`** | **built** |
| 232 | **the classical conserved energy of the band solution** | **`kgBandReal_energy_conserved`** | **built** |
| 233 | the difference of two solutions with different perturbations *and* different data | **`kgFieldMild_sub_general`** | **built** |
| 234 | **the difference measured by the action of the perturbations, not their norms** | **`norm_kgFieldMild_sub_general_le`** | **built** |
| 235 | the accumulated discrepancy of the band compressions vanishes | **`tendsto_integral_kgBandOp_sub`** | **built** |
| 236 | **the band solutions converge to the true solution** | `tendsto_kgFieldMild_band_of_nonneg`, **`tendsto_kgFieldMild_band`** | **built** |
| 237 | the band projection commutes with the inverse frequency | **`kgLowPassOp_kgFreqInvOp`** | **built** |
| 238 | the perturbed sources converge, `W_R u_R(s) → W u(s)` | **`tendsto_kgBandOp_source`** | **built** |
| 239 | the Duhamel terms of the velocity converge | **`tendsto_integral_kgCos_band`** | **built** |
| 240 | **the whole state converges, velocity as well as field** | **`tendsto_kgFieldVel_band`** | **built** |
| 241 | the Duhamel terms of the gradient converge | **`tendsto_integral_kgSin_band`** | **built** |
| 242 | the gradient `⟨D⟩u_R(t)` converges | **`tendsto_kgFieldGrad_band`** | **built** |
| 243 | the state converges in the energy space | **`tendsto_kgFieldState_band`** | **built** |
| 244 | **the energy of the band solution converges** | **`tendsto_kgFieldEnergy_band`** | **built** |
| 245 | one cut-off bounds the whole observation window | **`norm_kgFieldMild_band_sub_le_endpoint`** | **built** |
| 246 | **the band approximation is uniform on `[0,T]`** | **`tendstoUniformlyOn_kgFieldMild_band`** | **built** |
| 247 | the band compression of a moving background, and its strong limit | `kgBandOpT`, `norm_kgBandOpT_le`, `continuous_kgBandOpT_apply`, **`tendsto_kgBandOpT_apply`** | **built** |
| 248 | the difference of two solutions in different moving backgrounds | **`kgFieldMildT_sub_general`** | **built** |
| 249 | **the sharp difference estimate for moving backgrounds** | **`norm_kgFieldMildT_sub_general_le`** | **built** |
| 250 | the accumulated discrepancy of the moving compressions vanishes | **`tendsto_integral_kgBandOpT_sub`** | **built** |
| 251 | one cut-off bounds the whole window, moving case | **`norm_kgFieldMildT_band_sub_le_endpoint`** | **built** |
| 252 | **the band solutions converge in a moving background** | `tendsto_kgFieldMildT_band_of_nonneg`, **`tendsto_kgFieldMildT_band`** | **built** |
| 253 | **uniform on `[0,T]` in a moving background** | **`tendstoUniformlyOn_kgFieldMildT_band`** | **built** |
| 254 | the perturbed sources converge, moving case | **`tendsto_kgBandOpT_source`** | **built** |
| 255 | the Duhamel terms converge, moving case | **`tendsto_integral_kgCosT_band`**, **`tendsto_integral_kgSinT_band`** | **built** |
| 256 | the velocity converges, moving case | **`tendsto_kgFieldVelT_band`** | **built** |
| 257 | the gradient converges, moving case | **`tendsto_kgFieldGradT_band`** | **built** |
| 258 | **the state and the energy converge in a moving background** | **`tendsto_kgFieldStateT_band`**, **`tendsto_kgFieldEnergyT_band`** | **built** |
| 259 | the source difference is the field difference | `norm_kgPair_zero_left`, `kgSourceOp_sub_apply`, **`norm_kgSourceOp_sub_apply`** | **built** |
| 260 | the difference of two states, split along the second one | **`kgStateMild_sub_general`** | **built** |
| 261 | **the sharp difference estimate in the energy space** | **`norm_kgStateMild_sub_general_le`** | **built** |
| 262 | **the sharp difference estimate for the state of the field** | **`norm_kgFieldState_sub_general_le`** | **built** |
| 263 | one cut-off bounds the state over the whole window | **`norm_kgFieldState_band_sub_le_endpoint`** | **built** |
| 264 | **the state converges uniformly on `[0,T]`** | **`tendstoUniformlyOn_kgFieldState_band`** | **built** |
| 265 | gradient and velocity converge uniformly on `[0,T]` | **`tendstoUniformlyOn_kgFieldGrad_band`**, **`tendstoUniformlyOn_kgFieldVel_band`** | **built** |
| 266 | **the energy converges uniformly on `[0,T]`** | `kgFieldEnergy_eq_norm_sq`, `norm_kgFieldState_band_le`, `norm_kgFieldState_le_window`, **`tendstoUniformlyOn_kgFieldEnergy_band`** | **built** |
| 267 | the difference of two states in different moving backgrounds | `continuous_kgSourceOpT_apply`, **`kgStateMildT_sub_general`** | **built** |
| 268 | **the state estimate in a moving background** | **`norm_kgStateMildT_sub_general_le`** | **built** |
| 269 | **the state estimate for the field in a moving background** | **`norm_kgFieldStateT_sub_general_le`** | **built** |
| 270 | one cut-off bounds the moving state over the window | **`norm_kgFieldStateT_band_sub_le_endpoint`** | **built** |
| 271 | **the moving state converges uniformly on `[0,T]`** | **`tendstoUniformlyOn_kgFieldStateT_band`** | **built** |
| 272 | moving gradient and velocity converge uniformly | **`tendstoUniformlyOn_kgFieldGradT_band`**, **`tendstoUniformlyOn_kgFieldVelT_band`** | **built** |
| 273 | **the moving energy converges uniformly on `[0,T]`** | `kgFieldEnergyT_eq_norm_sq`, `norm_kgFieldStateT_band_le`, `norm_kgFieldStateT_le_window`, **`tendstoUniformlyOn_kgFieldEnergyT_band`** | **built** |
| 274 | strong solutions in a moving background, and their energy identity | `SolvesKGSourceT`, `solvesKGSourceT_const`, **`hasDerivAt_kgStrongEnergy_sourceT`** | **built** |
| 275 | the strong energy grows at most exponentially, moving case | **`kgStrongEnergy_le_expT`** | **built** |
| 276 | time reversal and vanishing data, moving case | `SolvesKGSourceT.comp_neg`, **`eq_zero_of_solvesKGSourceT`** | **built** |
| 277 | **uniqueness for the strong Cauchy problem in a moving background** | **`eq_of_solvesKGSourceT`** | **built** |
| 278 | the band is invariant under a moving evolution | `kgLowPassOp_kgFieldMildT`, `kgFieldMildT_lowPass_invariant`, **`kgBandOpT_lowPass_invariant`** | **built** |
| 279 | the band-restricted `⟨D⟩²` of the moving solution | **`kgFreqSqLowOp_kgFieldMildT`** | **built** |
| 280 | **the moving band solution is a strong solution** | **`hasDerivAt_kgFieldVelT_band`** | **built** |
| 281 | **the strong Cauchy problem on a band is well posed in a moving background** | `solvesKGSourceT_band`, `eq_of_solvesKGSourceT_band`, **`exists_unique_solvesKGSourceT_band`** | **built** |
| 282 | compression is linear: compressing a switched background is switching the compression | `kgBandOp_smul`, **`kgBandOpT_kgScaledPotential`** | **built** |
| 283 | **on a band the moving gradient is `⟨D⟩_R u`** | **`kgFieldGradT_band`** | **built** |
| 284 | a real potential of varying strength, compressed to a band | `kgBandSwitchedPotential`, `kgBandSwitchedPotential_eq`, `norm_kgBandSwitchedPotential_le`, **`inner_kgBandSwitchedPotential`**, **`hasDerivAt_kgBandSwitchedPotential`** | **built** |
| 285 | its potential term and work density are honest integrals | **`re_inner_kgBandOp_kgMulOp`**, **`re_inner_kgBandSwitchedPotential`** | **built** |
| 286 | **the adiabatic energy on a band, every term a quantity of the field** | **`kgBandSwitched_energy_eq`** | **built** |
| 287 | **the classical work–energy balance on a band** | **`kgBandSwitched_work`** | **built** |
| 288 | **the adiabatic estimate on a band** | **`kgBandSwitched_energy_le`** | **built** |
| 289 | the compressions act correctly along any convergent curve of states | **`tendsto_kgBandOpT_apply_of_tendsto`** | **built** |
| 290 | the potential term converges | **`tendsto_re_inner_kgBandOpT_source`** | **built** |
| 291 | **the adiabatic energy of the band solution converges** | **`tendsto_kgAdiabaticEnergy_band`** | **built** |
| 292 | **the accumulated work of the band solution converges** | **`tendsto_integral_work_band`** | **built** |
| 293 | **the band-restricted frequency undoes the inverse frequency** | **`kgFreqLowOp_kgFreqInvOp`** | **built** |
| 294 | the field restart, with the state at the restarting time in closed form | **`kgFieldMildT_restart`** | **built** |
| 295 | the velocity and the gradient restart | **`kgFieldVelT_restart`**, **`kgFieldGradT_restart`** | **built** |
| 296 | **the evolution is an evolution family on the energy space** | **`kgFieldStateT_restart`** | **built** |
| 297 | the period map of a periodically driven field | `kgPeriodMap`, `kgPeriodMap_apply`, **`norm_kgPeriodMap_le`**, `periodic_shift_nat` | **built** |
| 298 | **the evolution over one period does not depend on which period** | **`kgFieldStateT_period`** | **built** |
| 299 | **the state after `n` periods is the `n`-th iterate of the period map** | **`kgFieldStateT_iterate`** | **built** |
| 300 | **the Floquet form of the energy estimate** | **`norm_kgFieldStateT_period_le`** | **built** |
| 301 | the energy space componentwise; free term and kernel are linear | `kgEnergy_fst_add`, `kgEnergy_snd_add`, `kgEnergy_fst_smul`, `kgEnergy_snd_smul`, **`kgStateFree_linear`**, **`kgStateKernelT_linear`** | **built** |
| 302 | **the state is linear in the Cauchy datum** | **`kgStateMildT_linear`** | **built** |
| 303 | **the monodromy operator**, of norm at most `e^{b\|T\|}` | `kgPeriodLM`, **`kgMonodromy`**, `kgMonodromy_apply`, **`norm_kgMonodromy_le`** | **built** |
| 304 | **the state after `n` periods is `Mⁿ` applied to the datum** | `kgMonodromy_pow_apply`, **`kgFieldStateT_monodromy_pow`** | **built** |
| 305 | **stability from the monodromy alone** | **`norm_kgFieldStateT_le_of_pow_bound`** | **built** |
| 306 | running one period backwards undoes it | `periodic_neg`, **`kgPeriodMap_left_inverse`**, **`kgPeriodMap_right_inverse`** | **built** |
| 307 | **the monodromy is a linear homeomorphism of the energy space** | **`kgMonodromyEquiv`**, `kgMonodromyEquiv_apply`, `kgMonodromyEquiv_symm_apply`, **`norm_kgMonodromy_neg_le`** | **built** |
| 308 | **bounded powers give stability at every time** | **`norm_kgFieldStateT_le_of_pow_bound_all`** | **built** |
| 309 | bounded orbits give bounded powers | **`exists_pow_bound_of_orbits_bounded`** | **built** |
| 310 | **the stability criterion for a periodically driven clock** | **`kgFloquet_stable_iff`** | **built** |
| 311 | the state is contracted by the monodromy norm each period | **`norm_kgFieldStateT_period_le_pow`** | **built** |
| 312 | the leftover piece of time costs one period | **`norm_kgFieldStateT_le_floor`** | **built** |
| 313 | **a contraction over one period keeps the clock running** | **`norm_kgFieldStateT_le_of_norm_monodromy_le_one`** | **built** |
| 314 | a strict contraction damps the clock out along the periods | **`tendsto_kgFieldStateT_period_zero`** | **built** |
| 315 | **a strict contraction damps the clock out at every time** | **`tendsto_kgFieldStateT_zero`** | **built** |
| 316 | a constant background is periodic with every period | `periodic_const`, `kgFieldGradT_const`, `kgFieldVelT_const`, **`kgFieldStateT_const`**, `norm_kgPair_sq` | **built** |
| 317 | **the free monodromy is an isometry** | **`norm_kgMonodromy_zero_apply`**, **`norm_kgMonodromy_zero_le_one`** | **built** |
| 318 | a small real potential gives a uniformly bounded state, in energy-space form | **`norm_kgFieldState_le_uniform`** | **built** |
| 319 | **the stable class is inhabited, with an explicit constant** | **`norm_kgMonodromy_pow_le_of_small`**, `norm_kgFieldState_le_of_small` | **built** |
| 320 | the band model of a periodic background has its own monodromy | **`periodic_kgBandOpT`**, `kgBandMonodromy`, `kgBandMonodromy_apply`, **`norm_kgBandMonodromy_le`** | **built** |
| 321 | the band state differs from the true one by the accumulated discrepancy | **`norm_kgFieldStateT_band_sub_le_same`** | **built** |
| 322 | **the band monodromies converge strongly to the monodromy** | **`tendsto_kgBandMonodromy`** | **built** |
| 323 | **every power converges strongly** | **`tendsto_kgBandMonodromy_pow`** | **built** |
| 324 | **stability transfers from the band models** | **`norm_kgMonodromy_pow_le_of_band_bound`** | **built** |
| 325 | **the Floquet multipliers lie in the disc `\|k\| ≤ e^{b\|T\|}`** | `norm_one_kgEnergy_le`, **`norm_le_of_mem_spectrum_kgMonodromy`** | **built** |
| 326 | **a power bound confines the multipliers to the closed unit disc** | **`norm_le_one_of_mem_spectrum_of_pow_bound`** | **built** |
| 327 | a multiplier outside the unit disc forbids any power bound | **`not_pow_bounded_of_one_lt_norm_spectrum`** | **built** |
| 328 | **the Floquet instability criterion** | **`exists_unbounded_of_one_lt_norm_spectrum`** | **built** |
| 329 | **powers of an element of spectral radius `< 1` vanish in norm** (missing from mathlib) | **`tendsto_norm_pow_zero_of_spectralRadius_lt_one`** | **built** |
| 330 | a spectral radius below one damps the clock along the periods | **`tendsto_kgFieldStateT_period_zero_of_spectralRadius`** | **built** |
| 331 | **the sharp Floquet decay criterion** | **`tendsto_kgFieldStateT_zero_of_spectralRadius`** | **built** |
| 332 | the radius and its multipliers | **`spectralRadius_le_one_of_forall`**, **`exists_mem_spectrum_one_lt_norm`** | **built** |
| 333 | **a stable clock has spectral radius at most one** | **`spectralRadius_le_one_of_pow_bound`** | **built** |
| 334 | **a spectral radius greater than one breaks the clock** | **`exists_unbounded_of_one_lt_spectralRadius`** | **built** |
| 335 | **the Floquet trichotomy** | **`kgFloquet_trichotomy`** | **built** |
| 336 | each component of a datum is bounded by its energy norm | **`norm_fst_le_norm_kgPair`**, **`norm_snd_le_norm_kgPair`** | **built** |
| 337 | a uniform distance between backgrounds bounds the distance of their states | **`norm_kgFieldStateT_sub_le_of_uniform`** | **built** |
| 338 | **the monodromy is Lipschitz in the background** | **`norm_kgMonodromy_sub_le`** | **built** |
| 339 | **the decaying regime is open** | **`tendsto_kgFieldStateT_zero_of_perturbed`** | **built** |
| 340 | **the `L²` space, the energy space and the operator algebra are nontrivial** | **`kgLp_nontrivial`**, **`kgEnergy_nontrivial`**, **`norm_one_kgEnergy`** | **built** |
| 341 | **every monodromy has at least one Floquet multiplier** | **`spectrum_kgMonodromy_nonempty`** | **built** |
| 342 | the spectral radius is attained by a multiplier | **`exists_multiplier_eq_spectralRadius`** | **built** |
| 343 | every power of the free monodromy is an isometry of norm one | **`norm_kgMonodromy_zero_pow_apply`**, **`norm_kgMonodromy_zero_pow`** | **built** |
| 344 | **the free clock sits exactly on the boundary of the trichotomy** | **`spectralRadius_kgMonodromy_zero`** | **built** |
| 345 | **the free monodromy is a unit**, with inverse the monodromy over `-T` | **`kgMonodromy_zero_isUnit`** | **built** |
| 346 | no free multiplier lies inside the unit disc | **`one_le_norm_of_mem_spectrum_kgMonodromy_zero`** | **built** |
| 347 | **the free Floquet multipliers lie on the unit circle** | **`norm_eq_one_of_mem_spectrum_kgMonodromy_zero`** | **built** |
| 348 | a power bound confines the spectrum to the closed unit disc (general algebra) | **`norm_le_one_of_mem_spectrum_of_pow_bound'`** | **built** |
| 349 | **two-sided power boundedness puts the spectrum on the unit circle** | **`norm_eq_one_of_mem_spectrum_of_inverse`** | **built** |
| 350 | the monodromies of a constant background over opposite periods are inverse | **`kgMonodromy_const_mul_inv`** | **built** |
| 351 | **a clock in a weak static potential is purely oscillatory** | **`norm_eq_one_of_mem_spectrum_of_small_potential`** | **built** |
| 352 | the velocity flip: an isometric involution of the energy space | `kgFlip`, `kgFlip_apply`, **`norm_kgFlip_apply`**, **`kgFlip_kgFlip`** | **built** |
| 353 | the gradient is unchanged by time reflection | **`kgFieldGradT_neg`** | **built** |
| 354 | the velocity changes sign under time reflection | **`kgFieldVelT_neg`** | **built** |
| 355 | **the state reflects through the velocity flip** | **`kgFieldStateT_neg`**, **`norm_kgFieldStateT_neg`** | **built** |
| 356 | **the backward monodromy is the flip conjugate of the reflected forward one** | **`kgMonodromy_neg_apply`**, **`kgMonodromy_neg_pow_apply`** | **built** |
| 357 | the backward powers are no larger than the reflected forward ones | **`norm_kgMonodromy_neg_pow_le`** | **built** |
| 358 | **the backward transfer from the band models** | **`norm_kgMonodromy_neg_pow_le_of_band_bound`** | **built** |
| 359 | **oscillation can be decided on the band models** | **`norm_eq_one_of_mem_spectrum_of_band_bounds`** | **built** |
| 360 | the velocity flip is a unit of the operator algebra | **`kgFlip_mul_self`**, `kgFlipUnit`, `kgFlipUnit_val`, `kgFlipUnit_inv_val` | **built** |
| 361 | the backward monodromy is a flip conjugate, as operators | **`kgMonodromy_neg_eq_conj`** | **built** |
| 362 | conjugating by the flip does not move the spectrum | **`spectrum_kgMonodromy_neg_eq`** | **built** |
| 363 | **time reversal inverts the Floquet multipliers** | **`spectrum_kgMonodromy_reflected`** | **built** |
| 364 | the reflected multipliers are the reciprocals | **`mem_spectrum_reflected_iff`** | **built** |
| 365 | the reflection of a periodic background is periodic | **`periodic_neg_background`** | **built** |
| 366 | **a clock that keeps time in both directions is purely oscillatory** | **`norm_eq_one_of_mem_spectrum_of_two_way_stable`** | **built** |
| 367 | **a two-way stable clock has spectral radius exactly one** | **`spectralRadius_eq_one_of_two_way_stable`** | **built** |
| 368 | **conditional stability at every instant** | **`norm_sub_le_of_lowPassT_everywhere`** | **built** |
| 369 | **the cube-root law at every instant** | **`norm_sub_le_optimal_everywhere`** | **built** |
| 370 | for every tolerance there is an admissible probe whose drift term is below it | **`exists_small_probe_time`** | **built** |
| 371 | **exact observations determine a band-limited moving background exactly** | **`eq_of_exact_observation_everywhere`** | **built** |
| 372 | a periodic background is periodic under every integer multiple of its period | **`periodic_shift_int`** | **built** |
| 373 | restarting at an instant is restarting at its representative in the first period | `periodRep_nonneg`, `periodRep_lt`, **`shift_eq_periodRep`** | **built** |
| 374 | **one period of experiments determines a periodic band-limited background** | **`eq_of_exact_observation_period`** | **built** |
| 375 | compression contracts the difference of differences | **`norm_kgBandOp_sub_sub_le`** | **built** |
| 376 | **the reconstruction theorem on the band models** | **`eq_of_exact_observation_band`** | **built** |
| 377 | one period of experiments determines the band model of a periodic background | **`eq_of_exact_observation_band_period`** | **built** |
| 378 | **observing every band model determines the background exactly** | **`eq_of_exact_observation_all_bands`** | **built** |
| 379 | **a periodic background is determined by one period of experiments at every cut-off** | **`eq_of_exact_observation_all_bands_period`** | **built** |
| 380 | **a symbol whose multiplication operator vanishes vanishes a.e.** (missing from the corpus) | **`ae_eq_zero_of_lpBoundedMulCLM_eq_zero`** | **built** |
| 381 | **a bounded real potential is determined by its multiplication operator** | **`kgMulOp_injective`** | **built** |
| 382 | **a static real potential is determined a.e. by short-time clock observations** | **`potential_ae_eq_of_exact_observation`** | **built** |
| 383 | the four-term combination of multiplication operators is one multiplication operator | **`norm_kgMulOp_sub_sub_le`** | **built** |
| 384 | **a moving real potential is determined a.e. at every instant** | **`potentialT_ae_eq_of_exact_observation`** | **built** |
| 385 | the operator family of a periodic potential is periodic | **`kgMulOp_periodic`** | **built** |
| 386 | **a periodic real potential is read off one period of experiments** | **`potentialT_ae_eq_of_exact_observation_period`** | **built** |
| 387 | the monodromy depends on the background and nothing else | **`kgMonodromy_congr`** | **built** |
| 388 | **observationally identical clocks have the same Floquet spectrum** | **`spectrum_kgMonodromy_eq_of_exact_observation`** | **built** |
| 389 | **the trichotomy verdict is the same for them** | **`spectralRadius_kgMonodromy_eq_of_exact_observation`** | **built** |
| 390 | **one period of observations decides the fate of a periodic clock** | **`spectralRadius_kgMonodromy_eq_of_exact_observation_period`** | **built** |
| 391 | no Floquet multiplier is smaller than the estimate allows | **`exp_neg_le_norm_of_mem_spectrum_kgMonodromy`** | **built** |
| 392 | **every Floquet multiplier lies in the annulus `e^{−b\|T\|} ≤ \|k\| ≤ e^{b\|T\|}`** | **`mem_annulus_of_mem_spectrum_kgMonodromy`** | **built** |
| 393 | a spectral radius below one is witnessed by a multiplier inside the disc | **`exists_multiplier_lt_one_of_spectralRadius_lt_one`** | **built** |
| 394 | **decay costs a potential**: `b·\|T\| > 0` | **`zero_lt_of_spectralRadius_lt_one`** | **built** |
| 395 | **instability costs a potential**: `b·\|T\| > 0` | **`zero_lt_of_one_lt_norm_spectrum`** | **built** |
| 396 | the logarithm of a multiplier is bounded by `b·\|T\|` | **`abs_log_norm_le_of_mem_spectrum_kgMonodromy`** | **built** |
| 397 | **the Floquet exponent is bounded by the strength of the background** | **`abs_floquetExponent_le`** | **built** |
| 398 | **a time-symmetric background has an inversion-invariant spectrum** | **`spectrum_kgMonodromy_inv_eq`** | **built** |
| 399 | its multipliers come in reciprocal pairs | **`mem_spectrum_kgMonodromy_inv_iff`** | **built** |
| 400 | **a stable time-symmetric clock has all multipliers on the unit circle** | **`norm_eq_one_of_mem_spectrum_of_time_symmetric`** | **built** |
| 401 | for a time-symmetric background, forward stability is backward stability | **`stable_neg_of_time_symmetric`** | **built** |
| 402 | **a time-symmetric periodic clock stable forwards has spectral radius one** | **`spectralRadius_eq_one_of_time_symmetric_stable`** | **built** |
| 403 | **a stable clock in a static potential can only oscillate** | `timeSymmetric_const`, **`spectralRadius_eq_one_of_static_stable`** | **built** |
| 404 | a spectral value is dominated by the spectral radius | `enorm_eq_ofReal_norm`, **`norm_le_spectralRadius`** | **built** |
| 405 | a uniform bound on the values bounds the radius | **`spectralRadius_le_ofReal_of_forall`** | **built** |
| 406 | **the spectral radius lies in the annulus too** | **`spectralRadius_kgMonodromy_mem_annulus`** | **built** |
| 407 | **the powers are eventually below any rate exceeding the spectral radius** (missing from mathlib) | **`eventually_norm_pow_le_of_spectralRadius`** | **built** |
| 408 | the spectral radius of a monodromy is finite | **`spectralRadius_kgMonodromy_ne_top`** | **built** |
| 409 | **after enough periods a clock grows no faster than its spectral radius** | **`eventually_norm_kgFieldStateT_le_of_spectralRadius`** | **built** |
| 410 | every spectral value grows no faster than the powers | **`norm_pow_le_norm_pow_of_mem_spectrum`** | **built** |
| 411 | the powers of a monodromy grow at least like its spectral radius | **`spectralRadius_pow_le_norm_pow_kgMonodromy`** | **built** |
| 412 | **the growth of a clock is exactly its spectral radius** | **`norm_pow_kgMonodromy_sandwich`** | **built** |
| 413 | **the discrete rate governs continuous time**, at the cost of one period | **`eventually_norm_kgFieldStateT_le_floor_rate`** | **built** |
| 414 | **an exponential bound at the true rate** | **`eventually_norm_kgFieldStateT_le_exp_rate`** | **built** |
| 415 | a sequence dominated by a geometric one has base at most the geometric base | **`norm_le_of_pow_geometric`** | **built** |
| 416 | a geometric bound on the band powers passes to the true monodromy | **`norm_pow_le_of_band_rate`** | **built** |
| 417 | **the growth rate transfers from the band models** | **`spectralRadius_le_of_band_rate`** | **built** |
| 418 | the energy after `n` periods is bounded by the square of the operator norm | **`kgFieldEnergyT_pow_le`** | **built** |
| 419 | **the energy grows at twice the Floquet exponent** | **`eventually_kgFieldEnergyT_le_rate`** | **built** |
| 420 | **a band model decaying geometrically makes the true clock decay** | **`tendsto_kgFieldStateT_zero_of_band_rate`** | **built** |
| 421 | **the energy obeys the card's estimate at the true rate** | `exp_mul_self`, **`eventually_kgFieldEnergyT_le_exp_rate`** | **built** |
| 422 | flipping the velocity does not change the energy norm | **`norm_kgPair_neg_snd`** | **built** |
| 423 | **the backward rate is the reflected background's forward rate** | **`eventually_norm_kgFieldStateT_neg_le_exp_rate`** | **built** |
| 424 | **the two-sided estimate at the true rate**, for a background even in time | **`exists_bound_norm_kgFieldStateT_abs`** | **built** |
| 425 | **the card's inequality at the sharp rate, in both directions of time** | **`exists_bound_kgFieldEnergyT_abs`** | **built** |
| 426 | a right inverse telescopes through powers | **`pow_mul_pow_eq_one`** | **built** |
| 427 | **a clock in a weak static real potential has spectral radius exactly one** | **`spectralRadius_eq_one_of_small_potential`** | **built** |
| 428 | its state is bounded below as well as above | **`norm_kgFieldStateT_ge_of_small_potential`** | **built** |
| 429 | **its energy is trapped in a band, for all time** | **`kgFieldEnergy_trapped_of_small_potential`** | **built** |
| 430 | **the trap holds at every instant, not only at multiples of a period** | **`kgFieldEnergy_trapped_all_time`** | **built** |
| 431 | the powers of an operator act on an eigenvector by the powers of its eigenvalue | `pow_apply_of_smul` | **built** |
| 432 | the state is homogeneous in the Cauchy datum | `kgFieldStateT_smul` | **built** |
| 433 | **the shift law**: one period advances the solution by restarting it | `kgFieldStateT_shift` | **built** |
| 434 | **an eigen-solution multiplies by its multiplier over every period, at every instant** | **`kgFieldStateT_eigen_shift`** | **built** |
| 435 | its stroboscopic state is exactly `kⁿ` times the datum | `kgFieldStateT_eigen_pow` | **built** |
| 436 | **its growth is exactly geometric**: `‖v(nT)‖ = |k|ⁿ‖v(0)‖`, no `ε`, no one-period constant | **`norm_kgFieldStateT_eigen`** | **built** |
| 437 | its energy is exactly geometric: `E(nT) = |k|^{2n}E(0)` | `kgFieldEnergyT_eigen` | **built** |
| 438 | **the Floquet normal form**: `v(t) = e^{μt}p(t)` with `p` of period `T` | **`exists_floquet_normal_form`** | **built** |
| 439 | a nonnegative real whose powers stay in `[1/c, c]` is one | `eq_one_of_pow_mem_Icc` | **built** |
| 440 | **an attained multiplier of a weak static real potential lies on the unit circle** | **`norm_floquet_multiplier_eq_one_of_small_potential`** | **built** |
| 441 | **an eigen-clock in a weak static real potential keeps exact time**: `E(nT) = E(0)` | **`kgFieldEnergy_eigen_conserved_of_small_potential`** | **built** |
| 442 | the same, in the autonomous register | `kgFieldEnergy_eigen_conserved` | **built** |
| 443 | **a continuous periodic function is bounded** | `exists_bound_of_periodic` | **built** |
| 444 | **a nonvanishing one is bounded away from zero** | `exists_pos_lower_bound_of_periodic` | **built** |
| 445 | the solution is its exponential factor times its periodic part | `kgFieldStateT_eq_exp_smul` | **built** |
| 446 | the periodic part is continuous | `continuous_kgFloquetPeriodicPart` | **built** |
| 447 | **the periodic part of an eigen-solution is periodic** | `periodic_kgFloquetPeriodicPart` | **built** |
| 448 | the norm splits as `e^{(Re μ)t}` times the periodic part | `norm_kgFieldStateT_eq_exp_mul` | **built** |
| 449 | **the exponential envelope of an eigen-solution, above, at every real time** | **`exists_envelope_of_eigen`** | **built** |
| 450 | **the exact two-sided envelope of a nonvanishing eigen-solution** | **`exists_two_sided_envelope_of_eigen`** | **built** |
| 451 | the state in a weak static real potential is bounded below at every instant | `norm_kgFieldStateT_ge_all_time` | **built** |
| 452 | hence it never vanishes | `kgFieldStateT_ne_zero_of_small_potential` | **built** |
| 453 | **an eigen-clock in a weak static real potential has a flat envelope** | **`exists_flat_envelope_of_small_potential`** | **built** |
| 454 | a symmetry of the free blocks commutes with the free propagator | `kgDiagOp_kgPropagator` | **built** |
| 455 | a symmetry of the potential commutes with the source operator | `kgDiagOp_kgSourceOp` | **built** |
| 456 | hence with the Duhamel kernel | `kgDiagOp_kgStateKernelT` | **built** |
| 457 | and with the free state | `kgDiagOp_kgStateFree` | **built** |
| 458 | **a symmetry of the background is a symmetry of the flow** | **`kgDiagOp_kgStateMildT`** | **built** |
| 459 | the symmetry law in the state register | `kgFieldStateT_diag` | **built** |
| 460 | the symmetry law for the gradient | `kgFieldGradT_diag` | **built** |
| 461 | the symmetry law for the velocity | `kgFieldVelT_diag` | **built** |
| 462 | **the monodromy commutes with any symmetry of the background** | **`kgMonodromy_kgDiagOp_comm`** | **built** |
| 463 | **a datum fixed by a symmetry stays fixed for all time** | **`kgFieldStateT_fixed`** | **built** |
| 464 | **two Fourier multipliers commute** | `fourierMulCLM_comm` | **built** |
| 465 | a Fourier multiplier commutes with `cos t⟨D⟩` | `fourierMulCLM_kgCosOp_comm` | **built** |
| 466 | a Fourier multiplier commutes with `sin t⟨D⟩` | `fourierMulCLM_kgSinOp_comm` | **built** |
| 467 | a Fourier multiplier commutes with `⟨D⟩⁻¹` | `fourierMulCLM_kgFreqInvOp_comm` | **built** |
| 468 | **for a frequency-diagonal background every Fourier multiplier is a symmetry of the flow** | **`kgFieldStateT_fourierMul_symmetry`** | **built** |
| 469 | its monodromy commutes with every Fourier multiplier | `kgMonodromy_fourierMul_comm` | **built** |
| 470 | **a frequency-diagonal background cannot move energy between bands** | **`kgFieldStateT_band_invariant`** | **built** |
| 471 | on a band-limited state a diagonal potential is unchanged by truncation | `kgSourceOp_kgBandOp_eq` | **built** |
| 472 | **on a frequency-diagonal background the band model is exact** | **`kgStateMildT_kgBandOp_eq`** | **built** |
| 473 | the same, in the state register | `kgFieldStateT_kgBandOp_eq` | **built** |
| 474 | **the band energy is exact, at every time** | **`kgFieldEnergyT_kgBandOp_eq`** | **built** |
| 475 | the state is additive in the Cauchy datum | `kgFieldStateT_add` | **built** |
| 476 | the zero datum generates the zero state | `kgFieldStateT_zero_datum` | **built** |
| 477 | **the trajectory splits across a projection, and the pieces stay apart** | **`kgFieldStateT_decouple`** | **built** |
| 478 | **a clock in a frequency-diagonal background decouples across every band** | **`kgFieldStateT_band_decouple`** | **built** |
| 479 | **multiplication by a real bounded symbol is self-adjoint on `L²`** | `lpBoundedMulCLM_inner` | **built** |
| 480 | **a Fourier multiplier with a real symbol is self-adjoint** | **`fourierMulCLM_inner`** | **built** |
| 481 | the low-pass symbol is real | `starRingEnd_kgLowPass` | **built** |
| 482 | **the low-pass projection is orthogonal** | `kgLowPassOp_inner` | **built** |
| 483 | **a clock in a weak real diagonal potential has its energy trapped, at every instant** | **`kgFieldEnergy_trapped_diagonal`** | **built** |
| 484 | its state is bounded above and below by the same constant | `norm_kgFieldState_trapped_diagonal` | **built** |
| 485 | the energy norm in components | `norm_kgEnergy_sq` | **built** |
| 486 | the first component of a fixed state is fixed | `kgDiagOp_fixed_fst` | **built** |
| 487 | the second component of a fixed state is fixed | `kgDiagOp_fixed_snd` | **built** |
| 488 | the first component of an annihilated state is annihilated | `kgDiagOp_zero_fst` | **built** |
| 489 | the second component of an annihilated state is annihilated | `kgDiagOp_zero_snd` | **built** |
| 490 | **what a self-adjoint projection fixes is orthogonal to what it annihilates** | `inner_eq_zero_of_proj` | **built** |
| 491 | **Pythagoras on the energy space, across a self-adjoint projection** | `norm_kgEnergy_add_sq` | **built** |
| 492 | **the state splits orthogonally across every band, at every time** | **`norm_kgFieldStateT_band_split`** | **built** |
| 493 | **a clock's energy is the sum of its band energies** | **`kgFieldEnergyT_band_split`** | **built** |
| 494 | the annulus symbol is measurable | `measurable_kgAnnulus` | **built** |
| 495 | it is bounded by one | `norm_kgAnnulus_le` | **built** |
| 496 | it is real | `starRingEnd_kgAnnulus` | **built** |
| 497 | it takes only the values `0` and `1` | `kgAnnulus_mul_self` | **built** |
| 498 | on ordered radii it is the difference of the low-pass symbols | `kgAnnulus_eq_sub` | **built** |
| 499 | the annulus projection is bounded by one | `norm_kgAnnulusOp_le` | **built** |
| 500 | **the annulus projection is idempotent** | `kgAnnulusOp_idem` | **built** |
| 501 | **the annulus projection is orthogonal** | `kgAnnulusOp_inner` | **built** |
| 502 | on ordered radii it is the difference of the low-pass projections | `kgAnnulusOp_eq_sub` | **built** |
| 503 | **a clock decouples across every annulus of frequencies** | **`kgFieldStateT_annulus_decouple`** | **built** |
| 504 | **its energy is the energy inside the annulus plus the energy outside** | **`kgFieldEnergyT_annulus_split`** | **built** |
| 505 | the high-frequency part of a datum vanishes as the cutoff grows | `tendsto_norm_sub_kgLowPassOp` | **built** |
| 506 | the energy splits into low and high parts, autonomously | `kgFieldEnergy_band_split_static` | **built** |
| 507 | **the high-frequency energy is a fixed multiple of its own initial value, at every time** | **`kgFieldEnergy_high_le`** | **built** |
| 508 | **no ultraviolet cascade**: a cutoff above which the clock carries less than `ε`, for all time | **`exists_cutoff_high_energy_small`** | **built** |
| 509 | **all but `ε` of a clock's energy stays below a fixed frequency, forever** | **`kgFieldEnergy_no_uv_cascade`** | **built** |
| 510 | **the energy below a cutoff is trapped, two-sidedly** | `kgFieldEnergy_low_trapped` | **built** |
| 511 | **the energy above a cutoff is trapped, two-sidedly** | `kgFieldEnergy_high_trapped` | **built** |
| 512 | **the energy in any annulus is trapped, two-sidedly** | **`kgFieldEnergy_annulus_trapped`** | **built** |
| 513 | the energy splits across an annulus, autonomously | `kgFieldEnergy_annulus_split_static` | **built** |
| 514 | **the spectral profile of a clock is frozen** | **`kgFieldEnergy_spectrum_frozen`** | **built** |
| 515 | **a self-adjoint projection splits the norm of a datum orthogonally** | `norm_sq_split_of_proj` | **built** |
| 516 | **the initial energy splits orthogonally across a band** | `kgDatum_energy_split` | **built** |
| 517 | the same across any annulus | `kgDatum_energy_split_annulus` | **built** |
| 518 | the energy inside an annulus obeys the estimate with its own initial energy | `kgFieldEnergyT_annulus_le` | **built** |
| 519 | the same outside the annulus | `kgFieldEnergyT_annulus_compl_le` | **built** |
| 520 | **the card's inequality, band by band, for a moving diagonal background** | **`kgFieldEnergyT_band_resolved`** | **built** |
| 521 | the high-frequency energy of a moving diagonal background is charged to its own initial value | `kgFieldEnergyT_high_le` | **built** |
| 522 | **no cascade on a finite window** | **`exists_cutoff_high_energy_small_window`** | **built** |
| 523 | **on any finite window all but `ε` of the energy stays below a fixed frequency** | **`kgFieldEnergyT_no_uv_cascade_window`** | **built** |
| 524 | the shifted frequency is nonnegative | `kgShiftedFreq_nonneg` | **built** |
| 525 | its radicand is positive for a weak potential | `kgShiftedFreq_sq_arg_pos` | **built** |
| 526 | **the shifted frequency is a genuine positive frequency** | **`kgShiftedFreq_pos`** | **built** |
| 527 | **it squares to `⟨ξ⟩² + v`** | **`kgShiftedFreq_sq`** | **built** |
| 528 | it is bounded below away from zero | `one_sub_le_kgShiftedFreq_sq` | **built** |
| 529 | the shifted frequency is measurable | `measurable_kgShiftedFreq` | **built** |
| 530 | the shifted symbols are measurable | `measurable_kgShiftedCos`, `measurable_kgShiftedSin`, `measurable_kgShiftedSinOverFreq` | **built** |
| 531 | the shifted cosine and sine are bounded by one | `norm_kgShiftedCos_le`, `norm_kgShiftedSin_le` | **built** |
| 532 | **`sin(tΩ)/Ω` is bounded by the elapsed time** | **`norm_kgShiftedSinOverFreq_le`** | **built** |
| 533 | the shifted symbols are real | `starRingEnd_kgShiftedCos`, `starRingEnd_kgShiftedSinOverFreq` | **built** |
| 534 | the shifted propagators are bounded | `norm_kgShiftedCosOp_le`, `norm_kgShiftedSinFreqOp_le` | **built** |
| 535 | **the shifted propagators are self-adjoint** | `kgShiftedCosOp_inner`, `kgShiftedSinFreqOp_inner` | **built** |
| 536 | the shifted symbols at time zero | `kgShiftedCos_zero`, `kgShiftedSin_zero`, `kgShiftedSinOverFreq_zero` | **built** |
| 537 | **the cosine addition formula for the shifted frequency** | **`kgShiftedCos_add`** | **built** |
| 538 | **the sine addition formula for the shifted frequency** | **`kgShiftedSin_add`** | **built** |
| 539 | **the addition formula for `sin(tΩ)/Ω`**, valid where `Ω` degenerates | **`kgShiftedSinOverFreq_add`** | **built** |
| 540 | the shifted symbols lie on the circle | `kgShiftedSin_sq_add_cos_sq` | **built** |
| 541 | the shifted sine propagator | `kgShiftedSinOp`, `norm_kgShiftedSinOp_le` | **built** |
| 542 | **the shifted cosine propagator is the identity at time zero** | `kgShiftedCosOp_zero` | **built** |
| 543 | the shifted sine propagators vanish at time zero | `kgShiftedSinOp_zero`, `kgShiftedSinFreqOp_zero` | **built** |
| 544 | **the group law of the shifted cosine propagator** | **`kgShiftedCosOp_add`** | **built** |
| 545 | **the group law of the shifted sine propagator** | **`kgShiftedSinFreqOp_add`** | **built** |
| 546 | **below a fixed frequency the shifted frequency is bounded** | `kgShiftedFreq_sq_le` | **built** |
| 547 | the band bound is nonnegative | `band_bound_nonneg` | **built** |
| 548 | the shifted cosine defect symbol is measurable | `measurable_kgShiftedCosDefectLow` | **built** |
| 549 | **the shifted cosine defect is second order on a band** | `norm_kgShiftedCosDefectLow_le` | **built** |
| 550 | **the shifted cosine propagator is the identity to second order below a fixed frequency** | **`norm_kgShiftedCosOp_lowPass_sub_le`** | **built** |
| 551 | the shifted sine defect symbol is measurable | `measurable_kgShiftedSinDefectLow` | **built** |
| 552 | **the shifted sine defect is third order on a band** | `norm_kgShiftedSinDefectLow_le` | **built** |
| 553 | **the shifted sine propagator is multiplication by the elapsed time to third order** | **`norm_kgShiftedSinFreqOp_lowPass_sub_le`** | **built** |
| 554 | **the shifted sine propagator differentiates to the shifted cosine propagator, below a fixed frequency** | **`hasDerivAt_kgShiftedSinFreqOp_lowPass`** | **built** |
| 555 | the generator symbol is measurable | `measurable_kgShiftedFreqSqLow` | **built** |
| 556 | **below a fixed frequency the generator symbol is bounded** | `norm_kgShiftedFreqSqLow_le` | **built** |
| 557 | the generator symbol is real | `starRingEnd_kgShiftedFreqSqLow` | **built** |
| 558 | **the generator of the shifted propagator on a band** | `kgShiftedFreqSqLowOp`, `norm_kgShiftedFreqSqLowOp_le` | **built** |
| 559 | **the generator is self-adjoint** | `kgShiftedFreqSqLowOp_inner` | **built** |
| 560 | **the cosine addition formula through the bounded sine symbol, cut to a band** | **`kgShiftedCos_add_lowPass`** | **built** |
| 561 | **the group law of the shifted cosine propagator, in bounded form on a band** | **`kgShiftedCosOp_lowPass_add`** | **built** |
| 562 | **the second equation of motion**: `d/dt cos(tΩ) = −Ω²·(sin(tΩ)/Ω)` on a band | **`hasDerivAt_kgShiftedCosOp_lowPass`** | **built** |
| 563 | the complex symbol of a real diagonal potential | `kgRealPotSymbol`, `measurable_kgRealPotSymbol` | **built** |
| 564 | it is bounded by the potential's size and is real | `norm_kgRealPotSymbol_le`, `starRingEnd_kgRealPotSymbol` | **built** |
| 565 | the shifted frequency of a real potential uses the negated symbol | `abs_neg_pot_le` | **built** |
| 566 | **the generator against `⟨D⟩⁻²` collapses to the equation's right-hand side** | **`kgFreqInvSq_kgShiftedFreqSqLow`** | **built** |
| 567 | the shifted cosine propagator commutes with the band projection | `kgShiftedCosOp_kgLowPassOp_comm` | **built** |
| 568 | the shifted sine propagator commutes with it | `kgShiftedSinFreqOp_kgLowPassOp_comm` | **built** |
| 569 | the generator commutes with it | `kgShiftedFreqSqLowOp_kgLowPassOp_comm` | **built** |
| 570 | **the collapse in operator form**: `⟨D⟩⁻²(Ω²χ(Pz)) = Pz − ⟨D⟩⁻²(p(Pz))` | **`kgFreqInvOp_sq_kgShiftedFreqSqLowOp`** | **built** |
| 571 | the explicit field, velocity and acceleration of the shifted propagator | `kgShiftedField`, `kgShiftedVel`, `kgShiftedAcc` | **built** |
| 572 | **the shifted field stays band-limited** | `kgLowPassOp_kgShiftedField` | **built** |
| 573 | **the field differentiates to the velocity** | `hasDerivAt_kgShiftedField` | **built** |
| 574 | **the velocity differentiates to the acceleration** | `hasDerivAt_kgShiftedVel` | **built** |
| 575 | **the shifted field satisfies the strong equation** | **`kgShiftedField_equation`** | **built** |
| 576 | **the shifted propagator is a strong solution of the band problem** | **`solvesKGSourceT_kgShifted`** | **built** |
| 577 | it starts at the projected data | `kgShiftedField_zero`, `kgShiftedVel_zero` | **built** |
| 578 | **it is the only strong solution with those data** | **`eq_kgShiftedField_of_solvesKGSourceT`** | **built** |
| 579 | **the mild field of a real diagonal potential on a band is the shifted propagator** | **`kgFieldMildT_eq_kgShiftedField`** | **built** |
| 580 | **the mild velocity is the shifted velocity** | **`kgFieldVelT_eq_kgShiftedVel`** | **built** |
| 581 | **two symbols equal a.e. give the same multiplier, whatever bounds build it** | `fourierMulCLM_congr` | **built** |
| 582 | **at zero potential the shifted frequency is the free frequency** | `kgShiftedFreq_zero` | **built** |
| 583 | the shifted symbols reduce to the free symbols | `kgShiftedCos_zero_pot`, `kgShiftedSinOverFreq_zero_pot` | **built** |
| 584 | **at zero potential the shifted cosine propagator is the free one** | `kgShiftedCosOp_zero_pot` | **built** |
| 585 | **at zero potential the shifted sine propagator is the free one** | `kgShiftedSinFreqOp_zero_pot` | **built** |
| 586 | **the modified energy of a real diagonal potential is exactly conserved** | **`kgFieldEnergy_conserved_diagonal`** | **built** |
| 587 | **the field of a real diagonal potential, from band-limited data, is the shifted propagator — no band compression** | **`kgFieldMildT_diagonal_eq_kgShiftedField`** | **built** |
| 588 | the potential that flattens the frequency below `√b` | `kgFlatPot`, `measurable_kgFlatPot` | **built** |
| 589 | it is bounded by `b` | `abs_kgFlatPot_le` | **built** |
| 590 | **on its band the shifted frequency is one** | **`kgShiftedFreq_kgFlatPot`** | **built** |
| 591 | **on its band the shifted cosine symbol is the constant `cos t`** | `kgShiftedCos_kgFlatPot_lowPass` | **built** |
| 592 | **on its band the shifted sine symbol is the constant `sin t`** | `kgShiftedSinOverFreq_kgFlatPot_lowPass` | **built** |
| 593 | **on the flat band the shifted cosine propagator is the scalar `cos t`** | `kgShiftedCosOp_kgFlatPot` | **built** |
| 594 | **on the flat band the shifted sine propagator is the scalar `sin t`** | `kgShiftedSinFreqOp_kgFlatPot` | **built** |
| 595 | **the clock of the flattening potential is a plane rotation** | **`kgShiftedField_kgFlatPot`** | **built** |
| 596 | **the clock is exactly `2π`-periodic** | **`kgShiftedField_kgFlatPot_periodic`** | **built** |
| 597 | **it returns exactly to its initial state after one period** | **`kgShiftedField_kgFlatPot_two_pi`** | **built** |
| 598 | on the flat band the generator symbol is the band symbol | `kgShiftedFreqSqLow_kgFlatPot_lowPass` | **built** |
| 599 | **on the flat band the generator is the identity** | `kgShiftedFreqSqLowOp_kgFlatPot` | **built** |
| 600 | **the velocity of the periodic clock is the rotated datum** | `kgShiftedVel_kgFlatPot` | **built** |
| 601 | the velocity returns after one period | `kgShiftedVel_kgFlatPot_two_pi` | **built** |
| 602 | **the monodromy of the periodic clock fixes every band-limited state** | **`kgMonodromy_kgFlatPot_fixed`** | **built** |
| 603 | **the band compression of a self-adjoint operator is self-adjoint** | `kgBandOp_inner` | **built** |
| 604 | **the periodic clock is a Floquet eigen-solution with multiplier one** | **`kgMonodromy_kgFlatPot_eigen`** | **built** |
| 605 | **the shifted frequency is bounded below by `√(1−b)`** | `sqrt_one_sub_le_kgShiftedFreq` | **built** |
| 606 | **the shifted sine symbol is bounded uniformly in time** | `norm_kgShiftedSinOverFreq_le_inv` | **built** |
| 607 | so is the shifted sine propagator | `norm_kgShiftedSinFreqOp_le_inv` | **built** |
| 608 | **a clock in a weak real diagonal potential does not drift** | **`norm_kgShiftedField_le`** | **built** |
| 609 | **the velocity of a diagonal clock is bounded uniformly in time** | **`norm_kgShiftedVel_le`** | **built** |
| 610 | **a diagonal clock drifts in neither position nor velocity** | **`norm_kgShiftedField_and_vel_le`** | **built** |
| 611 | the potential that tunes the frequency to `c` on its band | `kgTunedPot`, `measurable_kgTunedPot` | **built** |
| 612 | the frequency squares to `1 + ‖ξ‖²` | `kgFreq_sq_eq` | **built** |
| 613 | **the tuned potential is admissible for `1 ≤ c² ≤ 1 + b`** | **`abs_kgTunedPot_le`** | **built** |
| 614 | **on its band it makes the shifted frequency `c`** | **`kgShiftedFreq_kgTunedPot`** | **built** |
| 615 | the shifted cosine symbol becomes `cos(ct)` there | `kgShiftedCos_kgTunedPot_lowPass` | **built** |
| 616 | the shifted sine symbol becomes `sin(ct)/c` there | `kgShiftedSinOverFreq_kgTunedPot_lowPass` | **built** |
| 617 | a positive square root at least one is at least one | `one_le_of_one_le_sq` | **built** |
| 618 | **on the tuned band the shifted cosine propagator is the scalar `cos(ct)`** | `kgShiftedCosOp_kgTunedPot` | **built** |
| 619 | **on the tuned band the shifted sine propagator is the scalar `sin(ct)/c`** | `kgShiftedSinFreqOp_kgTunedPot` | **built** |
| 620 | **the tuned clock is the plane rotation at rate `c`** | **`kgShiftedField_kgTunedPot`** | **built** |
| 621 | **it has exact period `2π/c`** | **`kgShiftedField_kgTunedPot_periodic`** | **built** |
| 622 | **it returns to its initial state after one period** | **`kgShiftedField_kgTunedPot_period`** | **built** |
| 623 | on the tuned band the generator symbol is `c²` times the band symbol | `kgShiftedFreqSqLow_kgTunedPot_lowPass` | **built** |
| 624 | **on the tuned band the generator is multiplication by `c²`** | `kgShiftedFreqSqLowOp_kgTunedPot` | **built** |
| 625 | **the velocity of the tuned clock is `−(c sin ct)Px + (cos ct)Py`** | **`kgShiftedVel_kgTunedPot`** | **built** |
| 626 | the velocity returns after one period | `kgShiftedVel_kgTunedPot_period` | **built** |
| 627 | **the state of the tuned clock returns after one period** | **`kgFieldStateT_kgTunedPot_period`** | **built** |
| 628 | **the tuned clock is a Floquet eigen-solution with multiplier one at its own period** | **`kgMonodromy_kgTunedPot_eigen`** | **built** |
| 629 | the phase acquired by the tuned clock, and its modulus one | `kgTunedPhase`, `norm_kgTunedPhase` | **built** |
| 630 | **the clock started from `(Px, −icPx)` acquires that phase** | **`kgShiftedField_kgTunedPot_circle`** | **built** |
| 631 | **so does its velocity** | **`kgShiftedVel_kgTunedPot_circle`** | **built** |
| 632 | **the whole state rotates by the phase** | **`kgFieldStateT_kgTunedPot_circle`** | **built** |
| 633 | **every point of the unit circle is an attained Floquet multiplier** | **`kgMonodromy_kgTunedPot_circle_eigen`** | **built** |
| 634 | **the band carries a nonzero state** | **`exists_ne_zero_kgLowPassOp_fixed`** | **built** |
| 635 | the frequency operator does not kill a nonzero band element | `kgFreqLowOp_ne_zero_of_fixed` | **built** |
| 636 | a pair with nonzero first component is nonzero | `kgPair_ne_zero_of_fst` | **built** |
| 637 | **the band supplies a nonzero energy-space datum** | **`exists_ne_zero_eigen_state`** | **built** |
| 638 | **the periodic clock keeps exact time, by the general eigen-clock law** | **`exists_periodic_clock_energy_conserved`** | **built** |
| 639 | **the unit-modulus law applied to the tuned clock** | **`exists_tuned_clock_multiplier_norm_one`** | **built** |
| 640 | the phase is an exponential with imaginary exponent | `kgTunedPhase_eq_exp` | **built** |
| 641 | **the flat envelope applied to the tuned clock** | **`exists_tuned_clock_flat_envelope`** | **built** |
| 642 | **the state norm of the tuned eigen-clock is constant in time** | **`norm_kgFieldStateT_kgTunedPot_circle`** | **built** |
| 643 | **it conserves its energy at every instant** | **`kgFieldEnergyT_kgTunedPot_circle`** | **built** |
| 644 | **the gradient of the tuned clock from a real datum** | `kgFieldGradT_kgTunedPot_real` | **built** |
| 645 | **its velocity** | `kgFieldVelT_kgTunedPot_real` | **built** |
| 646 | **the exact energy of the tuned clock from a real datum** | **`kgFieldEnergyT_kgTunedPot_real`** | **built** |
| 647 | **at time zero the energy is carried entirely by the gradient** | `kgFieldEnergyT_kgTunedPot_real_zero` | **built** |
| 648 | **a quarter period later, entirely by the velocity** | `kgFieldEnergyT_kgTunedPot_real_quarter` | **built** |
| 649 | **the energy never leaves the interval between the two** | **`kgFieldEnergyT_kgTunedPot_real_between`** | **built** |
| 650 | **the projection is dominated by the frequency-weighted vector** | `norm_kgLowPassOp_le_norm_kgFreqLowOp` | **built** |
| 651 | **and dominates it up to `√(1+R²)`** | `norm_kgFreqLowOp_le_norm_kgLowPassOp` | **built** |
| 652 | **the excursion of the oscillating energy is the frequency spread of its band** | **`kgFieldEnergyT_kgTunedPot_real_spread`** | **built** |
| 653 | **the explicit excursion factor lies inside the trapping band** | **`excursion_le_trap_band`** | **built** |
| 654 | the gap between them is `2b²/(1−b)` | `trap_band_sub_excursion` | **built** |
| 655 | **the model's energy obeys the general trapping bound** | **`kgFieldEnergyT_kgTunedPot_real_le_trap`** | **built** |
| 656 | the trapping comparison in cleared form | `excursion_mul_le` | **built** |
| 657 | **the model's energy obeys the lower trapping bound too** | **`kgFieldEnergyT_kgTunedPot_real_ge_trap`** | **built** |
| 658 | **on a sub-band the shifted cosine symbol is still `cos(ct)`** | `kgShiftedCos_kgTunedPot_subband` | **built** |
| 659 | **and the sine symbol still `sin(ct)/c`** | `kgShiftedSinOverFreq_kgTunedPot_subband` | **built** |
| 660 | **and the generator symbol still `c²`** | `kgShiftedFreqSqLow_kgTunedPot_subband` | **built** |
| 661 | **on a sub-band the shifted cosine propagator is the scalar `cos(ct)`** | `kgShiftedCosOp_kgTunedPot_subband` | **built** |
| 662 | **and the sine propagator the scalar `sin(ct)/c`** | `kgShiftedSinFreqOp_kgTunedPot_subband` | **built** |
| 663 | **on a sub-band the tuned generator is multiplication by `c²`** | `kgShiftedFreqSqLowOp_kgTunedPot_subband` | **built** |
| 664 | **the velocity of the tuned clock on a sub-band** | **`kgShiftedVel_kgTunedPot_subband`** | **built** |
| 665 | **the field of the tuned clock from arbitrary band-limited data** | **`kgFieldMildT_kgTunedPot_band`** | **built** |
| 666 | **its velocity from arbitrary band-limited data** | **`kgFieldVelT_kgTunedPot_band`** | **built** |
| 667 | **the tuned clock in field coordinates** | `kgFieldMildT_kgTunedPot_field` | **built** |
| 668 | **its velocity in field coordinates** | `kgFieldVelT_kgTunedPot_field` | **built** |
| 669 | **a quarter period sends the field to `(1/c)·h`** | `kgFieldMildT_kgTunedPot_quarter` | **built** |
| 670 | **and the velocity to `−c·w`** | `kgFieldVelT_kgTunedPot_quarter` | **built** |
| 671 | **one switching cycle is `(w,h) ↦ (−(c₁/c₂)·w, −(c₂/c₁)·h)`** | **`kgSwitchedClock_step`** | **built** |
| 672 | **so the velocity norm is multiplied by `c₂/c₁` per cycle** | **`norm_kgSwitchedClock_vel`** | **built** |

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
`KleinGordonTimePotentialStability.lean` (150–151), `KleinGordonTimePotentialFlow.lean` (152–154), `KleinGordonIllPosed.lean` (155–159), `KleinGordonSecondOrderDuhamel.lean` (160–162),
`KleinGordonLowPass.lean` (163–165), `KleinGordonConditionalStability.lean` (166–168),
`KleinGordonBandStability.lean` (169–171), `KleinGordonTimeBandStability.lean` (172–174),
`KleinGordonOptimalProbe.lean` (175–177), `KleinGordonFieldEnergy.lean` (178–182),
`KleinGordonTimeFieldEnergy.lean` (183–186), `KleinGordonExactConservation.lean` (187–189), `KleinGordonUniformEnergy.lean` (190–192),
`KleinGordonRealPotential.lean` (193–196), `KleinGordonTimeReducedState.lean` (197–198),
`KleinGordonAdiabatic.lean` (199–201), `KleinGordonAdiabaticWork.lean` (202–204),
`KleinGordonSwitchedPotential.lean` (205–208), `KleinGordonBandPotential.lean` (209–212),
`KleinGordonBandLimit.lean` (213–216), `KleinGordonBandInvariance.lean` (217–220),
`KleinGordonBandFrequency.lean` (221–224), `KleinGordonBandStrong.lean` (225–226),
`KleinGordonBandWellPosed.lean` (227–229), `KleinGordonBandEnergy.lean` (230–232),
`KleinGordonStrongDifference.lean` (233–234), `KleinGordonBandApproximation.lean` (235–236),
`KleinGordonBandStateApprox.lean` (237–240),
`KleinGordonBandStateConvergence.lean` (241–244), `KleinGordonBandUniform.lean` (245–246),
`KleinGordonTimeBandDifference.lean` (247–249), `KleinGordonTimeBandApproximation.lean` (250–253),
`KleinGordonTimeBandStateConvergence.lean` (254–258),
`KleinGordonStateDifference.lean` (259–262), `KleinGordonBandStateUniform.lean` (263–265),
`KleinGordonBandEnergyUniform.lean` (266), `KleinGordonTimeStateDifference.lean` (267–272),
`KleinGordonTimeBandEnergyUniform.lean` (273),
`KleinGordonTimeStrongSolution.lean` (274–277), `KleinGordonTimeBandStrong.lean` (278–281),
`KleinGordonTimeBandGradient.lean` (282–283), `KleinGordonBandSwitchedWork.lean` (284–288),
`KleinGordonBandAdiabaticLimit.lean` (289–292), `KleinGordonFloquet.lean` (293–300),
`KleinGordonMonodromy.lean` (301–305), `KleinGordonFloquetStability.lean` (306–310),
`KleinGordonFloquetDichotomy.lean` (311–315), `KleinGordonFloquetInhabited.lean` (316–319),
`KleinGordonBandMonodromy.lean` (320–324), `KleinGordonFloquetSpectrum.lean` (325–328),
`KleinGordonFloquetDecay.lean` (329–331), `KleinGordonFloquetTrichotomy.lean` (332–335),
`KleinGordonMonodromyLipschitz.lean` (336–339), `KleinGordonFloquetNontrivial.lean` (340–344),
`KleinGordonFreeMultipliers.lean` (345–347), `KleinGordonOscillatory.lean` (348–351),
`KleinGordonStateReflection.lean` (352–355), `KleinGordonBandOscillatory.lean` (356–359),
`KleinGordonTimeReversalSpectrum.lean` (360–364), `KleinGordonTwoWayClock.lean` (365–367),
`KleinGordonProbeEverywhere.lean` (368–369), `KleinGordonExactReconstruction.lean` (370–371),
`KleinGordonPeriodicReconstruction.lean` (372–374), `KleinGordonBandReconstruction.lean` (375–376),
`KleinGordonFullReconstruction.lean` (377–379), `KleinGordonPotentialInjective.lean` (380–382),
`KleinGordonMovingPotential.lean` (383–384), `KleinGordonPeriodicPotential.lean` (385–386),
`KleinGordonObservationFate.lean` (387–390), `KleinGordonMultiplierAnnulus.lean` (391–392),
`KleinGordonNoFreeDrift.lean` (393–395), `KleinGordonFloquetExponent.lean` (396–397),
`KleinGordonTimeSymmetric.lean` (398–400), `KleinGordonSymmetricStability.lean` (401–403),
`KleinGordonRadiusAnnulus.lean` (404–406), `KleinGordonGrowthRate.lean` (407–409),
`KleinGordonExactRate.lean` (410–412), `KleinGordonContinuousRate.lean` (413–414),
`KleinGordonBandRate.lean` (415–417), `KleinGordonEnergyRate.lean` (418–420),
`KleinGordonEnergyExponent.lean` (421), `KleinGordonTwoSidedRate.lean` (422–424),
`KleinGordonEnergyTwoSided.lean` (425), `KleinGordonTrappedEnergy.lean` (426–429),
`KleinGordonTrappedAllTime.lean` (430), `KleinGordonFloquetNormalForm.lean` (431–438),
`KleinGordonEigenClock.lean` (439–442), `KleinGordonEigenEnvelope.lean` (443–453), `KleinGordonSymmetry.lean` (454–463), `KleinGordonMultiplierSymmetry.lean` (464–470), `KleinGordonBandExact.lean` (471–474), `KleinGordonBandSplitting.lean` (475–478),
`KleinGordonSelfAdjointMultiplier.lean` (479–484),
`KleinGordonBandEnergySplit.lean` (485–493), `KleinGordonAnnulus.lean` (494–504), `KleinGordonNoCascade.lean` (505–509), `KleinGordonSpectrumFrozen.lean` (510–514), `KleinGordonBandResolved.lean` (515–520), `KleinGordonWindowCascade.lean` (521–523),
`KleinGordonShiftedFrequency.lean` (524–535), `KleinGordonShiftedGroupLaw.lean` (536–545), `KleinGordonShiftedBandDefect.lean` (546–553), `KleinGordonShiftedDerivative.lean` (554), `KleinGordonShiftedGenerator.lean` (555–560),
`KleinGordonShiftedEquationOfMotion.lean` (561–562),
`KleinGordonShiftedInverseSquare.lean` (563–566),
`KleinGordonShiftedBandCommutation.lean` (567–570),
`KleinGordonShiftedStrongSolution.lean` (571–578),
`KleinGordonShiftedIdentification.lean` (579–580), `KleinGordonShiftedFreeCase.lean` (581–586), `KleinGordonDiagonalClosedForm.lean` (587), `KleinGordonFlatBandPotential.lean` (588–592), `KleinGordonPeriodicClock.lean` (593–597), `KleinGordonMonodromyFixed.lean` (598–602), `KleinGordonEigenWitness.lean` (603–604), `KleinGordonDiagonalNoDrift.lean` (605–608),
`KleinGordonDiagonalVelocityBound.lean` (609–610), `KleinGordonTunedClock.lean` (611–616), `KleinGordonTunedClockPeriod.lean` (617–622), `KleinGordonTunedVelocity.lean` (623–625), `KleinGordonTunedMonodromy.lean` (626–628), `KleinGordonTunedCircleData.lean` (629–631), `KleinGordonCircleMultiplier.lean` (632–633), `KleinGordonBandNonzero.lean` (634), `KleinGordonEigenStateNonzero.lean` (635–637),
`KleinGordonPeriodicClockConserved.lean` (638),
`KleinGordonTunedUnitModulus.lean` (639), `KleinGordonTunedFlatEnvelope.lean` (640–641), `KleinGordonTunedExactNorm.lean` (642–643), `KleinGordonTunedRealDatum.lean` (644–646), `KleinGordonTunedEnergyRange.lean` (647–649),
`KleinGordonBandFrequencySpread.lean` (650–652),
`KleinGordonModelInsideTrap.lean` (653–655), `KleinGordonModelTrapLower.lean` (656–657), `KleinGordonTunedSubband.lean` (658–660), `KleinGordonTunedSubbandOps.lean` (661–662),
`KleinGordonTunedSubbandVelocity.lean` (663–664), `KleinGordonTunedBandData.lean` (665–666),
`KleinGordonSwitchedClock.lean` (667–672).
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
the observations determine the equation, and they determine it stably in the forward direction. The
inverse direction is settled — negatively — by statements 155–159.

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
constant case.

### The inverse problem is ill-posed

Statements 135–154 make the forward map `W ↦ u` a continuous injection. Statements 155–159 settle the
remaining question — whether its *inverse* is continuous — in the negative, and the obstruction is
visible in the symbol rather than in any estimate.

The half-order propagator `sin(τ⟨ξ⟩)/⟨ξ⟩` decays like `⟨ξ⟩⁻¹`. A perturbation living entirely above
frequency `R` therefore enters the Duhamel term damped by `⟨R⟩⁻¹`, no matter how large its operator
norm. The witness is the **high-pass multiplier** `kgHighPassOp`, with symbol `c·1_{‖ξ‖ ≥ R}`. Its
norm is exactly `c` (**`norm_kgHighPassOp`**) — the upper bound is the symbol bound, and the lower
bound is attained on any function whose spectrum lies in a ball at distance `≥ R` from the origin,
the same `kgBallFun` witness that showed `⟨D⟩⁻¹` is not surjective (statements 114–116). But
composed with the propagator its norm collapses:

**`norm_kgSinFreqOp_comp_kgHighPassOp`**: `‖sin(τ⟨D⟩)/⟨D⟩ ∘ W_R‖ ≤ c/√(1+R²)`,

and this is an operator-norm bound on the *composite*, not the product of the two operator norms —
it is only visible at the level of symbols, which is why the Fourier-multiplier presentation of the
whole card pays off here. Feeding it into the Duhamel formula together with the a-priori bound of
statement 85 gives

**`norm_kgFieldMild_kgHighPassOp_sub_free_le`**:
`‖u_{W_R}(t) − u_free(t)‖ ≤ (c/√(1+R²))·|t|·(‖f‖+‖h‖)e^{c|t|}`,

uniformly over *all* Cauchy data. Choosing `R = cTe^{cT}/ε` makes the right-hand side at most
`ε(‖f‖+‖h‖)` on the whole window `[-T,T]`, so

**`exists_norm_eq_and_kgFieldMild_close`**: for every tolerance `ε` and every observation window
there is a perturbation of norm **exactly** `c` whose field is `ε`-indistinguishable from the free
field, uniformly over all data.

The forward map is therefore not bounded below, and its inverse admits no modulus of continuity:
**`exists_potentials_field_closer_than`** produces, for any factor `κ`, two admissible perturbations
whose fields are `κ` times closer than the perturbations themselves. Constant families are moving
backgrounds, so the same witness applies verbatim to the non-autonomous theory
(**`exists_norm_eq_and_kgFieldMildT_close`**).

Two consequences worth stating. First, the exponential factor in the stability estimate of statements
136 and 150 is not an artefact of the Grönwall argument — no estimate of that shape can be inverted.
Second, and this is the physically meaningful reading for a clock: a bounded background can be
arbitrarily violent at high frequency and still leave the field it acts on essentially untouched over
any prescribed observation window. What a clock reads is not the potential but the potential
convolved against a `⟨ξ⟩⁻¹`-damped kernel, and reconstruction from a finite-precision reading is
possible only under an a-priori frequency restriction that this card does not assume.

### The other side of the cut-off: conditional stability

The ill-posedness of statements 155–159 lives entirely above frequency `R` — the damping `⟨ξ⟩⁻¹` that
hides a perturbation is small only where `⟨ξ⟩` is large. Statements 160–168 show the picture reverses
below a fixed frequency: on the class of perturbations that only couple frequencies below `R`, the
forward map **is** bounded below, with a constant explicit in `R`, in the size of the perturbations,
and in the length of the observation window.

Three ingredients, each reusable.

*The propagator is bounded by the elapsed time.* `|sin(τω)/ω| ≤ |τ|`, because `|sin a| ≤ |a|`. This is
worthless for large times and sharp for small ones. Stating it needs a small piece of hygiene the
corpus had been missing: a multiplier obeys **every** bound its symbol obeys, not only the one it was
constructed with (**`norm_fourierMulCLM_le_of_bound`**). The immediate consequence is that the
perturbation enters the Duhamel term at second order,
`‖u(t) − u_free(t)‖ ≤ b(‖f‖+‖h‖)e^{b|t|}t²` (**`norm_kgFieldMild_sub_free_le_sq`**, and the same for a
moving background) — so the whole first-order behaviour of the solution is free.

*The propagators are Taylor-accurate at low frequency.* Cutting to `‖ξ‖ ≤ R` gives
`‖(cos(τ⟨D⟩) − 1)P_R‖ ≤ τ²(1+R²)/2` and `‖(sin(τ⟨D⟩)/⟨D⟩ − τ)P_R‖ ≤ |τ|³(1+R²)/6`. Both descend from
the scalar estimates `|cos a − 1| ≤ a²/2` and `|sin a − a| ≤ |a|³/6`; mathlib has the first (as
`Real.one_sub_sq_div_two_le_cos`) but not the second, which is proved here by integrating the first
along `sin a − a = ∫₀ᵃ(cos t − 1)dt`.

*The perturbation is readable off the short-time field.* Start from rest (`h = 0`) at a low-frequency
datum. The solution leaves it at second order — the free part by the cosine estimate, the Duhamel part
by statement 162 — and therefore

`∫₀ˣ (sin((x−s)⟨D⟩)/⟨D⟩)(A u(s)) ds = (x²/2)·Af + O(x⁴)`,

where the `O(x⁴)` splits into a term carrying `‖A‖` (from the motion of the datum) and a term carrying
`‖Af‖` (from the sine defect). The left-hand side is bounded by the observed discrepancy, via the
difference-Duhamel identity of statement 135. Choosing the probing time `x` short enough that
`x²((1+R²)/2 + b e^{bT}) ≤ 1/8` makes both `O(x⁴)` terms absorbable, and what is left is

**`norm_sub_le_of_lowPass`**: `‖W₁ − W₂‖ ≤ 8η(1+bT)/x²`,

where `η` is the uniform discrepancy of the two fields on `[−T,T]`. The hypothesis on the class is
exactly that the difference is low-pass on both sides, `A = P_R A P_R`; the domain restriction is what
lets a low-frequency datum test the whole operator, and the range restriction is what makes the sine
defect bounded.

Taken with 155–159 this is the complete classical picture of the inverse problem: unstable in general,
stable on any fixed frequency band, with a constant that degrades like `R⁴` as the band widens (the
admissible `x` is of order `(1+R²)^{-1/2}`).

### The constant, and the moving background

Two completions of the conditional estimate.

*The probing time is not a restriction.* `x = min(T, (8K)^{-1/2})` is always admissible
(**`exists_probe_time`**), and making the choice removes the free parameter:

**`norm_sub_le_of_lowPass_explicit`**: `‖W₁−W₂‖ ≤ 8η(1+bT)(T⁻² + 8((1+R²)/2 + b e^{bT}))`.

Paired with the Lipschitz estimate in the other direction this says that on each band the field
discrepancy and the potential discrepancy control each other (**`lowPass_band_stability`**) — the
classical formulation of a well-posed inverse problem, which holds here for every fixed band even
though it fails without one.

*A clock reads a background that moves.* Statements 172–174 redo the reconstruction for a
time-dependent perturbation, and the answer is necessarily local in time: what the short-time field
sees is the perturbation **at the initial instant**, blurred by however much it moves during the
probe. Splitting the source as

`W(s)u(s) − W(0)f = (W(s)−W(0))u(s) + W(0)(u(s)−f)`

leaves the autonomous error, of order `x⁴` after integration, plus a new term of order `Lx³` where
`L` bounds the temporal Lipschitz constant of the difference. Dividing by the `x²` that carries the
signal,

**`norm_sub_zero_le_of_lowPassT`**: `‖W₁(0) − W₂(0)‖ ≤ 8η(1+bT)/x² + 8Le^{bT}x`.

The two terms compete: shortening the probe amplifies the observational noise `η`, lengthening it
admits more of the background's own motion. A static background is `L = 0`, where the second term
vanishes and statement 168 is recovered.

### The optimal integration time, and the cube-root law

That the estimate has a genuine optimum, rather than improving without limit as the probe shortens,
is statements 175–177 — and the optimum is elementary. Writing the bound as `A/x² + Bx`, the balance
point `Bx³ = 2A` makes the noise term exactly half the drift term, so the total is `(3/2)Bx`; and for
every other probing time the total is larger, by the identity

`(A/y² + By) − (A/x² + Bx) = A(x−y)²(x+2y)/(x³y²)`,

which is manifestly non-negative (**`inv_sq_add_linear_le_of_balance`**). No inequality of means is
needed — the difference is a square times a positive factor.

The balance point is `x = (2A/B)^{1/3}` (**`balance_probe_eq`**), so both the optimal probe and the
optimal error scale like the **cube root** of the observational noise: halving the noise buys a factor
`2^{1/3} ≈ 1.26` in the reconstruction, not a factor two. That is the sharp form of the statement that
such a measurement has an integration time — a real parameter of the experiment, not an artefact of
the proof (**`norm_sub_zero_le_optimal`**, **`kgProbe_bound_optimal`**).

### The estimate the card is named after, sharp

The card opens with the energy method for pointwise solutions with compact spatial support.
Statements 178–182 close it in the register the rest of the corpus works in, and with the constants
the classical argument gives:

**`kgFieldEnergy_le`**: `‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖² ≤ (‖⟨D⟩u(0)‖² + ‖∂ₜu(0)‖²)·e^{2‖W‖|t|}`

for the mild `L²` solution of `∂ₜ²u = -⟨D⟩²u + Wu`, with `W` an **arbitrary bounded operator** and no
regularity or smoothing hypothesis anywhere. The constant is **one** and the rate is exactly `‖W‖`;
both are sharp, since the free evolution conserves the energy exactly (statement 58).

The proof is the energy method read through the propagator rather than through an integration by
parts — which is what makes it survive the total absence of regularity. The gradient and the velocity
are available in closed form from the two Duhamel formulas (statements 96 and 97),

`⟨D⟩u(t) = cos(t⟨D⟩)g + sin(t⟨D⟩)h + ∫₀ᵗ sin((t−s)⟨D⟩)Wu(s)ds`,
`∂ₜu(t) = −sin(t⟨D⟩)g + cos(t⟨D⟩)h + ∫₀ᵗ cos((t−s)⟨D⟩)Wu(s)ds`,

and `kgFreqInvOp_kgFieldGrad` checks that the first really is `⟨D⟩u` by dividing it back down. The
pair they form solves a Volterra equation in the energy space whose free term is the propagator — an
**isometry**, statement 59 — and whose kernel is the propagator composed with `v ↦ (0, W⟨D⟩⁻¹v₁)`.
That kernel has norm at most `‖W‖` precisely because `⟨D⟩⁻¹` is a contraction, which is the operator
form of the classical step `‖u‖ ≤ ‖⟨D⟩u‖`. The Volterra layer's own exponential bound is then already
the sharp estimate, and the remaining work is uniqueness: the closed-form pair and the Volterra
solution satisfy the same equation, so they agree (**`kgFieldState_eq_kgStateMild`**).

Statements 183–186 say the estimate is sharp and that it survives a moving background. Sharpness is
the degenerate case: with `W = 0` the Duhamel term is absent and the state is literally the propagator
applied to the datum, so the estimate is an **equality** (**`kgFieldEnergy_zero_op`**) — the free field
conserves `‖⟨D⟩u‖² + ‖∂ₜu‖²` exactly, and the exponential factor is the only room there is. As for the
moving background, the argument never used the autonomy of the perturbation: replacing `W` by a
uniformly bounded, strongly continuous curve changes the Volterra kernel from `v ↦ (0, W⟨D⟩⁻¹v₁)` to
`v ↦ (0, W(s)⟨D⟩⁻¹v₁)`, whose norm obeys the same uniform bound, and nothing else moves
(**`kgFieldEnergyT_le`**). A clock in a time-varying background obeys the same sharp estimate.

### Exact conservation, for a real potential

The exponential estimate is what a general bounded perturbation allows. A *real* potential allows
much more, and statements 187–189 prove it: when `W` is self-adjoint the total energy

`E(t) = ‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖² − re⟪W u(t), u(t)⟫`

is **exactly conserved** (**`kgFieldEnergy_conserved`**), for the mild solution, with no regularity
beyond the one power of `⟨D⟩⁻¹` on the position datum that the velocity already needs, and with no
smallness anywhere.

The obstacle in the mild theory is that the classical computation differentiates
`‖⟨D⟩u‖² + ‖∂ₜu‖²` term by term, and each term's derivative involves the unbounded generator —
`d/dt(⟨D⟩u) = ⟨D⟩∂ₜu` and `d/dt(∂ₜu) = −⟨D⟩²u + Wu` — so only their *sum* is finite, and neither
half exists on its own. The way around it is to carry the state back to time zero by the free
evolution. The reduced state

`Z(t) = S(−t)V(t) = V(0) + ∫₀ᵗ S(−s)(0, Wu(s)) ds`

is differentiable by the fundamental theorem of calculus alone (**`hasDerivAt_kgReducedState`**) — the
generator has been absorbed into the propagator, which is not differentiated. The identity itself
(**`kgReducedState_eq`**) is the Duhamel formula composed with the group law `S(−t)S(t−s) = S(−s)`.

The rest is transport. `S(−t)` is not merely an isometry but **unitary** (**`inner_kgPropagator`**,
from `norm_kgPropagator_apply` through `LinearIsometry.inner_map_map`), so `‖V(t)‖ = ‖Z(t)‖` and the
inner products carry across unchanged. Differentiating the squared norm gives
`re(⟪∂ₜu, Wu⟫ + ⟪Wu, ∂ₜu⟫)`, differentiating the potential term gives `re(⟪Wu, ∂ₜu⟫ + ⟪W∂ₜu, u⟫)`, and
self-adjointness identifies `⟪W∂ₜu, u⟫` with `⟪∂ₜu, Wu⟫`. The two cancel.

Statements 190–192 read off what conservation buys. The ill-posedness witness of 155–159 shows that
for a general `W` the exponential of the estimate is real; for a self-adjoint `W` it disappears
entirely, because conservation turns the differential inequality into an algebraic one. The mechanism
is `‖u‖ ≤ ‖⟨D⟩u‖` — the operator form of the mass gap, the frequency being bounded below by one —
which controls the potential term by the very quantity it is subtracted from
(**`norm_kgFieldMild_sq_le_energy`**). If the potential is small, `‖W‖ = b < 1`,

**`kgFieldEnergy_uniform`**: `‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖² ≤ (1+b)/(1−b)·(‖⟨D⟩u(0)‖² + ‖∂ₜu(0)‖²)`

for **every** time — no growth at all, only a fixed loss. If instead the potential is confining,
`re⟪Wx,x⟫ ≤ 0`, no smallness is needed at all: the potential term has the right sign and the energy
never exceeds its initial value (**`kgFieldEnergy_le_of_nonpos`**), which also keeps the field itself
bounded for all time. A clock in a real background therefore does not run away; a clock in a general
complex one can.

Statements 193–196 exhibit the class the self-adjointness hypothesis was written for, so that none of
this is vacuous: **multiplication by a bounded real function of position**. Such an operator is
self-adjoint for exactly the reason the classical energy method works — the potential is real, so the
cross terms conjugate into each other (**`inner_kgMulOp`**, from statement 58). Everything specialises:
the energy `‖⟨D⟩u‖² + ‖∂ₜu‖² − ∫V|u|²` is exactly conserved, a potential of sup-norm below one gives an
energy bounded uniformly in time, and the potential term is literally the integral
`∫ V(a)|u(a)|² da` (**`re_inner_kgMulOp`**). For an **attractive** potential, `V ≤ 0`, that integral is
non-positive, so no smallness is needed at all and the field itself stays bounded forever
(**`kgRealPotential_norm_le_of_nonpos`**) — a clock sitting in a potential well does not run away.

### The adiabatic estimate

A fixed real potential conserves the energy exactly. A **moving** real background does work on the
field, and statements 197–201 identify the rate: it is exactly the rate at which the background
itself moves.

The reduced-state device of 187–188 never used the autonomy of the perturbation, so it transfers
(**`kgReducedStateT_eq`**, **`hasDerivAt_kgReducedStateT`**), and gives the differentiated identity
`d/dt‖state‖² = 2 re⟪W(t)u, ∂ₜu⟫` for any uniformly bounded, strongly continuous curve of
perturbations. Differentiating the potential term as well — the product rule for `t ↦ W(t)u(t)` is
`HasDerivAt.clm_apply`, after restricting scalars so that the operator curve is differentiated over
the same field as the time variable — and cancelling by self-adjointness leaves the **work–energy
identity**

**`hasDerivAt_kgAdiabaticEnergy`**: `d/dt (‖⟨D⟩u‖² + ‖∂ₜu‖² − re⟪W(t)u, u⟫) = −re⟪Ẇ(t)u, u⟫`.

The right-hand side is bounded by `‖Ẇ(t)‖·‖u‖²`; the mass gap bounds `‖u‖²` by the state, and for
`‖W‖ ≤ b < 1` the state is in turn bounded by the energy itself (**`kgAdiabaticEnergy_lower`**). So

`|E'| ≤ (L/(1−b))·E`,  hence  **`kgAdiabaticEnergy_le`**: `E(t) ≤ E(0)·e^{L|t|/(1−b)}`

with `L` any bound for `‖Ẇ‖`. This is the adiabatic principle in quantitative form: a background that
changes slowly heats the field slowly, at a rate proportional to its own rate of change and to nothing
else. A static background is `L = 0`, where the bound degenerates to the exact conservation of 189.

No Grönwall inequality is used: `E(t)e^{∓Kt}` is monotone because its derivative has a sign, which is
both shorter and two-sided in the time.

Statements 202–204 sharpen it and make it concrete. The work–energy identity is a derivative, so
integrating it gives the exact accounting

**`kgAdiabaticEnergy_sub`**: `E(t) − E(0) = −∫₀ᵗ re⟪Ẇ(s)u(s), u(s)⟫ ds`

— the energy the field gains is literally the work the background does on it, with no inequality
anywhere; the exponential bound is what one gets by discarding the sign of the integrand. Feeding in
the a-priori bound on `‖u‖` turns it into the explicit
`|E(t) − E(0)| ≤ L(‖g‖+‖h‖)²e^{2b|t|}|t|`.

For the hypotheses not to be vacuous, 203–204 exhibit the canonical instance: a fixed self-adjoint
perturbation switched on and off by a scalar profile, `W(t) = φ(t)·W₀`. Its norm derivative is
`φ̇(t)·W₀` (**`hasDerivAt_kgScaledPotential`**, from `HasDerivAt.smul_const` after coercing the profile
into `ℂ`), it is self-adjoint because the profile is real, and the hypotheses of the adiabatic
estimate reduce to bounds on `φ` and `φ̇`. That is the situation a clock in a background of varying
strength actually sits in.

Statements 205–208 remove the last abstraction by composing the two concrete constructions: the fixed
self-adjoint perturbation of 193 (multiplication by a real `V`) switched by the profile of 203. What
is left is

`∂ₜ²u = -⟨D⟩²u + φ(t)V(x)u`

with no abstract hypothesis anywhere. Its work density is the switching rate times the potential
energy of the field, `φ̇(t)·∫V|u|²` (**`re_inner_kgSwitchedPotential`**); the exact accounting
(**`kgSwitchedPotential_work`**) and the adiabatic estimate (**`kgSwitchedPotential_energy_le`**) hold
with every constant read off from three quantities an experiment can bound: `sup|φ|`, `sup|φ̇|` and
`sup|V|`.

### Where the two threads meet

The conditional stability estimate (168, 170) is stated for perturbations that only couple frequencies
below a fixed cut-off, `A = P_R A P_R`. Multiplication by a function of position is never of that
form, so as it stood the inverse-problem thread and the concrete real potentials of the energy thread
had no common ground: each was proved about a class the other could not reach.

Statements 209–212 supply the intersection. The low-pass symbol is an indicator, so the projection is
**idempotent** and **self-adjoint** (209) — both by the same one-line case split on the symbol.
Compressing any bounded operator to the band,

`A ↦ P_R A P_R` (**`kgBandOp`**),

therefore produces an operator that satisfies the hypotheses of the conditional estimate on both
sides (**`kgBandOp_lowPass_dom`**, **`kgBandOp_lowPass_ran`**, from idempotence) and that is
self-adjoint whenever the operator is (**`inner_kgBandOp`**, from the projection being self-adjoint).
So on each frequency band the *same* class of perturbations carries both halves of the theory:

* **`norm_kgBandOp_sub_le`** — the inverse problem is well posed on it, with the explicit constant of
  statement 170;
* **`kgBandOp_real_energy_conserved`** — and if the operator compressed is a real potential, the
  evolution it generates conserves the energy exactly.

Physically the band compression is the part of a potential that a field of bounded frequency can
actually feel, which is the only part any finite-bandwidth measurement could hope to recover — so the
restriction is the one the physics imposes anyway, not an artefact of the proof.

Statements 213–216 close the circle by showing the bands **exhaust** the potential, so that the
band-restricted theory is a theory of the potential rather than of a proxy. The indicator symbols
converge pointwise to one — each frequency is eventually below the cut-off — so the corpus's own
strong-convergence criterion for Fourier multipliers (statement 48) gives
`P_R x → x` (**`tendsto_kgLowPassOp_apply`**), and two applications with a triangle inequality move
the limit past the perturbation:

**`tendsto_kgBandOp_apply`**: `P_R W P_R x → W x` as `R → ∞`.

Hence **`eq_of_kgBandOp_eq`**: two perturbations with the same compression on every band are equal.
Together with 211 this is the complete statement of what the observations determine: on each band,
quantitatively and with an explicit constant; across all bands, exactly.

Statements 217–220 record what the band buys dynamically. The projection commutes with the
propagators for the trivial reason that everything in sight is a Fourier multiplier, so it passes
through the free field; and it passes through the *perturbed* evolution exactly when the perturbation
neither reads nor writes outside the band — which is what the band compression arranges. Uniqueness
then gives the invariance:

**`kgBandOp_lowPass_invariant`**: band-limited data evolve into band-limited states.

On such a state the frequency is bounded, and statement 220 makes that precise: the multiplier
`⟨D⟩²P_R` has norm at most `1 + R²`, and dividing it twice by the frequency returns the projection
(**`kgFreqInvOp_sq_kgFreqSqLowOp`**). So on a band `⟨D⟩²` is realised by a genuinely bounded operator,
and the obstruction that forced the smoothing hypothesis of statements 103–109 — `⟨D⟩sin(τ⟨D⟩)` being
unbounded — is simply absent.

Statements 221–224 make that usable by recording the symbol calculus of `⟨D⟩_R`, the frequency cut to
the band. All of them are instances of one fact — composing two Fourier multipliers multiplies their
symbols — applied to products where the factor `⟨ξ⟩` cancels against `⟨ξ⟩⁻¹` or is absorbed by the
indicator. Two of them do the real work:

* **`kgFreqInvOp_kgFreqLowOp`**: `⟨D⟩⁻¹⟨D⟩_R = P_R`. Every band-limited vector is `⟨D⟩⁻¹` of
  something, so the regularity hypothesis of the differentiated theory (statements 87–88, 96–97) is
  **automatic** on a band — one no longer has to prescribe the datum in the form `⟨D⟩⁻¹g`.
* **`kgSinOp_kgLowPassOp`**: `sin(t⟨D⟩)P_R = (sin(t⟨D⟩)/⟨D⟩)⟨D⟩_R`. The propagator whose
  differentiation was blocked is, on a band, the differentiable one composed with a bounded operator.

Together with the commutation identities of 224 these are exactly the inputs a strong solution on a
band requires, and statements 225–226 assemble it:

**`hasDerivAt_kgFieldVel_band`**: for band-limited data and a band-compressed perturbation the mild
solution is twice differentiable and `∂ₜ²u = −⟨D⟩²_R u + Wu` as an identity in `L²`,

with **no smoothing hypothesis** — the perturbation is any bounded operator, compressed to the band.
This closes the gap left by statements 103–109, where the strong theory had to assume `W = ⟨D⟩⁻¹W₀`
because differentiating the velocity a second time produced the unbounded `⟨D⟩sin(τ⟨D⟩)`. On a band
that term never appears: the sine propagator factors as `(sin(t⟨D⟩)/⟨D⟩)⟨D⟩_R`, whose first factor is
differentiable on every vector and whose second is bounded.

Every analytic input was already in the corpus — the two propagator derivatives of statement 65, the
Duhamel second derivative of statement 102 — each stated for `⟨D⟩⁻¹`-regular arguments, which
statement 222 now supplies for free. What 225 adds is the bookkeeping that makes them fit: pushing
`⟨D⟩²_R` through the Duhamel formula gives
`⟨D⟩²_R u(t) = cos(t⟨D⟩)⟨D⟩²_R x + sin(t⟨D⟩)⟨D⟩_R y + ∫₀ᵗ sin((t−s)⟨D⟩)⟨D⟩_R Wu(s) ds`,
which is exactly the negative of the three derivative terms.

Statements 227–229 connect that back to the corpus's own strong theory. Dividing
`∂ₜ²u = −⟨D⟩²_R u + Wu` twice by the frequency gives `⟨D⟩⁻²∂ₜ²u = −u + ⟨D⟩⁻²Wu`, because `⟨D⟩⁻²⟨D⟩²_R`
is the band projection (220) and the solution lives on the band (219). That is exactly the predicate
`SolvesKGSource` of statement 74, so the uniqueness theorem proved there — by the energy method, and
never needing the smoothing hypothesis itself — applies verbatim. What had been missing was not
uniqueness but **existence**: the strong theory could only produce solutions for a smoothing
perturbation. So

**`exists_unique_solvesKGSource_band`**: for band-limited data and any bounded perturbation compressed
to the band there is a strong solution with those data, and it is the only one.

The strong Cauchy problem, which the card could previously solve only under the smoothing hypothesis
of 103–109, is therefore well posed on every frequency band with no hypothesis on the perturbation
beyond boundedness.

Statements 230–232 make the conserved energy concrete. The energy thread carries the gradient as an
abstract closed-form expression `kgFieldGrad`, defined so that dividing it by the frequency returns
the solution; on a band it is literally `⟨D⟩_R u` (**`kgFieldGrad_band`**), a bounded operator applied
to the state. With that identification the conservation law of statement 189, specialised to a real
potential compressed to the band, reads

**`kgBandReal_energy_conserved`**:
`‖⟨D⟩_R u(t)‖² + ‖∂ₜu(t)‖² − ∫V|u(t)|² = ‖⟨D⟩_R u(0)‖² + ‖∂ₜu(0)‖² − ∫V|u(0)|²`,

the classical conserved energy of the Klein–Gordon field in a potential, with every term a quantity of
the solution itself.

### Comparing solutions without comparing operators

The Lipschitz estimate of statement 136 measures the difference of two solutions by the **operator
norm** of the difference of the perturbations. That is the right measure when the perturbations are
close as operators, and useless when they are not — and they often are not. The band compressions of
statement 215 converge to the potential *strongly* but not in norm, so 136 says nothing about whether
the band solutions converge to the true one.

Statements 233–234 replace the operator norm by what the perturbations actually do:

**`norm_kgFieldMild_sub_general_le`**:
`‖u₁(t) − u₂(t)‖ ≤ (‖f₁−f₂‖ + ‖h₁−h₂‖ + ∫₀ᵗ‖(W₁−W₂)u₂(s)‖ds)·e^{bt}`,

allowing the data to differ as well. The mechanism is the same splitting as in 135, taken the other
way: `W₁u₁ − W₂u₂ = (W₁−W₂)u₂ + W₁(u₁−u₂)` puts the whole discrepancy into a source evaluated along a
**known** curve — the second solution — so what is left for Grönwall is a genuine memory term. Statement
136 is the special case where the source is estimated by `‖W₁−W₂‖‖u₂‖`; the point of the sharper form
is that it survives strong convergence, where the operator-norm bound is vacuous.

Statements 235–236 collect the return. The band theory is a complete theory, but of the *compressed*
equation `∂ₜ²u = −⟨D⟩²u + P_RWP_R u` with band-limited data; what makes it a theory of the original
equation is that it converges to it. Along the true solution the discrepancy
`(P_RWP_R − W)u(s)` tends to zero pointwise by statement 215 and is dominated by `2‖W‖‖u(s)‖`, so
dominated convergence kills the accumulated term; the data converge by statement 214; and 234 turns
both into

**`tendsto_kgFieldMild_band`**: `u_R(t) → u(t)` as `R → ∞`, for every time.

So everything the band carries — strong solutions with no smoothing hypothesis (226), well-posedness
(229), the classical conserved energy (232), and a well-posed inverse problem (211) — is a faithful
approximation of the general equation rather than a parallel theory about a different one.

### The whole state, not only the field

A clock does not read the field alone; it reads the **state**, the field and its velocity together —
that is what statements 178–182 measure and what 129–130 propagate. So statement 236 is only half of
what "faithful" means: it says the band field converges, and says nothing about the band velocity.

Statements 237–240 close the other half. The velocity is
`∂ₜu(t) = −sin(t⟨D⟩)f + cos(t⟨D⟩)h + ∫₀ᵗcos((t−s)⟨D⟩)Wu(s)ds`; the first two terms converge because
the data do (214) and the propagators are contractions. The integrand of the third is the only real
work, and the estimate is a splitting again — this time of the *source*, not of the difference:

`W_Ru_R(s) − Wu(s) = (W_R − W)u(s) + W_R(u_R(s) − u(s))`.

The first term vanishes by the strong convergence of the compressions (215) and the second by
statement 236 itself, uniformly damped by `‖W_R‖ ≤ ‖W‖`; so the integrand converges pointwise while
staying bounded by the constant `‖W‖(‖f‖+‖h‖)e^{b|t|}` on the whole interval, and dominated
convergence gives

**`tendsto_kgFieldVel_band`**: `∂ₜu_R(t) → ∂ₜu(t)` as `R → ∞`, for every time.

The bookkeeping needs one commutation, `P_R⟨D⟩⁻¹ = ⟨D⟩⁻¹P_R` (237), because the velocity of the band
solution is stated for the band-limited *field* datum `P_R⟨D⟩⁻¹g` while the approximation theorem is
stated for `⟨D⟩⁻¹P_Rg`; the two symbols commute, so they agree. With 240 the band approximation is
faithful on the state, which is the object the clock programme actually measures.

### The energy passes to the limit, and the window is finite

Two things are still missing before the band theory can be used as a theory of the original equation.
The first is the **energy**, the quantity the whole card is about. It is the norm squared of the state
`(⟨D⟩u, ∂ₜu)`, so it converges as soon as both components do; the gradient is the velocity's own
Duhamel formula with the sine propagator in place of the cosine, and 238 already supplies the
convergence of the source, so 241–243 run the same dominated-convergence argument and give

**`tendsto_kgFieldEnergy_band`**: `‖⟨D⟩u_R(t)‖² + ‖∂ₜu_R(t)‖² → ‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖²`.

The sharp estimate of statement 182 and the exact conservation of 189 are therefore statements about
the limit as well, not only about the compressed equation.

The second is **uniformity**. A measurement occupies a window, and a limit taken at each time
separately does not by itself give one cut-off good for the whole of it. Here nothing new is needed:
the right-hand side of statement 234 is monotone in the endpoint — its accumulated term is an
integral of a norm and its exponential is increasing — so its value at `T` already majorises the
error at every `t ∈ [0,T]` (245), and that single quantity is the one shown to vanish in 235. Hence

**`tendstoUniformlyOn_kgFieldMild_band`**: `u_R → u` uniformly on `[0, T]`, for every `T`.

So for any prescribed accuracy over any finite observation window there is a cut-off beyond which the
band theory — strong solutions with no smoothing hypothesis (226), well-posedness (229), the classical
conserved energy (232), a well-posed inverse problem (211) — describes the original equation to within
that accuracy, everywhere in the window at once.

### The background moves

A clock does not sit in a static field. The moving theory of statements 144–154 solves
`∂ₜ²u = −⟨D⟩²u + W(t)u` for a curve of bounded operators that is uniformly bounded and strongly
continuous, and the band programme has so far compressed only a fixed one. Statements 247–253 carry
the whole approximation thread to the moving case.

Nothing in it used autonomy. The compression of a moving background is the compression at each time,
`W_R(t) = P_RW(t)P_R`, and it inherits both hypotheses of the moving theory from the background it
compresses (247). The splitting `W₁(s)u₁ − W₂(s)u₂ = (W₁(s)−W₂(s))u₂ + W₁(s)(u₁−u₂)` is pointwise in
the time, so it holds verbatim for curves (248) and Grönwall closes it with the same uniform bound:

**`norm_kgFieldMildT_sub_general_le`**:
`‖u₁(t) − u₂(t)‖ ≤ (‖f₁−f₂‖ + ‖h₁−h₂‖ + ∫₀ᵗ‖(W₁(s)−W₂(s))u₂(s)‖ds)·e^{bt}`.

With that in hand the rest repeats: the discrepancy `(W_R(s) − W(s))u(s)` vanishes pointwise at each
time and is dominated by `2‖W‖‖u(s)‖` on the interval (250), so

**`tendsto_kgFieldMildT_band`**: `u_R(t) → u(t)` for every time, and

**`tendstoUniformlyOn_kgFieldMildT_band`**: uniformly on every window `[0,T]`.

The negative-time half comes from the moving theory's own reflection (149), whose reflected
background `r ↦ W(−r)` commutes with the compression definitionally.

Statements 254–258 complete it on the state. The gradient and the velocity are the same Duhamel
formula with the sine and the cosine propagator, and both have the same integrand, so the work is done
once: the perturbed source converges by the splitting
`W_R(s)u_R(s) − W(s)u(s) = W_R(s)(u_R(s) − u(s)) + (W_R(s) − W(s))u(s)`, whose first term is damped by
the uniform bound and killed by 252 and whose second vanishes by 247. Dominated convergence then gives
both propagator terms and hence

**`tendsto_kgFieldEnergyT_band`**: `‖⟨D⟩u_R(t)‖² + ‖∂ₜu_R(t)‖² → ‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖²`.

The estimate of statement 186 is therefore a statement about the moving equation itself, and the whole
approximation thread — field, state, energy, uniformity — now holds in the register the clock
programme uses: a bounded field in a background that changes with time, observed over a finite window.

### The estimate belongs to the state, not to the field

One gap is left in that list: statements 243–244 converge the state and the energy *at each time*,
because they were obtained by dominated convergence on the Duhamel integrals, and that gives nothing
uniform. The field's uniformity (246) came from the Grönwall bound of 234, which the state did not
have.

Statements 259–262 give the state its own. The state solves a Volterra equation in the energy space
whose free term is an isometry applied to the datum and whose kernel is `P(t−s)∘S(W)` with
`S(W)v = (0, W⟨D⟩⁻¹v₁)`; the splitting of 233 applies there verbatim, and the source difference is the
*same* quantity as before, because `S(W₁) − S(W₂)` lands in the second component and a state with
vanishing first component has the norm of its second:

`‖(S(W₁) − S(W₂))v₂(s)‖ = ‖(W₁ − W₂)u₂(s)‖`.

So the whole state obeys the bound of 234 with the free term replaced by the energy norm of the data
difference:

**`norm_kgFieldState_sub_general_le`**:
`‖(⟨D⟩u₁, ∂ₜu₁)(t) − (⟨D⟩u₂, ∂ₜu₂)(t)‖ ≤ (‖(g₁−g₂, h₁−h₂)‖ + ∫₀ᵗ‖(W₁−W₂)u₂(s)‖ds)·e^{bt}`.

Its right-hand side is monotone in the endpoint for the same two reasons as before, and its majorant is
the one already shown to vanish, so 263–265 upgrade the pointwise limits to uniform ones: the state,
the gradient and the velocity all converge uniformly on `[0, T]`. The approximation is now uniform in
exactly the quantity the energy estimate controls.

The energy follows (266). It is the square of the energy norm of the state, and squaring is uniformly
continuous on bounded sets; both the band states and the true state are bounded on the window by the
*same* constant `(‖g‖+‖y‖)e^{bT}`, because the band data are contractions of the data, so
`|E_R(t) − E(t)| ≤ 2M‖v_R(t) − v(t)‖` on the window and the uniform convergence of the state passes
straight through.

Statements 267–272 do all of this again for a moving background. The energy-space kernel there is
`P(t−s)∘S(W(s))`, so the splitting is pointwise in the time and the source difference is the same
field difference as before; the estimate, its monotonicity in the endpoint, and the uniform band
approximation of the state, the gradient and the velocity transfer verbatim. Everything the energy
estimate controls is therefore approximated uniformly on a finite observation window, in a background
that moves — including the energy itself (273).

### Strong solutions in a moving background

The mild theory says what the solution *is*; the strong theory says it solves the equation. Statements
74–78 build the latter for one fixed perturbation, and statements 225–229 make it unconditional on a
band — no smoothing hypothesis, because the sine propagator factors through the half-order one and the
leftover frequency is the bounded `⟨D⟩_R`. Neither argument touches the perturbation's time dependence.

Statements 274–281 carry both to a moving background. The energy identity

`d/dt (‖⟨D⟩⁻¹∂ₜu‖² + ‖u‖²) = 2 Re⟨⟨D⟩⁻²∂ₜu, W(t)u⟩`

evaluates `W` at the same instant as everything else, so it holds for a curve of operators as it
stands, and Grönwall only ever uses the uniform bound; uniqueness then needs nothing beyond linearity
of each `W(t)`, since the difference of two solutions solves the same equation at every time
separately (277). On a band the mild solution is again twice differentiable with

`∂ₜ²u = −⟨D⟩²_R u + W(t)u`,

so it is a strong solution in that sense, and the uniqueness above makes it the only one:

**`exists_unique_solvesKGSourceT_band`** — the strong Cauchy problem in a moving background is well
posed on a band, for any uniformly bounded strongly continuous background.

With 253 and 271–273 this closes the moving register: existence, uniqueness, the sharp energy
estimate, and a band approximation that is faithful and uniform on every finite observation window.

### What the clock reads: the classical work–energy balance

The adiabatic layer (199–208) proves the work–energy identity for an abstract self-adjoint moving
background. Statements 282–288 make every term of it a quantity of the field, in the register the
clock programme uses.

Band compression is linear in the operator, so compressing `φ(t)V` gives the switched compression
`φ(t)·P_RVP_R` (282) — every statement of the adiabatic layer becomes a statement about a band by
changing the fixed operator alone, and the compressed operator is still self-adjoint and still
norm-differentiable in `t`. On a band the abstract gradient is `⟨D⟩_R u`, in a moving background as in
a static one (283), and the potential term is an honest integral, because `P_Ru = u` along the
solution (285). The identity of statement 202 therefore reads

**`kgBandSwitched_work`**:
`[‖⟨D⟩_R u(t)‖² + ‖∂ₜu(t)‖² − φ(t)∫V|u(t)|²] − [same at 0] = −∫₀ᵗ φ'(s)∫V|u(s)|² ds`,

the classical work–energy balance of a Klein–Gordon field in a potential of varying strength: the
energy changes exactly by the work the switching does. The accompanying estimate (288) bounds the
growth by `e^{L|t|/(1−b)}` with `L` the switching rate and `b` the potential's strength, so a slowly
switched potential moves the energy slowly — the adiabatic statement the clock programme needs, with
nothing abstract left in it.

Statements 289–292 make that balance a statement about the original equation and not only about the
compressed one: both of its sides converge as the cut-off grows. The mechanism is one lemma — a
uniformly bounded, strongly continuous family has compressions that act correctly along *any*
convergent curve of states, `W_R(s)z_R → W(s)z` (289) — applied twice: to the solution, for the
potential term, and to the derivative family, for the work density. The state converges by 258 and the
work density is bounded by `L((‖f‖+‖h‖)e^{b|t|})²` on the interval, so dominated convergence gives

**`tendsto_kgAdiabaticEnergy_band`** and **`tendsto_integral_work_band`**.

The band accounting is therefore an approximation of the true one, term by term.

### A periodically driven clock

The evolution family of statement 152 restarts the solution from its own state, at the price of
shifting the background. When the background is periodic the shift changes nothing — so the evolution
over one period is the *same* map at every period.

Making that precise needs the restart at the level of the state, not only of the field, and that is
statements 293–296. The velocity restarts by differentiating the field restart in time. The gradient
restarts because `⟨D⟩⁻¹` is injective and `⟨D⟩⁻¹⟨D⟩u = u` identifies it with the field; the missing
half of the symbol calculus of 222, `⟨D⟩_R⟨D⟩⁻¹ = P_R` (293), is recorded alongside. Together they say
the non-autonomous evolution is an **evolution family on the energy space**, not only on the field.

For a `T`-periodic background this gives the **period map** `v ↦ (⟨D⟩u(T), ∂ₜu(T))` (297) and

**`kgFieldStateT_iterate`**: the state after `n` periods is its `n`-th iterate,

whence **`norm_kgFieldStateT_period_le`**: `‖v(nT)‖ ≤ ‖v(0)‖·e^{nb|T|}`. The growth of a
periodically driven clock is carried by one operator rather than by the whole history — the Floquet
form of the estimate the card is about.

Statements 301–305 make that operator a genuine one. The state solves a Volterra equation in the
energy space whose free term is linear in the datum and whose kernel is linear in the state, so
superposing two solutions solves the superposed equation and uniqueness identifies it with the
solution of the superposed datum (302). The period map is therefore linear and bounded — the
**monodromy operator** `M`, with `‖M‖ ≤ e^{b|T|}` — and

**`kgFieldStateT_monodromy_pow`**: `v(nT) = Mⁿ v(0)`.

The long-time behaviour of a periodically driven clock is the behaviour of the powers of a single
bounded operator, and any bound on those powers is a bound on the clock (305), with no exponential
growth of its own.

Statements 306–310 close the question the operator poses. A periodic background is periodic in both
directions, so running one period backwards is the evolution of the same equation over `-T` and undoes
it: the monodromy is a **linear homeomorphism**, with both norms bounded by `e^{b|T|}` (307). And the
long-time behaviour is decided by its powers in both directions:

* bounded powers give boundedness at *every* time, not only at multiples of the period — the leftover
  piece of time is shorter than one period and costs one factor `e^{bT}` (308);
* conversely, bounded orbits give bounded powers, by the uniform boundedness principle on the energy
  space, which is complete (309).

**`kgFloquet_stable_iff`**: the state stays bounded at every time for every datum **iff**
`sup_n‖Mⁿ‖ < ∞`. A periodically driven clock is stable exactly when its monodromy has bounded powers —
the question of whether such a clock keeps time is reduced to a spectral question about one operator.

Statements 311–315 settle the two extreme cases from the crudest datum available, the norm of `M`
itself. Along the periods the state is contracted by `‖M‖` each time (311), and between periods the
leftover time is shorter than one period and costs at most `e^{bT}` (312). Hence

* **`norm_kgFieldStateT_le_of_norm_monodromy_le_one`**: if `‖M‖ ≤ 1`, then
  `‖v(t)‖ ≤ ‖v(0)‖e^{bT}` for every `t ≥ 0` — the clock keeps running, with a constant read off from
  one period;
* **`tendsto_kgFieldStateT_zero`**: if `‖M‖ < 1`, then `v(t) → 0` as `t → ∞` — the driving damps the
  clock out, at every time and not only along the periods.

The second uses that `⌊t/T⌋ → ∞`, so the geometric decay along the periods survives the leftover
piece.

### The stable class is inhabited

A criterion decides nothing until something satisfies it. A constant background is periodic with
every period, so the autonomous theory of statements 187–196 supplies the first inhabitants —
with explicit constants, not merely existence.

For the free field the monodromy is an **isometry**: the propagator conserves the energy exactly, so
`‖M‖ ≤ 1` and statement 313 applies verbatim (317). For a self-adjoint potential of strength `b < 1`
the exactly conserved energy of 189 differs from the state norm by the fixed factor of 191, so

**`norm_kgMonodromy_pow_le_of_small`**: `‖Mⁿ‖ ≤ √((1+b)/(1−b))` for every `n`,

uniformly — the criterion of statement 310 is met with a constant read off from the potential's
strength alone, and the class of stable periodically driven clocks is not empty.

### Deciding stability on a band

The criterion is about the powers of the monodromy of the original equation, which is not an object
one computes with. The band models are: there the Cauchy problem is a genuine strong problem (281),
the frequency is bounded, and everything is a bounded operator with a cut-off.

The band compression of a periodic background is periodic (320), so it carries a monodromy `M_R` of
its own. Applying the state estimate of 269 with the *same* datum for both backgrounds bounds
`‖M_R v − M v‖` by the accumulated discrepancy over one period, which vanishes by 250 — so `M_R → M`
strongly (322). The `M_R` are bounded uniformly by `e^{b|T|}`, so the splitting
`M_R^{n+1}v − M^{n+1}v = M_R(M_R^n v − M^n v) + (M_R − M)(M^n v)` propagates this to every power (323).
Hence

**`norm_kgMonodromy_pow_le_of_band_bound`**: a bound on the powers of the band monodromies, uniform in
the cut-off, is a bound on the powers of the true monodromy.

Whether a periodically driven clock keeps time may therefore be decided on the band models, and the
answer transfers.

### The Floquet multipliers

The spectrum of the monodromy is the set of **Floquet multipliers**. Everything the criterion says
about it follows from one inequality, `‖k‖ⁿ = ‖kⁿ‖ ≤ ‖Mⁿ‖‖1‖`, valid because `kⁿ` is a spectral value
of `Mⁿ`:

* every multiplier lies in the disc `|k| ≤ e^{b|T|}` cut out by the energy estimate over one
  period (325);
* if the powers are bounded — that is, if the clock is stable — every multiplier lies in the **closed
  unit disc** (326), since `‖k‖ⁿ ≤ C` for every `n`.

Contrapositively, and this is the classical instability statement:

**`exists_unbounded_of_one_lt_norm_spectrum`** — one multiplier of modulus greater than one produces a
Cauchy datum whose state is unbounded in time.

So a single point of the spectrum outside the unit circle breaks the clock, and the whole long-time
question sits inside the unit circle, where it belongs.

### Decay from the spectral radius

Statement 315 damps the clock out when the monodromy is a contraction, `‖M‖ < 1`. That is not the
sharp condition: a clock can have `‖M‖ > 1` and still decay, because the norm sees one period while
the fate of the clock is decided by many.

The sharp condition is on the spectral radius, and Gelfand's formula reaches it. mathlib has the
formula but not the consequence, so statement 329 proves it for an arbitrary complex Banach algebra:
`‖aⁿ‖^{1/n} → spectralRadius a`, so a spectral radius below one puts `‖aⁿ‖ ≤ qⁿ` eventually for some
`q < 1`, hence **`tendsto_norm_pow_zero_of_spectralRadius_lt_one`**: `‖aⁿ‖ → 0`. Applied to the
monodromy and combined with the leftover-period estimate of 312, this gives

**`tendsto_kgFieldStateT_zero_of_spectralRadius`** — if every Floquet multiplier lies in the *open*
unit disc, the state tends to zero at every time.

With 326 and 328 the picture is the classical one: multipliers strictly inside the unit disc mean
decay, a multiplier strictly outside means an unbounded solution, and stability forces all of them
into the closed disc.

Statements 332–335 collect that at the level of the radius. The passage between the radius and its
multipliers is the contrapositive in both directions — the radius is the supremum of the moduli, so it
is at most one exactly when all of them are, and exceeds one only if one of them does — and the result
is

**`kgFloquet_trichotomy`**:

* `spectralRadius M < 1` → every solution decays to zero;
* `spectralRadius M > 1` → some solution is unbounded in time;
* the clock is stable only if `spectralRadius M ≤ 1`.

That is the classical Floquet statement, unconditional, for the `L²` Klein–Gordon field in a
uniformly bounded strongly continuous periodic background.

### The verdict survives an inexactly known background

A criterion about one operator built from one background is only useful if the operator does not jump
when the background is perturbed. It does not. Applying the state estimate of 269 with the same datum
for both backgrounds, and bounding the accumulated discrepancy by a uniform operator-norm distance
`δ = sup_s‖W₁(s) − W₂(s)‖`, gives

**`norm_kgMonodromy_sub_le`**: `‖M_{W₁} − M_{W₂}‖ ≤ 2Tδe^{2bT}`,

the monodromy is Lipschitz in the background. Hence the decaying regime is **open**: a clock whose
monodromy is a strict contraction stays one under every perturbation with
`δ < (1 − ‖M‖)/(2Te^{2bT})`, and by 315 it still damps out (339). The Floquet verdict therefore
survives an inexactly known background, which is the only kind a measurement provides.

### The multipliers exist, and the free clock is on the boundary

Everything said about Floquet multipliers is empty until the spectrum is known to be inhabited, and
that needs the energy space to be nontrivial. It is: the indicator of the unit ball is a nonzero
element of `L²` — the corpus already built it, for the non-surjectivity of `⟨D⟩⁻¹` (114–116) — so the
energy space and the algebra of operators on it are nontrivial (340), and every element of a
nontrivial complex Banach algebra has nonempty spectrum. Hence

**`spectrum_kgMonodromy_nonempty`**: every monodromy has at least one Floquet multiplier,

and the spectral radius is attained by one of them (342). The multiplier language of 325–335 is
therefore about something.

Nontriviality also locates the free clock exactly. Its monodromy is an isometry, so every power is one
and has norm exactly one (343) — the lower bound is where nontriviality enters — and Gelfand's formula
turns that into

**`spectralRadius_kgMonodromy_zero`**: `spectralRadius M₀ = 1`.

The free field sits precisely on the boundary of the trichotomy: neither branch of 335's first two
clauses applies to it. It is stable — its energy is exactly conserved — but it does not decay, which
is what a clock that keeps time must look like.

Statements 345–347 sharpen that from the radius to the multipliers themselves. The free evolution is
reversible with an inverse of the same size — running one period backwards is the evolution over `-T`,
also an isometry — so the free monodromy is a unit (345), and for `|k| < 1` the factorisation

`k·1 − M₀ = −M₀(1 − kM₀⁻¹)`

exhibits `k·1 − M₀` as a unit, the second factor by the Neumann series since `‖kM₀⁻¹‖ = |k| < 1`.
So no multiplier lies inside the disc (346), and with 326 every one lies on its boundary:

**`norm_eq_one_of_mem_spectrum_kgMonodromy_zero`**: `|k| = 1` for every free Floquet multiplier.

The free clock oscillates and neither grows nor decays — the spectral form of the exact conservation
of its energy.

### Purely oscillatory clocks

The free argument used that the evolution and its inverse are *isometries*. Statements 348–349 show
the conclusion needs much less — **two-sided power boundedness**. If `a` is invertible and the powers
of `a` and of `a⁻¹` are separately bounded, then `‖k‖ ≤ 1` from the first bound and `‖k⁻¹‖ ≤ 1` from
the second, because the spectrum of an inverse is the inverse of the spectrum; so the whole spectrum
sits on the unit circle.

That applies to a clock in a weak static real potential. Its monodromies over `T` and over `−T` are
inverse to each other (350) and statement 319 bounds the powers of both by `√((1+b)/(1−b))`. Hence

**`norm_eq_one_of_mem_spectrum_of_small_potential`**: every Floquet multiplier of such a clock has
modulus one.

A clock in a weak static potential is therefore *purely oscillatory*: no secular growth, no decay —
which is what an instrument that keeps time must do, and what the exactly conserved energy of 194
predicts.

### Time reflection, at the level of the state

The moving theory reflects time on the *field* (149): running `W` backwards from `(f, h)` is running
`W(−·)` forwards from `(f, −h)`. Everything since is stated for the state, and the estimates that
carry it — 269 and its consequences — are proved forwards in time only. Statements 352–355 lift the
reflection to the state, so every forward statement acquires a backward counterpart.

It lifts through the **velocity flip** `(g, h) ↦ (g, −h)`, an isometric involution of the energy space
(352). The gradient is unchanged (353), because `⟨D⟩⁻¹` is injective and the two fields agree by 149;
the velocity changes sign (354), because it is the derivative of a curve composed with `s ↦ −s`.
Hence

**`kgFieldStateT_neg`**: `(⟨D⟩u, ∂ₜu)(−t)` is the flip of the state of the reflected background at
`+t`,

and in particular the energy at `−t` for `W` equals the energy at `+t` for `W(−·)` — the estimate is
symmetric in time, as the equation is.

### Oscillation on a band

The transfer of statement 324 runs forwards only, because the state estimate it rests on is proved for
`t ≥ 0`; the oscillatory criterion of 349 needs both directions. The reflection supplies the other one
in a sharp form (356):

`M_W(−T) = F ∘ M_{W(−·)}(T) ∘ F`,   `F` the velocity flip,

an identity of operators, since `F` is an involution. Conjugation by an isometry does not change the
norm of a power (357), so the forward transfer applied to the reflected background bounds the backward
powers (358), and statement 349 closes it:

**`norm_eq_one_of_mem_spectrum_of_band_bounds`** — if the band monodromies of the background *and of
its reflection* have powers bounded uniformly in the cut-off, every Floquet multiplier of the clock
lies on the unit circle.

So oscillation, like stability, is decidable on the band models, where the Cauchy problem is a genuine
strong problem.

### Reversing time inverts the multipliers

The flip conjugation of 356 has a spectral reading. The flip is an involution, hence a unit of the
operator algebra (360), and conjugation by a unit does not move the spectrum, so

`σ(M_W(−T)) = σ(M_{W(−·)}(T))`   (362).

For a periodic background the backward monodromy is the *inverse* of the forward one, and the spectrum
of an inverse is the inverse of the spectrum. Putting the two together:

**`spectrum_kgMonodromy_reflected`**: `σ(M_{W(−·)}(T)) = σ(M_W(T))⁻¹`.

Reversing time inverts the Floquet multipliers (363–364): a mode that grows by a factor `k` per period
in one direction of time decays by exactly that factor in the other. That is the spectral form of the
reversibility of the equation, and it explains why the marginal case — all multipliers on the unit
circle — is the only one a clock can be in if it is to keep time in both directions.

### The two-way clock

That last remark is now a theorem. The criterion of 310 decides stability forwards in time and the
trichotomy of 335 leaves three possibilities; an instrument that measures time must survive both
directions of it, and that single extra demand removes two of the three.

Stability forwards puts every multiplier in the closed unit disc (326). Stability of the *reflected*
background — which is periodic with the same period (365) — bounds the backward powers through the
flip conjugation (357), so `|k|⁻¹ ≤ 1` as well. Hence

**`norm_eq_one_of_mem_spectrum_of_two_way_stable`**: every multiplier of a two-way stable clock lies
on the unit circle,

and since the spectrum is nonempty (341), **`spectralRadius_eq_one_of_two_way_stable`**: its spectral
radius is exactly one. Neither the decaying branch nor the unbounded branch of the trichotomy is
available to an instrument that keeps time in both directions — it can only oscillate.

### Reading a moving background at every instant

The conditional stability of statement 174 reads the background off the short-time field, but at the
*initial* instant only. A background that moves is not determined by one instant, and the evolution
family of 152 says what to do: restart the experiment at time `s`, which is solving the equation of
the shifted background `W(· + s)` from time zero.

Every hypothesis of 174 transfers to the shifted pair — a *uniform* Lipschitz bound on the difference
gives the shifted one with the same constant, the band conditions are imposed at every instant, and
the observation hypothesis is the natural one: the experimenter may prepare data at any instant and
watch for a time `T`. So the conclusion holds at every instant, with no loss:

**`norm_sub_le_of_lowPassT_everywhere`**: `‖W₁(s) − W₂(s)‖ ≤ 8η(1+bT)/x² + 8Le^{bT}x` for every `s`,

and at the balance point the cube-root law of 176 holds at every instant too (369). The whole moving
background is reconstructed, with a modulus of continuity that does not degrade with time.

Letting the noise vanish closes the thread. The bound has two error sources — the observational noise
divided by the square of the probing time, and the drift multiplied by it — and with exact
observations the first vanishes for *every* admissible probe while the second can be made as small as
one likes by probing briefly: every sufficiently short probe satisfies `0 < x ≤ T` and
`x²((1+R²)/2 + be^{bT}) ≤ 1/8` (370). So the bound collapses and

**`eq_of_exact_observation_everywhere`**: a band-limited moving background is determined *exactly* by
exact observations of the short-time field, at every instant.

That is the quantitative route to the injectivity of 152–154, and unlike it the argument carries a
modulus: the same computation with `η > 0` is the cube-root law of 369.

For a periodic background even that is more than one needs. Restarting at `s` and at `s + nP` is the
same experiment, because the shifted backgrounds coincide (372), and every instant is congruent modulo
the period to one in `[0, P)` through the integer part of `s/P` (373). So the observation hypothesis
need only be imposed on a single period:

**`eq_of_exact_observation_period`** — a periodic band-limited background is determined by **one
period** of short-time experiments.

That is what an experimenter with a periodically driven apparatus can actually perform, and it closes
the inverse-problem thread in the register the Floquet theory works in.

One thing is still owed: the reconstruction theorems carry two band hypotheses on the difference of
the backgrounds, and a hypothesis class decides nothing until it is inhabited. The band compressions
inhabit it — statement 210 records exactly those two identities for `P_RW₁P_R − P_RW₂P_R` — and
compression cannot spoil the Lipschitz hypothesis either, being linear in the operator and contracting
(375). Hence

**`eq_of_exact_observation_band`**: two moving backgrounds compressed to the same band and observed
exactly on short times have equal compressions.

The reconstruction theory therefore applies to the very models on which the rest of the card computes.

What that experiment recovers is the band compression `P_RWP_R`, not `W`. Statement 216 closes the
gap: the compressions determine the operator, so running the experiment at every cut-off leaves
nothing behind (378), and combining with the periodic reduction of 374 gives the sharpest form the
inverse problem takes here:

**`eq_of_exact_observation_all_bands_period`** — a periodic moving background is determined exactly by
**one period** of short-time experiments performed at **every cut-off**, with no band hypothesis on
the background itself.

That is the inverse-problem counterpart of the Floquet criterion: both reduce a question about the
original equation to a family of questions about its band models, and both transfer back.

### From the operator to the potential

All of that recovers an *operator*. The clock programme is about a *potential*, and the step between
them was missing: the corpus records that an a.e. vanishing symbol induces the zero operator but not
the converse. Statement 380 supplies it, by testing the operator on the indicator of a ball — the
vector built for the non-surjectivity of `⟨D⟩⁻¹` (114–116). Applying the operator to it multiplies the
symbol by one on the ball, so the symbol vanishes a.e. there; the balls of integer radius exhaust the
space and a countable union of null sets is null.

Hence a bounded real potential is determined by its multiplication operator (381), and combining with
378:

**`potential_ae_eq_of_exact_observation`** — a static bounded real potential is determined almost
everywhere by short-time clock observations at every cut-off.

That is the inverse problem in the register the card was written for: what is reconstructed is the
potential the clock moves in, not merely the operator that represents it.

Statements 383–384 let the potential move. The reconstruction machinery is built for moving
backgrounds; what it needs is the translation of its two analytic hypotheses into statements about the
potential. The uniform bound is immediate — a multiplication operator obeys every bound its symbol
obeys — and the Lipschitz hypothesis is the same fact applied to the four-term combination
`(V₁(σ)−V₂(σ)) − (V₁(τ)−V₂(τ))`, which is again a multiplication operator by the additivity of the
symbol calculus (383). Strong continuity in time is a genuine hypothesis on the family — it is what
the moving theory of 144–147 assumes, and the switched potentials of 206 satisfy it. With those,

**`potentialT_ae_eq_of_exact_observation`** — a moving bounded real potential, Lipschitz in time, is
determined almost everywhere at every instant by short-time clock observations at every cut-off.

When the potential is periodic the instants may be restricted to a single period, by the reduction of
379 — provided the operator family inherits the periodicity, which it does, multiplication operators
of potentials that agree everywhere being equal (385). Hence

**`potentialT_ae_eq_of_exact_observation_period`** — a periodic moving real potential, Lipschitz in
time, is determined almost everywhere at every instant by **one period** of short-time clock
observations at every cut-off.

That is the sharpest form the inverse problem takes here, and it is the mirror of the Floquet
criterion: both a periodically driven clock's fate and the potential driving it are decided by one
period of band-limited data.

### The observations decide the fate

That mirror is now a theorem. The monodromy depends on the background and on nothing else (387), so
the reconstruction results transfer to it directly: observationally identical clocks have the **same
Floquet spectrum** (388), hence the same spectral radius (389), hence the same verdict in the
trichotomy of statement 335 — and for a periodic clock one period of observations suffices (390).

So the data an experimenter can collect in a finite window decides not only what the background is but
whether the clock will keep time, decay, or break.

### The multipliers live in an annulus

Statement 325 confines the multipliers to the disc `|k| ≤ e^{b|T|}` that the energy estimate cuts out
over one period. The evolution is reversible and its inverse obeys the *same* bound (307), and the
spectrum of an inverse is the inverse of the spectrum, so `|k|⁻¹ ≤ e^{b|T|}` as well:

**`mem_annulus_of_mem_spectrum_kgMonodromy`** — every Floquet multiplier satisfies
`e^{−b|T|} ≤ |k| ≤ e^{b|T|}`.

The annulus closes onto the unit circle as the potential weakens or the period shortens, which is the
quantitative form of the free case (347): a clock cannot drift faster per period than its own energy
estimate allows, in either direction of time. In particular the trichotomy's two extreme branches
require a multiplier at distance at least `e^{−b|T|}` from the origin — instability and decay are both
rate-limited by the estimate the card began with.

Statements 393–395 make that a no-go. Both extreme branches need a multiplier off the unit circle, and
the annulus says what that costs: decay needs `e^{−b|T|} < 1` and instability needs `1 < e^{b|T|}`.
Either way

**`zero_lt_of_spectralRadius_lt_one`** and **`zero_lt_of_one_lt_norm_spectrum`**: `b·|T| > 0`.

**A free clock, or one whose period is instantaneous, can neither decay nor break.** The drift of a
clock is bought entirely with the strength of its background and the length of its period — which is
what the energy estimate the card began with says, read through the spectrum.

Taking logarithms turns the annulus into the statement a physicist reads. A multiplier `k` describes a
mode multiplied by `k` each period, so its **Floquet exponent** is `log|k|/T`, the growth rate per
unit time, and the annulus says `|log|k|| ≤ b·|T|` (396). Hence

**`abs_floquetExponent_le`**: `|log|k| / T| ≤ b`.

A mode cannot grow or decay faster than the strength of the background it moves in, whatever the
period. That is the energy estimate `‖v(t)‖ ≤ ‖v(0)‖e^{b|t|}` of statement 186 in spectral form, and
it is sharp: the free field has `b = 0` and exponent zero (347).

### A time-symmetric driving pairs its multipliers

Statement 363 inverts the multipliers under time reversal. When the background is even in time —
`W(−r) = W(r)`, a driving that looks the same run backwards — reversing time changes nothing, so the
spectrum is **invariant under inversion** (398):

`σ(M) = σ(M)⁻¹`,   equivalently   `k ∈ σ(M) ↔ k⁻¹ ∈ σ(M)` (399).

The multipliers of such a clock come in reciprocal pairs, and the consequence is sharp: a multiplier
outside the unit circle is accompanied by one inside it, so

**`norm_eq_one_of_mem_spectrum_of_time_symmetric`** — a *stable* time-symmetric clock has **all** of
its multipliers on the unit circle.

There is no partial stability for a driving symmetric in time: either every mode oscillates, or some
mode grows. This is the same conclusion as 366 for two-way stable clocks, reached from a symmetry of
the background rather than from a demand on the solutions.

That symmetry also cheapens the capstone. Statement 367 asks for stability in *both* directions of
time; for a background even in time the two demands are one, because the reflected background is the
background itself and a bound on the solutions run forwards is literally a bound on the reflected
problem's (401). Hence

**`spectralRadius_eq_one_of_time_symmetric_stable`** — a time-symmetric periodic clock that keeps time
*forwards* has spectral radius exactly one.

The static case is an instance: a constant background is even in time and periodic with every period,
so **a stable clock in a static potential can only oscillate** (403) — the conclusion of 351 obtained
from a symmetry instead of from the conserved energy.

The annulus holds for the spectral radius as well as for each multiplier (406): the upper bound
because a supremum of things below a bound is below it, the lower bound because the spectrum is
inhabited (341) and a supremum dominates any one of its terms. The two elementary facts about suprema
this needs — a spectral value is dominated by the radius (404), and a uniform bound on the values
bounds the radius (405) — are recorded once here, having been inlined twice before.

### The true growth rate

Statement 300 bounds the state after `n` periods by `e^{nb|T|}`, the *estimate's* rate. The true rate
is the spectral radius, and Gelfand's formula says so. mathlib has the formula but not this
consequence: statement 329 extracted the special case `r < 1`, and 407 proves it for an arbitrary
finite radius — for every tolerance `ε` the powers are eventually below `(r+ε)ⁿ`. The monodromy's
radius is finite, being bounded by `e^{b|T|}` (408), so

**`eventually_norm_kgFieldStateT_le_of_spectralRadius`** — after enough periods a clock grows no
faster than its spectral radius, to any prescribed accuracy.

The estimate the card began with gives the rate `b`; the spectrum gives the true one, and 397 says the
two never differ by more than the estimate allows.

The bound below is the same inequality that confines the multipliers: `kⁿ` is a spectral value of
`Mⁿ`, so `|k|ⁿ ≤ ‖Mⁿ‖` (410). The radius of a monodromy is *attained* by a multiplier (342), so the
lower bound holds with `r` itself and needs no tolerance (411), and the two combine into

**`norm_pow_kgMonodromy_sandwich`**: `rⁿ ≤ ‖Mⁿ‖ ≤ (r+ε)ⁿ` eventually, for every `ε > 0`.

The growth of a periodically driven clock is exactly its spectral radius. The estimate's rate `e^{b|T|}`
is an upper bound for `r` (406), never the truth unless the two coincide — which for the free clock
they do, both being one.

Those statements are read at multiples of the period. Between periods nothing much can happen — the
leftover piece is shorter than one period and costs at most `e^{bT}` (312) — so the discrete rate
governs continuous time as well (413), and when the rate is at least one that is an honest exponential
bound:

**`eventually_norm_kgFieldStateT_le_exp_rate`**: `‖v(t)‖ ≤ e^{(log(r+ε)/T)·t}·‖v(0)‖·e^{bT}` for all
large `t`,

with exponent the Floquet exponent of statement 397 at the tolerance chosen. The card's estimate, its
spectral sharpening, and their continuous-time forms now agree.

The rate transfers from the band models too. Statement 324 transfers a uniform bound on the powers and
359 a two-sided one; a *geometric* bound `‖M_Rⁿ‖ ≤ Cqⁿ`, uniform in the cut-off, passes to the limit by
the same argument (416), and a geometric bound caps the spectrum, because `|k|ⁿ ≤ ‖Mⁿ‖` (410) and a
sequence `|k|ⁿ` below `Cqⁿ` forces `|k| ≤ q` (415). Hence

**`spectralRadius_le_of_band_rate`** — the spectral radius of the true clock is bounded by the rate of
its band models.

Growth rate, like stability (324) and oscillation (359), is decidable on the models where the Cauchy
problem is a genuine strong problem.

### Back to the energy

The card's subject is the energy `E(t) = ‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖²`, and the Floquet theory has been
carried on the state, whose norm is its square root. Everything said about the rate of the state
therefore says the same about the energy with the exponent doubled (418–419):

`E(nT) ≤ ‖Mⁿ‖²·E(0)`,   hence eventually   `E(nT) ≤ (r+ε)^{2n}·E(0)`.

And the band transfer reads, in the form the card set out to prove something about:

**`tendsto_kgFieldStateT_zero_of_band_rate`** — if the band models decay at a uniform geometric rate
below one, the true clock decays.

The property the card began by estimating is decided on the models where the Cauchy problem is a
genuine strong problem.

And in continuous time the card's own estimate reappears with the exponent replaced by the truth
(421): the state grows at `log(r+ε)/T` (414) and the energy is the square of its norm, so

**`eventually_kgFieldEnergyT_le_exp_rate`**: `E(t) ≤ e^{2(log(r+ε)/T)·t}·E(0)·e^{2bT}` for all large `t`.

The card opened with `E(t) ≤ E(0)e^{(‖V‖+1)|t|}` for a compactly supported classical solution. It closes
with the same shape for an arbitrary `L²` datum in a periodic bounded background, at twice the Floquet
exponent — the rate the clock actually has — and a constant that costs one period.

One asymmetry is left: the card's estimate carries `|t|`, and the spectral sharpening runs forwards.
The reflection supplies the other direction — the state at `−t` for `W` is the state at `+t` for the
reflected background, up to the velocity flip, which is an isometry (422) — so the backward rate is the
reflected background's forward rate (423). When the background is even in time the two coincide and the
bound closes up:

**`exists_bound_norm_kgFieldStateT_abs`**: `‖v(t)‖ ≤ e^{μ|t|}·‖v(0)‖·e^{bT}` for all `|t|` large,
`μ = log(r+ε)/T`.

That is the shape the card began with — absolute value and all — at the rate the clock actually has.

Squaring it closes the circle (425). The card opens with

`E(t) ≤ E(0)·e^{(‖V‖_∞+1)|t|}`

for a classical solution with uniformly compact spatial support, and it now proves

**`exists_bound_kgFieldEnergyT_abs`**: `E(t) ≤ e^{2μ|t|}·E(0)·e^{2bT}` for all `|t|` large,

for an **arbitrary `L²` datum** in a **periodic background even in time**, with `μ = log(r+ε)/T` twice
the Floquet exponent. The rate is bounded by the estimate's own `b` (397) and is generally smaller; for
the free field it is zero and the inequality degenerates to the exact conservation of statement 53.

For a weak static real potential the inequality collapses further, in both directions. Statement 319
bounds the powers by `K = √((1+b)/(1−b))` uniformly; the evolution is invertible and its inverse obeys
the same bound, so the powers are bounded *below* too — `‖Mⁿv‖ ≥ ‖v‖/K`, since `v = M⁻ⁿMⁿv` and a right
inverse telescopes through powers (426). Hence

**`kgFieldEnergy_trapped_of_small_potential`**: `E(0)·(1−b)/(1+b) ≤ E(nT) ≤ (1+b)/(1−b)·E(0)`,

and the spectral radius is exactly one (427): every multiplier lies on the unit circle (351) and the
spectrum is inhabited (341). A weak static potential neither drives a clock nor damps it — it can only
shift the energy by a fixed factor, once and for all.

And the trap is not confined to multiples of a period. A constant background is periodic with *every*
period, so taking the period to be `t` itself and one step of the evolution gives

**`kgFieldEnergy_trapped_all_time`**: `E(0)·(1−b)/(1+b) ≤ E(t) ≤ (1+b)/(1−b)·E(0)` for **every**
`t ∈ ℝ`.

The clock's energy never leaves a fixed band. That is the strongest form the card's inequality takes:
no exponential at all, in either direction of time, with both constants read off from the potential's
strength alone.

### The Floquet normal form

A Floquet multiplier is a point of the monodromy's spectrum. When it is *attained* — by an eigenvector
of the monodromy — the solution it carries is rigid. The restart law says the evolution over one period
starts again from the state it has reached, so an eigen-datum reproduces itself up to its multiplier
at **every** instant, not only at multiples of the period:

**`kgFieldStateT_eigen_shift`**: `v(t + T) = k·v(t)`.

Two consequences. First, the growth of an eigen-solution is *exactly* geometric —
**`norm_kgFieldStateT_eigen`**: `‖v(nT)‖ = |k|ⁿ‖v(0)‖` — with no `ε` and no one-period constant `e^{bT}`;
along eigen-data the approximate rates of statements 407–425 become an identity. Second, writing
`k = e^{μT}` with `μ = log k / T`, the solution splits as

**`exists_floquet_normal_form`**: `v(t) = e^{μt}·p(t)`,   `p(t + T) = p(t)`,

the classical Floquet normal form. The multiplier is the entire content of the solution's long-time
behaviour: the periodic factor contributes nothing to the rate.

### An eigen-clock in a weak static potential keeps exact time

For a weak static real potential the powers of the monodromy are bounded above (319) and below (428) by
the same constant `K = √((1+b)/(1−b))`. Along an eigen-solution the stroboscopic growth is exactly
`|k|ⁿ`, so `|k|ⁿ` is confined to `[1/K, K]` for every `n` — and a nonnegative real whose powers stay in
a fixed compact interval away from `0` and `∞` must be `1`:

**`norm_floquet_multiplier_eq_one_of_small_potential`**: `|k| = 1`.

The energy of such a solution is therefore not merely trapped in the band of statement 430; it returns
to its initial value **exactly**, at every period:

**`kgFieldEnergy_eigen_conserved_of_small_potential`**: `E(nT) = E(0)`.

A clock that repeats itself stroboscopically in a weak static potential keeps exact time.

### The exact envelope

The normal form makes the continuous-time behaviour of an eigen-solution completely explicit. Its
periodic part is continuous, so it is bounded on a single period, and — when the solution never
vanishes — bounded away from zero there as well; periodicity then carries both bounds to the whole
line. The result is an exact two-sided envelope:

**`exists_two_sided_envelope_of_eigen`**: `m·e^{(Re μ)t} ≤ ‖v(t)‖ ≤ M·e^{(Re μ)t}` for **all** `t ∈ ℝ`.

No `ε`, no one-period loss `e^{bT}`, no restriction to large `|t|`: the rate is exactly the Floquet
exponent `Re μ = log|k|/T`, and the only freedom left is the pair of constants — which is the sharpest
form such a statement can take, since a nonconstant periodic factor genuinely oscillates.

For a weak static real potential the two-sided monodromy bound puts the multiplier on the unit circle
(440), so the exponent vanishes and the envelope is **flat**:

**`exists_flat_envelope_of_small_potential`**: `m ≤ ‖v(t)‖ ≤ M` for all `t`, with `m > 0`.

The nonvanishing hypothesis is discharged there, not assumed: the all-time lower bound `‖v(t)‖ ≥
‖v(0)‖/K` of statement 451 — statement 428 read at period `t` — keeps the state away from the origin
at every instant.

### Symmetries

The evolution is assembled from exactly two ingredients: the free propagator and the source operator
built from the potential. An operator `Λ` on `L²` that commutes with the free building blocks —
`cos t⟨D⟩`, `sin t⟨D⟩`, `⟨D⟩⁻¹` — and with the potential at every time commutes with both, and the
uniqueness of the Duhamel solution promotes that to a commutation with the whole flow:

**`kgDiagOp_kgStateMildT`**: `Λ v(t) = v_{Λ·datum}(t)`.

This is the Noether statement for the model, and it has two structural consequences. The monodromy of
a periodic background commutes with every such symmetry (**`kgMonodromy_kgDiagOp_comm`**), so the whole
Floquet spectral theory of statements 293–453 splits along the symmetry's eigenspaces. And a Cauchy
datum fixed by the symmetry stays fixed for all time (**`kgFieldStateT_fixed`**): symmetric initial data
generate symmetric solutions, which is the conservation law the symmetry carries.

The symmetry class is not abstract. Two Fourier multipliers commute, because their symbols do
(**`fourierMulCLM_comm`**), and the free building blocks `cos t⟨D⟩`, `sin t⟨D⟩`, `⟨D⟩⁻¹` are Fourier
multipliers — so for a background that is a Fourier multiplier at each time, *every* Fourier multiplier
satisfies all four commutation hypotheses at once:

**`kgFieldStateT_fourierMul_symmetry`**: a frequency-diagonal background admits the whole multiplier
algebra as symmetries.

The low-pass projections are Fourier multipliers, so the invariance statement reads:

**`kgFieldStateT_band_invariant`**: a band-limited Cauchy datum stays band-limited for all time.

A background diagonal in frequency cannot move energy between frequency bands — which is exactly why
the band programme of statements 237–292 has to work with `P_R W P_R` and pay an approximation error
for a general potential: only the diagonal ones leave the bands alone.

On the diagonal backgrounds there is no error to pay at all. Inside the band the truncated potential
acts exactly as the full one — `P_R` commutes with a diagonal `W` and fixes the solution, so the two
source terms coincide pointwise along the flow (**`kgSourceOp_kgBandOp_eq`**) — and Duhamel uniqueness
turns that into an identity of flows:

**`kgStateMildT_kgBandOp_eq`**: the band model reproduces the true solution exactly, at every time,
with no error term.

So the band energy is exact as well (**`kgFieldEnergyT_kgBandOp_eq`**): a band-limited clock in a
frequency-diagonal background loses nothing to band truncation. The approximation theorems of
statements 237–292 are needed only where the background genuinely mixes frequencies.

### The flow decouples

A symmetry that is a *projection* does more than preserve its range: it splits the trajectory. The
datum decomposes as `Λv + (1 − Λ)v`, the flow is additive, and the symmetry law keeps the two pieces
apart — the first stays in the range of `Λ` for all time, the second stays in its kernel:

**`kgFieldStateT_decouple`**: `v(t) = v_{Λ}(t) + v_{1−Λ}(t)`, with `Λ v_Λ(t) = v_Λ(t)` and
`Λ v_{1−Λ}(t) = 0`, for every `t`.

The low-pass operators are projections and, on a frequency-diagonal background, symmetries. So

**`kgFieldStateT_band_decouple`**: a clock's dynamics decouples across every frequency band exactly —
the low-frequency part of the solution is the solution of the low-frequency part of the datum, and
nothing crosses between the bands at any time.

### The self-adjointness hypothesis, discharged

The whole small-potential theory — the two-sided monodromy bound (319, 428), the trapped energy (429,
430), the eigen-clock (441), the flat envelope (453) — carries self-adjointness of the potential as a
hypothesis. For a Fourier multiplier that hypothesis is a property of the symbol alone. The `L²` inner
product is the integral of `conj f · g`, so a real factor moves across it (**`lpBoundedMulCLM_inner`**);
the Fourier transform is unitary, so the multiplier it conjugates inherits the property
(**`fourierMulCLM_inner`**). In particular the low-pass projections are *orthogonal* projections
(**`kgLowPassOp_inner`**).

The hypothesis is therefore discharged for every real bounded symbol, and the trapping law becomes a
statement with no hypotheses beyond the size of the symbol:

**`kgFieldEnergy_trapped_diagonal`**: for a real symbol of sup-norm `b < 1`,
`E(0)·(1−b)/(1+b) ≤ E(t) ≤ (1+b)/(1−b)·E(0)` at **every** instant `t ∈ ℝ`.

That is the card's inequality in its final form on a concrete, explicitly described class of
potentials: no exponential, no `ε`, no hypothesis one cannot check by looking at the symbol.

### The energy is the sum of the band energies

Orthogonality upgrades the decoupling of statements 477–478 from qualitative to quantitative. A
self-adjoint projection makes what it fixes orthogonal to what it annihilates
(**`inner_eq_zero_of_proj`**), so Pythagoras holds on the energy space across it
(**`norm_kgEnergy_add_sq`**); the flow keeps the two halves of a trajectory in those two subspaces for
all time, and therefore

**`kgFieldEnergyT_band_split`**: `E(t) = E_low(t) + E_high(t)` at **every** instant,

each summand being the energy of the solution generated by that band of the datum. A clock in a
frequency-diagonal background is an exact direct sum of independent band clocks: no band borrows
energy from another, and each is separately governed by the estimate.

### Annuli

A band of frequencies is an annulus, not a disc. The annulus symbol — the indicator of
`R₁ < ‖ξ‖ ≤ R₂` — is real, takes only the values `0` and `1`, and on ordered radii is the difference of
the two low-pass symbols (**`kgAnnulus_eq_sub`**), so the annulus operator is a self-adjoint projection
(**`kgAnnulusOp_idem`**, **`kgAnnulusOp_inner`**) and a Fourier multiplier, hence a symmetry of every
frequency-diagonal background.

Everything proved for the discs therefore holds for annuli:

**`kgFieldStateT_annulus_decouple`** and **`kgFieldEnergyT_annulus_split`**: a clock's trajectory
decouples across any annulus of frequencies, and its energy is the energy carried inside the annulus
plus the energy carried outside it, at every instant of time.

### No ultraviolet cascade

The decomposition has a consequence about the *whole future*. In a weak real diagonal potential the
energy above a cutoff is the energy of an independent sub-clock, so the trapping law of statement 483
bounds it by `(1+b)/(1−b)` times its **own** initial value at every instant
(**`kgFieldEnergy_high_le`**) — and that initial value tends to zero as the cutoff grows, because the
low-pass projections converge strongly to the identity (**`tendsto_norm_sub_kgLowPassOp`**). Hence

**`exists_cutoff_high_energy_small`**: for every `ε > 0` there is an `R₀` such that for every cutoff
`R ≥ R₀` and **every** time `t`, the clock's energy above `R` is at most `ε`.

Combined with the splitting this is **`kgFieldEnergy_no_uv_cascade`**: all but `ε` of a clock's energy
stays below a fixed frequency, forever. A frequency-diagonal background cannot drive energy up the
spectrum — what starts below a frequency stays below it, up to an error fixed once and for all, with
no dependence on the length of the time window.

### The spectral profile is frozen

The same argument applies to every band at once, and in both directions. Each band carries an
independent clock, so the trapping law confines its energy — above *and* below — to the fixed interval
around its own initial value:

**`kgFieldEnergy_annulus_trapped`**: `E_A(0)·(1−b)/(1+b) ≤ E_A(t) ≤ (1+b)/(1−b)·E_A(0)` for every
annulus `A` of frequencies and every `t`.

Together with the splitting this is **`kgFieldEnergy_spectrum_frozen`**: the band energies still add up
to the total, and no band gains or loses more than the fixed factor `(1+b)/(1−b)`, ever. That is
strictly stronger than the trapping of the total energy (statement 483), which on its own would permit
energy to move freely between frequencies while the sum stayed put.

### The estimate, band by band

When the background *moves* the trapping law is no longer available — energy can genuinely be pumped in
— but the decoupling survives untouched. So the card's inequality applies to each band separately, with
that band's own initial energy on the right:

**`kgFieldEnergyT_band_resolved`**: the energy splits across the annulus at every time, the initial
energy splits with it (**`kgDatum_energy_split`**, from orthogonality of the projection), and each part
satisfies `E_A(t) ≤ e^{2b|t|}·E_A(0)`.

The decomposition is lossless — the band bounds add up to exactly the global bound — so what the
band-resolved form adds is the *attribution*: a band's growth is charged to its own initial energy. A
band that starts empty stays empty, however violently the background moves.

This is enough to recover the no-cascade conclusion in window-limited form. On `[−T, T]` the
exponential factor is bounded by `e^{2bT}`, and the initial high-frequency energy still tends to zero
with the cutoff, so

**`exists_cutoff_high_energy_small_window`**: for every `ε` and every window there is a cutoff above
which the clock carries less than `ε` of energy throughout the window,

and with the splitting, **`kgFieldEnergyT_no_uv_cascade_window`**. The dependence of the cutoff on the
window is honest — a moving background really can pump energy upward, so the uniform-in-time statement
of 508 is false here. What survives unconditionally is the attribution: the growth is always charged to
the energy already in the band, never borrowed across a band boundary.

### The shifted frequency

A real frequency-diagonal potential does not change the *shape* of the Klein–Gordon equation, only its
frequency: `ü + (⟨D⟩² + v)u = 0` is the free equation with `⟨ξ⟩` replaced by

`Ω_v(ξ) = √(⟨ξ⟩² + v(ξ))`,

and this is a genuine positive frequency whenever `|v| ≤ b < 1`, because `⟨ξ⟩² ≥ 1` leaves room for the
perturbation (**`kgShiftedFreq_pos`**, **`one_sub_le_kgShiftedFreq_sq`**). The shifted symbols
`cos(tΩ)`, `sin(tΩ)`, `sin(tΩ)/Ω` are measurable, real, and bounded — the third by the elapsed time
alone (**`norm_kgShiftedSinOverFreq_le`**), which is what makes the shifted propagator bounded without
any lower bound on the frequency — so they define Fourier multipliers, self-adjoint by statement 480.

The bounds are proved unconditionally: where the radicand would be negative the Lean square root
returns zero and `sin(tΩ)/Ω` returns zero, which satisfies the same estimate. The hypotheses on `v`
enter only through the identity `Ω² = ⟨ξ⟩² + v`.

The shifted symbols obey the addition formulas of the circle, and the multipliers they define inherit
them. So the shifted propagator is a one-parameter family with exactly the algebra of the free one:

**`kgShiftedCosOp_zero`**: it is the identity at time zero, and

**`kgShiftedCosOp_add`**, **`kgShiftedSinFreqOp_add`**: advancing by `t + s` is advancing by `t` and
then by `s`, with cosine and sine mixing as they do for the free field.

The division by `Ω` is harmless throughout: `sin((t+s)Ω)/Ω = (sin(tΩ)/Ω)cos(sΩ) + cos(tΩ)(sin(sΩ)/Ω)`
is an identity of division rings, so it holds where the shifted frequency degenerates as well, both
sides being zero there.

Below a fixed frequency the shifted frequency is bounded, `Ω² ≤ 1 + R² + b` (**`kgShiftedFreq_sq_le`**),
so the Taylor estimates of the circle become uniform there:

**`norm_kgShiftedCosOp_lowPass_sub_le`**: `‖(cos(τΩ) − 1)P_R‖ ≤ τ²(1 + R² + b)/2`,

**`norm_kgShiftedSinFreqOp_lowPass_sub_le`**: `‖(sin(τΩ)/Ω − τ)P_R‖ ≤ |τ|³(1 + R² + b)/6`.

These are the shifted counterparts of the free band estimates already in the corpus, and they are what
makes the shifted propagator differentiable in operator norm on a band — the step that turns the
shifted symbols into an actual solution operator.

That step is now taken. The group law turns the increment of the shifted sine propagator into exactly
those two defects,

`S(s) − S(t) − (s−t)C(t) = S(t)(C(s−t) − 1) + C(t)(S(s−t) − (s−t))`,

both quadratic in the increment below the cutoff, so

**`hasDerivAt_kgShiftedSinFreqOp_lowPass`**: `d/dt (sin(tΩ)/Ω) = cos(tΩ)` on a band.

This is the first of the two equations of motion of a frequency-diagonal background — the one carrying
no unbounded factor.

The second equation of motion carries the factor `Ω²`, which is unbounded — but bounded below a fixed
frequency, by statement 546. So `Ω²χ_R` is a Fourier multiplier of norm at most `1 + R² + b`
(**`norm_kgShiftedFreqSqLowOp_le`**), self-adjoint because its symbol is real
(**`kgShiftedFreqSqLowOp_inner`**): the generator of the shifted propagator restricted to that band.

The identity that will drive the second equation is the cosine addition formula rewritten through the
*bounded* sine symbol,

**`kgShiftedCos_add_lowPass`**: `cos((t+s)Ω)χ = cos(tΩ)cos(sΩ)χ − Ω²χ·(sin(tΩ)/Ω)·(sin(sΩ)/Ω)χ`,

which holds because `Ω > 0` for a weak potential and the band symbol is idempotent.

Composing multipliers turns that symbol identity into an operator identity on the band
(**`kgShiftedCosOp_lowPass_add`**): `C(t+s)P = C(t)C(s)P − G·S(t)S(s)P`. Subtracting `C(t)P` and the
linear term leaves exactly the two band defects of statements 550 and 553, both quadratic in the
increment, so

**`hasDerivAt_kgShiftedCosOp_lowPass`**: `d/dt cos(tΩ) = −Ω²·(sin(tΩ)/Ω)` on a band.

With statement 554 this is the complete system of equations of motion of a frequency-diagonal
background, written entirely in bounded operators — the form the mild theory needs.

The strong form used by that theory reads `⟨D⟩⁻²ü = −u + ⟨D⟩⁻²(Wu)`, so the potential enters with a
minus sign relative to the frequency: the natural frequency of a real diagonal potential `p` is
`Ω² = ⟨ξ⟩² − p`. Against `⟨D⟩⁻²` the generator of that frequency collapses to exactly the equation's
right-hand side:

**`kgFreqInvSq_kgShiftedFreqSqLow`**: `⟨ξ⟩⁻²·Ω²χ·χ = χ − ⟨ξ⟩⁻²·p·χ`.

This is the algebraic step that turns the two equations of motion into a strong solution.

All the operators of the shifted calculus are Fourier multipliers, so they commute with the band
projection (statements 567–569), and the collapse holds in operator form:

**`kgFreqInvOp_sq_kgShiftedFreqSqLowOp`**: `⟨D⟩⁻²(Ω²χ(Pz)) = Pz − ⟨D⟩⁻²(p(Pz))`,

both sides being multipliers of the same symbol. This is precisely the right-hand side the strong
equation demands, so the candidate `u(t) = cos(tΩ)Pu₀ + (sin(tΩ)/Ω)Pu₁`, whose second derivative is
`−Ω²χ·u(t)` by statements 554 and 562, satisfies it.

### The explicit solution

Putting the pieces together closes the construction. The field

**`kgShiftedField`**: `u(t) = cos(tΩ)Px + (sin(tΩ)/Ω)Py`,   `Ω² = ⟨ξ⟩² − p`,

stays band-limited (572), differentiates to `−Ω²χ(sin(tΩ)/Ω)Px + cos(tΩ)Py` (573), which
differentiates to `−Ω²χ·u(t)` (574); against `⟨D⟩⁻²` that acceleration collapses to `−u + ⟨D⟩⁻²(p·u)`,
and the band-compressed potential acts on the band-limited field as the potential itself, so

**`solvesKGSourceT_kgShifted`**: the shifted propagator is a strong solution of the band problem, with
`u(0) = Px`, `u̇(0) = Py`,

and by the uniqueness of that problem (statements 278–281),

**`eq_kgShiftedField_of_solvesKGSourceT`**: it is the **only** one.

So for a real frequency-diagonal potential the clock is solved in closed form: the propagator is
multiplication by `cos(tΩ)` and `sin(tΩ)/Ω` on the Fourier side, with `Ω` the shifted frequency.

The corpus builds its solution as a *mild* solution of the Duhamel equation. That solution is also a
strong solution of the band problem with the same data, so uniqueness identifies the two:

**`kgFieldMildT_eq_kgShiftedField`**: the Duhamel field of a real diagonal potential on a band is
`cos(tΩ)Px + (sin(tΩ)/Ω)Py`,

and, by uniqueness of derivatives, **`kgFieldVelT_eq_kgShiftedVel`** for the velocity. The clock of a
diagonal background is computed, not merely estimated.

The construction contains the free field as the case `p = 0`: there the shifted frequency is `⟨ξ⟩`
(**`kgShiftedFreq_zero`**) and each shifted operator is its free counterpart (**584**, **585**), the
identification of multipliers being independent of which bound was used to build them
(**`fourierMulCLM_congr`**).

The same self-adjointness that discharged the trapping hypothesis discharges the hypothesis of the
exact conservation law of statement 231, so

**`kgFieldEnergy_conserved_diagonal`**: for **every** real diagonal potential — no smallness at all —
the modified energy `E(t) − ⟨p·u(t), u(t)⟩` is exactly conserved.

Finally the band compression can be removed. On a frequency-diagonal background it is exact for
band-limited data (statement 473), so the solution of the *true* diagonal background, started from
band-limited data, is the same closed form:

**`kgFieldMildT_diagonal_eq_kgShiftedField`**: `u(t) = cos(tΩ)Px + (sin(tΩ)/Ω)Py`, with the potential
itself and no compression.

### A potential that flattens the frequency

The shifted frequency is `Ω² = ⟨ξ⟩² − p`, and `p` is at our disposal. Taking

**`kgFlatPot`**: `p(ξ) = ‖ξ‖²` for `‖ξ‖ ≤ √b`, and `0` beyond,

makes `Ω = 1` identically on that band (**`kgShiftedFreq_kgFlatPot`**), and `|p| ≤ b` holds precisely
because the band is where `‖ξ‖²` does not exceed `b`. On such a band the shifted symbols lose their
dependence on the frequency altogether:

`cos(tΩ)χ = (cos t)χ`,   `(sin(tΩ)/Ω)χ = (sin t)χ`.

A clock started from data in that band therefore runs at a single frequency — the step towards an
exactly periodic clock, and towards showing that the eigen-class of the Floquet theory is not empty.

At the operator level this makes the shifted propagator multiplication by scalars (**593**, **594**),
so the closed form of the solution collapses to a plane rotation:

**`kgShiftedField_kgFlatPot`**: `u(t) = (cos t)Px + (sin t)Py`.

Hence **`kgShiftedField_kgFlatPot_periodic`**: the clock is exactly `2π`-periodic, and
**`kgShiftedField_kgFlatPot_two_pi`**: it returns exactly to its initial state after one period. This
is a genuine bounded real potential — not a limiting or degenerate case — in which a clock repeats
itself exactly.

The velocity returns with it. On the flat band the generator `Ω²χ` is the band projection itself
(**`kgShiftedFreqSqLowOp_kgFlatPot`**), so the velocity is `−(sin t)Px + (cos t)Py` and equals `Py` at
`t = 2π`. Transporting both through the identification of statements 579 and 580 — the gradient by the
injectivity of `⟨D⟩⁻¹` — gives the energy-space form:

**`kgMonodromy_kgFlatPot_fixed`**: the monodromy at `2π` fixes every band-limited state, `M v = v`.

So the eigen-class of the Floquet theory is **not empty**: in a genuine bounded real potential every
nonzero band-limited datum is an eigenvector of the monodromy with multiplier one, and the eigen-clock
statements 434–453 apply to it.

In the exact form the Floquet layer uses, with the band compression of a self-adjoint potential itself
self-adjoint (**`kgBandOp_inner`**):

**`kgMonodromy_kgFlatPot_eigen`**: `M v = 1 · v`.

Every statement proved for eigen-solutions — the shift law 434, the exact stroboscopic growth 436, the
normal form 438, the exact conservation 441, the flat envelope 453 — therefore has a model, and its
predictions are visible directly in the plane rotation of statement 595.

### No drift

The closed form also bounds the *field*, which the energy estimates do not. The shifted frequency of a
weak potential is bounded below, `Ω ≥ √(1−b)` (**`sqrt_one_sub_le_kgShiftedFreq`**), so the sine
propagator is bounded by `1/√(1−b)` **uniformly in time** rather than by the elapsed time
(**`norm_kgShiftedSinFreqOp_le_inv`** — the estimate `‖sin(tΩ)/Ω‖ ≤ |t|` of statement 532 is the one
that must degrade as `Ω → 0`, and a weak potential never lets that happen). Hence

**`norm_kgShiftedField_le`**: `‖u(t)‖ ≤ ‖Px‖ + ‖Py‖/√(1−b)` for **all** `t`.

The card's estimates bound the pair `(⟨D⟩u, u̇)`; this bounds the field itself, and says a clock in
such a background does not drift, however long it runs.

The velocity is bounded the same way: the generator is bounded on a band (558) and the sine propagator
uniformly in time (607), so

**`norm_kgShiftedVel_le`**: `‖u̇(t)‖ ≤ (1+R²+b)/√(1−b)·‖Px‖ + ‖Py‖`,

and together (**`norm_kgShiftedField_and_vel_le`**) a clock in a weak real diagonal background drifts
in neither position nor velocity, however long it runs.

### Tunable clock rates

The flattening construction has a free parameter. For any rate `c` with `1 ≤ c² ≤ 1 + b` the potential

**`kgTunedPot`**: `p(ξ) = ⟨ξ⟩² − c²` on `‖ξ‖ ≤ √(c² − 1 + b)`, `0` beyond,

is admissible — its size is at most `b` exactly on that band (**`abs_kgTunedPot_le`**) — and makes the
shifted frequency identically `c` there (**`kgShiftedFreq_kgTunedPot`**), so the shifted symbols become
the constants `cos(ct)` and `sin(ct)/c`.

The strength of the potential therefore buys a whole interval of clock rates, `1 ≤ c ≤ √(1+b)`, each
with its own exact period `2π/c`; the case `c = 1` is the flattening potential of statement 588.

At the operator level the propagator is again multiplication by scalars (**618**, **619**), so

**`kgShiftedField_kgTunedPot`**: `u(t) = cos(ct)Px + (sin(ct)/c)Py`,

**`kgShiftedField_kgTunedPot_periodic`**: the clock has exact period `2π/c`, and
**`kgShiftedField_kgTunedPot_period`**: it returns to its initial state there. As `c` runs over
`[1, √(1+b)]` this realises every period in `[2π/√(1+b), 2π]`.

The generator is multiplication by `c²` on that band (**`kgShiftedFreqSqLowOp_kgTunedPot`**), so the
velocity is the one the second-order equation prescribes:

**`kgShiftedVel_kgTunedPot`**: `u̇(t) = −(c sin(ct))Px + (cos(ct))Py`.

Field and velocity together are the rotation of the pair `(Px, Py)` at rate `c`, the sine entries
carrying the reciprocal factors `1/c` and `c`.

At `t = 2π/c` both return, so the state returns (**`kgFieldStateT_kgTunedPot_period`**) and

**`kgMonodromy_kgTunedPot_eigen`**: `M v = 1 · v` at the period `2π/c`.

The Floquet eigen-class is therefore inhabited at **every** period in `[2π/√(1+b), 2π]`, each by its
own admissible potential.

The rotation has complex eigenvectors, and they give multipliers other than one. Started from the pair
`(Px, −icPx)`, both field and velocity acquire the same scalar

**`kgTunedPhase`**: `k(t) = cos(ct) − i sin(ct) = e^{−ict}`,   `‖k(t)‖ = 1`,

by **`kgShiftedField_kgTunedPot_circle`** and **`kgShiftedVel_kgTunedPot_circle`**. This is the datum
that will exhibit an arbitrary point of the unit circle as an attained Floquet multiplier, at every
period — not only the value one.

Transporting both components to the energy space gives the eigenvector equation at an **arbitrary**
period `T`:

**`kgMonodromy_kgTunedPot_circle_eigen`**: `M v = e^{−icT} · v` with `‖e^{−icT}‖ = 1`.

Statement 440 forces every attained multiplier of a weak static real potential onto the unit circle.
This shows the constraint is exactly sharp: as `T` runs over `ℝ`, `e^{−icT}` runs over the whole
circle, so every unit-modulus number really occurs as a multiplier of an admissible potential.

Finally the eigenvectors are not the zero vector. The low-pass symbol is the indicator of a closed
ball, which is compact — hence of finite measure — and of positive measure, so it is a nonzero element
of `L²` fixed by multiplication by itself; transporting it back through the Fourier transform gives

**`exists_ne_zero_kgLowPassOp_fixed`**: a nonzero `z` with `P_R z = z`, for every `R > 0`.

That is what the statements requiring a nonvanishing datum — the unit-modulus law 440, the exact
conservation 441, the flat envelope 453 — need in order to apply.

The frequency operator does not kill it — applying `⟨D⟩⁻¹` to `⟨D⟩_R z` returns `z` — so the
energy-space datum built from it is nonzero as well:

**`exists_ne_zero_eigen_state`**: a nonzero `kgPair(⟨D⟩_R z, P_R y)` with `P_R z = z`.

The Floquet eigenvectors exhibited for the periodic and tuned clocks are therefore genuine
eigenvectors, and every conditional statement of the eigen-theory has a complete model.

Every hypothesis of the eigen-clock law of statement 441 is then available: the flattening potential
is bounded by `b`, its band compression is self-adjoint (603), its monodromy at `2π` fixes the band
(604), and the datum is nonzero (637). So the general theorem fires, and its conclusion is exactly the
conservation the plane rotation exhibits:

**`exists_periodic_clock_energy_conserved`**: `E(2πn) = E(0)`.

That is the general machinery of the card checked end to end against a model where the answer is
already known by inspection.

The same is true of the unit-modulus law. Statement 440 derives `|k| = 1` from the two-sided bound on
the powers of the monodromy; the tuned clock computes its multiplier to be `e^{−icT}`, of modulus one
by inspection. Applying the general law to that clock —

**`exists_tuned_clock_multiplier_norm_one`** —

recomputes the same number by a completely different route: one spectral, one explicit.

The third check is the envelope. Writing the phase as `e^{μT}` with `μ = −ic` (**`kgTunedPhase_eq_exp`**)
supplies the exponent the normal form asks for, and the general theorem gives

**`exists_tuned_clock_flat_envelope`**: constants `0 < m ≤ M` with `m ≤ ‖v(t)‖ ≤ M` for all `t`.

The model shows this directly, since the state is multiplied by a phase and its norm is constant. Once
more the abstract route — through the periodic part of the normal form, its continuity and its
compactness on one period — reaches the same conclusion.

The model in fact does better than the general theorems it confirms. Because the state is multiplied
by a unit-modulus phase,

**`norm_kgFieldStateT_kgTunedPot_circle`**: the state norm is *constant*, not merely trapped, and

**`kgFieldEnergyT_kgTunedPot_circle`**: the energy is conserved at **every** instant, not only at
multiples of a period.

The general laws give a band (483), a flat envelope (453) and stroboscopic conservation (441); on this
clock all three collapse to a single exact conservation law.

That collapse is a property of the *datum*, not of the background. Started instead from a real datum —
vanishing velocity — the same clock has

`⟨D⟩u(t) = cos(ct)·⟨D⟩_R x`,   `u̇(t) = −(c sin(ct))·P_R x`,

so **`kgFieldEnergyT_kgTunedPot_real`**:

`E(t) = cos²(ct)·‖⟨D⟩_R x‖² + c² sin²(ct)·‖P_R x‖²`.

The energy genuinely oscillates, exchanging between gradient and velocity, and the size of the swing
is the spread between `‖⟨D⟩_R x‖` and `c‖P_R x‖`. So the band of statement 483 is not an artifact of
the proof: within a diagonal background the energy really does move, and only the complex eigen-data
hold it fixed.

The range is exact. The energy is a convex combination of its two extreme values with weights
`cos²(ct)` and `sin²(ct)`, so it never leaves the interval between them
(**`kgFieldEnergyT_kgTunedPot_real_between`**) and reaches both ends:

`E(0) = ‖⟨D⟩_R x‖²` (**647**),   `E(π/2c) = c²‖P_R x‖²` (**648**).

The oscillation is therefore a complete exchange between the gradient and the velocity, once per
quarter period, with no dissipation and no growth.

Its size is the frequency spread of the band. Downwards `⟨D⟩⁻¹` recovers the projection from the
frequency-weighted vector and has norm at most one; upwards the frequency operator on the band has
norm `√(1+R²)`. So

**`kgFieldEnergyT_kgTunedPot_real_spread`**: `‖P_R x‖² ≤ ‖⟨D⟩_R x‖² ≤ (c² + b)·‖P_R x‖²`,

using `1 + R² = c² + b` for the tuned band. The two extreme values of the energy therefore lie within
a factor `c² + b ≤ 1 + 2b` of one another — remarkably close to the general trapping band
`(1+b)/(1−b)`, which for small `b` is also `1 + 2b + O(b²)`. The general law and the explicit model
agree to first order in the strength of the potential.

That comparison is itself a theorem. The explicit factor is below the general one
(**`excursion_le_trap_band`**: `c² + b ≤ (1+b)/(1−b)`), the gap being exactly `2b²/(1−b)`
(**`trap_band_sub_excursion`**), and running the explicit formula through it recovers the general
bound:

**`kgFieldEnergyT_kgTunedPot_real_le_trap`**: `E(t) ≤ (1+b)/(1−b)·E(0)` for the model.

So the abstract estimate of statement 483 and the computed model agree, the model sits strictly inside
the band, and the discrepancy between them is second order in the strength of the potential.

The lower half follows the same way. The energy is bounded below by `‖P_R x‖²`, which the frequency
spread bounds below by `E(0)/(c² + b)`, and `c² + b ≤ (1+b)/(1−b)` again:

**`kgFieldEnergyT_kgTunedPot_real_ge_trap`**: `E(0)·(1−b)/(1+b) ≤ E(t)`.

Both halves of the trapping law of statement 483 are therefore recovered from the explicit solution,
by an argument that never mentions the monodromy or the conserved modified energy the general proof
uses.

### Towards two rates on one band

The tuned potential flattens the frequency on the whole of its own band, hence on every smaller band
as well. Stating the symbol identities for an arbitrary sub-band (**658–660**) lets two potentials of
different rates be compared on a band they share: for `c₁ < c₂` the smaller band `‖ξ‖ ≤ √(c₁²−1+b)`
lies inside both, and on it the two clocks are plane rotations at the two different rates.

That is the configuration in which a clock switched between the two rates can be studied — the setting
where the card's exponential estimate could first become sharp, since a static real diagonal potential
never produces growth at all.

At the operator level (**661**, **662**) the two propagators are then genuinely different scalars on
the shared band. In the state coordinates `(⟨D⟩u, u̇)` the evolution at rate `c` over a quarter period
`ct = π/2` sends

`(g, h) ↦ ((1/c)·⟨D⟩h, −c·⟨D⟩⁻¹g)`,

so switching rate after each quarter period composes two such maps and returns
`(g, h) ↦ (−(c₁/c₂)·g, −(c₂/c₁)·h)`: the velocity component is multiplied by `c₂/c₁ > 1` each cycle.
The `⟨D⟩` factors cancel because the two maps carry them in opposite positions.

The generator too is multiplication by `c²` on every sub-band (**663**), so the velocity keeps its
plane-rotation form there (**664**): both rates of a switching pair are described by the same formulas
on the band they share. The cancellation of the `⟨D⟩` factors rests on the two identities
`⟨D⟩⁻¹⟨D⟩_R = P_R` and `⟨D⟩_R⟨D⟩⁻¹ = P_R`, both already in the corpus.

Restating the closed form for an arbitrary band-limited pair rather than a parametrised one
(**665**, **666**) puts the evolution in the shape a switch of rate needs: given `P_R g = g` and
`P_R h = h`,

`u(t) = cos(ct)·⟨D⟩⁻¹g + (sin(ct)/c)·h`,   `u̇(t) = −(c sin(ct))·⟨D⟩⁻¹g + cos(ct)·h`,

so the output of one evolution can be fed into the next.

Statements **667**–**672** close the switching construction. Written in field coordinates — the
initial field `w` itself rather than the momentum `g` with `w = ⟨D⟩⁻¹g` — the tuned clock is the plain
rotation

`u(t) = cos(ct)·w + (sin(ct)/c)·h`,   `u̇(t) = −(c sin(ct))·w + cos(ct)·h`   (**667**, **668**),

valid for any band-limited pair `P_R w = w`, `P_R h = h` with `R ≤ √(c²−1+b)`. At the quarter period
`t = π/(2c)` the cosine dies and the sine is `1`, so the evolution is the exchange

`(w, h) ↦ ((1/c)·h, −c·w)`   (**669**, **670**):

field and velocity swap, and the rate is the exchange factor — in one direction it divides, in the
other it multiplies.

That asymmetry is the whole mechanism. Both `c₁` and `c₂` are admissible on the *same* band whenever
`1 ≤ cᵢ² ≤ 1+b` and `R ≤ √(cᵢ²−1+b)`, so the two quarter periods compose, and **`kgSwitchedClock_step`**
(**671**) states the composite in one theorem: running at rate `c₁` for `π/(2c₁)` and then at rate
`c₂` for `π/(2c₂)` carries

`(w, h) ↦ (−(c₁/c₂)·w, −(c₂/c₁)·h)`.

Up to the sign this is a *diagonal* map with eigenvalues `c₁/c₂` and `c₂/c₁`, so **672** reads off
`‖velocity‖ = (c₂/c₁)·‖h‖`: with `c₂ > c₁` the velocity component grows by a fixed factor on every
cycle, hence by `(c₂/c₁)ⁿ` after `n` cycles, while the field component shrinks by the reciprocal.

This is the first genuinely *growing* clock in the layer, and it is growth of the kind no static
background can produce. A real frequency-diagonal potential has all its multipliers on the unit
circle (**639**) and its envelope is flat (**641**) — the energy neither grows nor decays. Switching
between two such potentials breaks that, and it breaks it at a geometric rate that is explicit in the
two rates. Since every `c` with `1 ≤ c² ≤ 1+b` is available, the achievable growth factor per cycle
ranges over `(1, √(1+b)]`, the whole interval permitted by the admissible band. The card's
exponential estimate is therefore not merely an upper bound with no matching example: switching
realises exponential growth in the energy, with base determined by the size `b` of the potential.

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
- 2026-08-05 — statements 667–672: **the switching composition.** A quarter period at rate `c`
  exchanges field and velocity as `(w,h) ↦ ((1/c)h, −cw)`; composing the quarter periods of two
  admissible rates gives `(w,h) ↦ (−(c₁/c₂)w, −(c₂/c₁)h)`, so the velocity norm is multiplied by
  `c₂/c₁` on every cycle. Switching produces geometric growth where no static real diagonal
  potential can grow at all.
- 2026-08-05 — statements 665–666: **arbitrary band-limited data.** The tuned clock's field and
  velocity restated for any band-limited pair, so one evolution's output is the next one's input.
- 2026-08-05 — statements 663–664: **sub-band generator and velocity.** The tuned generator is `c²`
  on every sub-band and the velocity keeps its rotation form, so both rates of a switching pair share
  one set of formulas.
- 2026-08-05 — statements 661–662: **sub-band propagators as scalars.** Two rates act as different
  scalars on one band, so their quarter-period composition is computable and multiplies the velocity
  component by `c₂/c₁`.
- 2026-08-05 — statements 658–660: **sub-band identities.** The tuned symbols keep their constant
  values on any smaller band, so two rates can be realised on one shared band — the prerequisite for
  switching a clock between rates.
- 2026-08-05 — statements 656–657: **the lower trap from the model.** The energy is at least
  `‖P_R x‖² ≥ E(0)/(c²+b) ≥ E(0)(1−b)/(1+b)`, so both halves of the trapping law follow from the
  explicit solution.
- 2026-08-05 — statements 653–655: **the model sits inside the trap.** `c² + b ≤ (1+b)/(1−b)` with gap
  `2b²/(1−b)`, and the explicit energy formula reproduces the general trapping bound.
- 2026-08-05 — statements 650–652: **the excursion is the frequency spread.** `‖P_R x‖ ≤ ‖⟨D⟩_R x‖ ≤
  √(1+R²)‖P_R x‖`, so the oscillating energy's two extremes lie within a factor `c² + b ≤ 1 + 2b` —
  matching the general trapping band `(1+b)/(1−b)` to first order in `b`.
- 2026-08-05 — statements 647–649: **the exact range.** The oscillating energy is a convex combination
  of `‖⟨D⟩_R x‖²` and `c²‖P_R x‖²`, attains both at `t = 0` and `t = π/2c`, and never leaves the
  interval between them.
- 2026-08-05 — statements 644–646: **a real datum oscillates.** From vanishing velocity the tuned
  clock's energy is `cos²(ct)‖⟨D⟩_R x‖² + c²sin²(ct)‖P_R x‖²` — it genuinely swings, so the trapping
  band is not vacuous and exact conservation is a property of the eigen-datum.
- 2026-08-05 — statements 642–643: **exact conservation at every instant.** The unit-modulus phase
  makes the tuned eigen-clock's state norm constant, so its energy is conserved continuously — sharper
  than the band, the envelope and the stroboscopic law that the general theory provides.
- 2026-08-05 — statements 640–641: **the flat envelope on the tuned clock.** With the phase written
  as `e^{−icT}` the normal-form envelope theorem applies and returns the constant bounds the explicit
  rotation displays.
- 2026-08-05 — statement 639: **the unit-modulus law on the tuned clock.** The spectral derivation of
  `|k| = 1` and the explicit computation `k = e^{−icT}` agree.
- 2026-08-05 — statement 638: **the machinery checked against the model.** Every hypothesis of the
  eigen-clock law holds for the flattening potential, so the general theorem yields `E(2πn) = E(0)` —
  the conservation the explicit plane rotation shows directly.
- 2026-08-05 — statements 635–637: **the eigen-state is nonzero.** `⟨D⟩_R` does not kill a nonzero
  band element, so the energy-space datum is nonzero and the exhibited Floquet eigenvectors are
  genuine.
- 2026-08-05 — statement 634: **the band is nontrivial.** The low-pass symbol is the indicator of a
  ball of positive finite measure, so the band contains a nonzero state and the eigenvectors exhibited
  for the Floquet theory are genuinely nonzero.
- 2026-08-05 — statements 632–633: **the circle is exactly the multiplier set.** The complex datum's
  state rotates by `e^{−icT}`, so at an arbitrary period the monodromy has that eigenvalue: the
  unit-circle constraint of statement 440 is sharp.
- 2026-08-05 — statements 629–631: **the complex datum.** Started from `(Px, −icPx)` the tuned clock
  multiplies field and velocity by the unit-modulus phase `e^{−ict}` — the eigenvector that will give
  non-trivial Floquet multipliers.
- 2026-08-05 — statements 626–628: **the tuned monodromy.** At its own period the tuned clock returns
  in field and velocity, so its monodromy fixes the band: the eigen-class is inhabited at every period
  in `[2π/√(1+b), 2π]`.
- 2026-08-05 — statements 623–625: **the tuned velocity.** The generator is multiplication by `c²` on
  the tuned band, so the velocity of the plane rotation is `−(c sin ct)Px + (cos ct)Py`.
- 2026-08-05 — statements 617–622: **the tuned clock's period.** The tuned propagator is
  multiplication by `cos(ct)` and `sin(ct)/c`, so the clock is the plane rotation at rate `c` with
  exact period `2π/c`, realising every period in `[2π/√(1+b), 2π]`.
- 2026-08-05 — statements 611–616: **tunable clock rates.** The flattening potential generalises to a
  one-parameter family: any rate `c` with `1 ≤ c² ≤ 1 + b` is realised by an admissible potential, so
  the potential's strength buys an interval of exact clock periods.
- 2026-08-05 — statements 609–610: **the velocity does not drift either.** The bounded generator and
  the uniformly bounded sine propagator bound the velocity uniformly in time, completing the no-drift
  pair.
- 2026-08-05 — statements 605–608: **no drift.** The shifted frequency is bounded below by `√(1−b)`,
  so the sine propagator is bounded uniformly in time and the field of a diagonal clock stays bounded
  for all time.
- 2026-08-05 — statements 603–604: **the eigenvector equation.** Band compression preserves
  self-adjointness, and the periodic clock satisfies `M v = 1·v` in the exact form the Floquet layer
  uses — every eigen-solution statement now has a model.
- 2026-08-05 — statements 598–602: **the monodromy fixes the band.** The generator is the band
  projection on the flat band, so the velocity returns with the field, and the monodromy at `2π` fixes
  every band-limited state — the eigen-class of the Floquet theory is inhabited.
- 2026-08-05 — statements 593–597: **an exactly periodic clock.** On the flat band the shifted
  propagator is multiplication by `cos t` and `sin t`, so the clock is a plane rotation: exactly
  `2π`-periodic, returning to its initial state after one period.
- 2026-08-05 — statements 588–592: **a potential that flattens the frequency.** `p(ξ) = ‖ξ‖²` below
  `√b` makes the shifted frequency identically one there, so the shifted symbols become the constants
  `cos t` and `sin t` on that band.
- 2026-08-05 — statement 587: **the closed form without the band.** Band compression is exact on a
  diagonal background for band-limited data, so the true diagonal potential's field is the shifted
  propagator as well.
- 2026-08-05 — statements 581–586: **the free case, and exact conservation.** At zero potential the
  shifted calculus is the free calculus; and a real diagonal potential is self-adjoint, so its modified
  energy is exactly conserved with no smallness assumption.
- 2026-08-05 — statements 579–580: **the mild solution in closed form.** The Duhamel field and
  velocity of a real diagonal potential on a band coincide with the shifted propagator, by strong
  uniqueness and uniqueness of derivatives.
- 2026-08-05 — statements 571–578: **the explicit solution.** The shifted propagator is a strong
  solution of the band problem for a real frequency-diagonal potential, and by the uniqueness of that
  problem it is the only one: the clock is solved in closed form on the Fourier side.
- 2026-08-05 — statements 567–570: **the collapse in operator form.** The shifted operators commute
  with the band projection, and `⟨D⟩⁻²(Ω²χ(Pz)) = Pz − ⟨D⟩⁻²(p(Pz))` — the right-hand side of the
  strong equation.
- 2026-08-05 — statements 563–566: **the generator against the inverse square frequency.** The real
  potential's complex symbol, and the collapse `⟨ξ⟩⁻²Ω²χ² = χ − ⟨ξ⟩⁻²pχ` that matches the right-hand
  side of the strong equation.
- 2026-08-05 — statements 561–562: **the second equation of motion.** The band form of the cosine
  addition formula becomes an operator identity, and its increment reduces to the two quadratic band
  defects, so the shifted cosine propagator differentiates to minus the generator times the shifted
  sine propagator. The equations of motion are now complete in bounded form.
- 2026-08-05 — statements 555–560: **the generator on a band.** `Ω²χ_R` is a bounded self-adjoint
  Fourier multiplier, and the cosine addition formula rewritten through the bounded sine symbol is the
  identity that will produce the second equation of motion.
- 2026-08-05 — statement 554: **the shifted propagator differentiates.** The group law expresses the
  increment through the two band defects, both quadratic, so the shifted sine propagator has a
  derivative below a cutoff and it is the shifted cosine propagator.
- 2026-08-05 — statements 546–553: **the shifted propagator on a band.** The shifted frequency is
  bounded below a cutoff, so the circle's Taylor estimates become uniform: the shifted cosine is the
  identity to second order and the shifted sine is multiplication by the elapsed time to third order.
- 2026-08-05 — statements 536–545: **the group law of the shifted propagator.** The shifted symbols
  satisfy the circle addition formulas, so the multipliers they define form a one-parameter family with
  the free algebra: identity at time zero, and composition adding the times.
- 2026-08-05 — statements 524–535: **the shifted frequency.** The symbol layer of a real diagonal
  potential: `Ω = √(⟨ξ⟩² + v)` is a positive frequency for `|v| ≤ b < 1`, and the shifted propagator
  symbols are bounded, real, and measurable, hence self-adjoint Fourier multipliers.
- 2026-08-05 — statements 521–523: **no cascade on a finite window.** For a moving diagonal background
  the exponential factor is bounded on a window, so a cutoff depending on the window confines all but
  `ε` of the energy below it throughout that window.
- 2026-08-05 — statements 515–520: **the estimate band by band.** For a moving diagonal background the
  bands still decouple, the initial energy splits orthogonally with them, and each band obeys the card's
  inequality charged to its own initial energy.
- 2026-08-05 — statements 510–514: **the spectral profile is frozen.** Each band is an independent
  clock, so the trapping law confines its energy two-sidedly around its own initial value; with the
  splitting, no band gains or loses more than the fixed factor at any time.
- 2026-08-05 — statements 505–509: **no ultraviolet cascade.** The energy above a cutoff is an
  independent sub-clock's energy, so it is trapped by a fixed multiple of its own initial value for all
  time; that initial value vanishes as the cutoff grows, so all but `ε` of the energy stays below a
  fixed frequency forever.
- 2026-08-05 — statements 494–504: **annuli.** The indicator of a frequency annulus is a real
  `0`/`1` symbol, so the annulus operator is an orthogonal projection and a symmetry of every diagonal
  background; a clock decouples across any annulus and its energy splits into inside and outside.
- 2026-08-05 — statements 485–493: **the energy splits along the bands.** Self-adjointness makes the
  low-pass projection orthogonal, so the two halves of a decoupled trajectory are orthogonal at every
  instant and the energy is exactly the sum of the band energies.
- 2026-08-05 — statements 479–484: **self-adjointness discharged.** A real bounded symbol gives a
  self-adjoint multiplication operator, and the unitary Fourier transform carries this to the Fourier
  multiplier; the low-pass projections are orthogonal. The trapping law then holds for every real
  symbol of sup-norm below one, with no further hypothesis.
- 2026-08-05 — statements 475–478: **the flow decouples across a projection.** Additivity in the datum
  plus the symmetry law splits the trajectory into a piece confined to the range of the projection and
  one confined to its kernel; for a frequency-diagonal background this decouples the clock across every
  frequency band, exactly and for all time.
- 2026-08-05 — statements 471–474: **the band model is exact on diagonal backgrounds.** Along a
  band-limited solution the truncated and full potentials have the same source term, so Duhamel
  uniqueness makes the two flows — and the two energies — identical, with no approximation error.
- 2026-08-05 — statements 464–470: **the symmetry class, made concrete.** Fourier multipliers commute
  with one another, hence with the free blocks; a frequency-diagonal background therefore admits the
  whole multiplier algebra as symmetries, and band-limited data stay band-limited for all time.
- 2026-08-05 — statements 454–463: **symmetries.** An operator commuting with the free building blocks
  and with the potential commutes with the whole flow, by Duhamel uniqueness. The monodromy therefore
  commutes with every symmetry of the background, and symmetric data generate symmetric solutions.
- 2026-08-05 — statements 443–453: **the exact envelope.** A continuous periodic function is bounded
  above, and away from zero when it never vanishes, by constants read off one period; through the normal
  form this gives an eigen-solution a two-sided exponential envelope at the exact Floquet rate, valid at
  every real time. In a weak static real potential the exponent vanishes and the envelope is flat.
- 2026-08-05 — statements 431–442: **the Floquet normal form, and the eigen-clock.** An attained
  multiplier makes the estimate an identity: the eigen-solution multiplies by `k` over every period, so
  its growth is exactly `|k|ⁿ` and it splits as `e^{μt}` times a periodic state. In a weak static real
  potential the two-sided monodromy bound confines `|k|ⁿ` to a fixed interval, forcing `|k| = 1`: such a
  clock's energy returns to its initial value exactly, not merely to a band.
- 2026-08-05 — statement 430: **the trap holds at every instant.** A constant background is periodic
  with every period, so taking the period to be `t` puts the two-sided energy trap at every real time,
  not only at multiples of a fixed one.
- 2026-08-05 — statements 426–429: **the energy of a weak static clock is trapped.** The inverse obeys
  the same uniform bound as the monodromy, so the powers are bounded below as well as above and the
  energy stays in the band `[(1−b)/(1+b), (1+b)/(1−b)]·E(0)` for all time; the spectral radius is
  exactly one. Such a potential neither drives the clock nor damps it.
- 2026-08-05 — statement 425: **the card's inequality, at the sharp rate, in both directions.**
  Squaring the two-sided state bound gives `E(t) ≤ e^{2μ|t|}E(0)e^{2bT}` for an arbitrary `L²` datum in
  a periodic time-symmetric background — the shape the card opened with, at twice the Floquet exponent
  rather than at `‖V‖+1`.
- 2026-08-05 — statements 422–424: **the estimate in both directions.** The reflection makes the
  backward rate the reflected background's forward rate, and for a background even in time the two
  coincide, so the sharp bound closes up to `e^{μ|t|}` — the shape the card began with, at the rate the
  clock actually has.
- 2026-08-05 — statement 421: **the card's estimate at the true rate.** Squaring the continuous-time
  state bound gives `E(t) ≤ e^{2(log(r+ε)/T)t}E(0)e^{2bT}` — the shape the card opened with, for an
  arbitrary `L²` datum in a periodic bounded background, at twice the Floquet exponent.
- 2026-08-05 — statements 418–420: **back to the energy.** The state's rate is the energy's rate with
  the exponent doubled, so `E(nT) ≤ (r+ε)^{2n}E(0)` eventually; and a band model decaying at a uniform
  geometric rate below one makes the true clock decay — the card's own subject decided on the band
  models.
- 2026-08-05 — statements 415–417: **the rate transfers from the band models.** A geometric bound on
  the band powers passes to the limit as the uniform one did, and a geometric bound caps the spectrum,
  so the true clock's spectral radius is bounded by the band models' rate. Growth rate joins stability
  and oscillation among the things decidable on a band.
- 2026-08-05 — statements 413–414: **the true rate in continuous time.** The leftover piece between
  periods costs one factor `e^{bT}`, so the discrete rate governs continuous time, and for a rate at
  least one this becomes an exponential bound with exponent `log(r+ε)/T` — the Floquet exponent at the
  chosen tolerance.
- 2026-08-05 — statements 410–412: **the growth is exactly the spectral radius.** `kⁿ ∈ σ(Mⁿ)` bounds
  the powers below by any multiplier's modulus, and the radius is attained, so `rⁿ ≤ ‖Mⁿ‖` with no
  tolerance; with 409 that sandwiches the growth between `rⁿ` and `(r+ε)ⁿ`. The estimate's rate is an
  upper bound for `r`, never the truth unless the two coincide.
- 2026-08-05 — statements 407–409: **the true growth rate is the spectral radius.** Gelfand's formula
  gives, for an arbitrary finite radius, that the powers are eventually below `(r+ε)ⁿ` — mathlib has
  the formula but not this consequence. The monodromy's radius is finite by the annulus, so a clock
  eventually grows no faster than its spectral radius, to any prescribed accuracy.
- 2026-08-05 — statements 404–406: **the annulus holds for the radius.** With the two supremum facts
  extracted — a spectral value is dominated by the radius, a uniform bound on the values bounds it —
  the annulus of 392 transfers from the individual multipliers to the spectral radius itself.
- 2026-08-05 — statements 401–403: **for a symmetric driving one direction of stability is enough.**
  When the background is even in time the reflected problem is the same problem, so forward stability
  is backward stability and the capstone of 367 applies with half its hypotheses. The static case is
  an instance, recovering 351 from symmetry rather than from the conserved energy.
- 2026-08-05 — statements 398–400: **a time-symmetric driving pairs its multipliers.** If `W(−r) = W(r)`
  the reflected background is the background itself, so 363 makes the spectrum inversion-invariant and
  the multipliers come in reciprocal pairs. A stable time-symmetric clock therefore has all of them on
  the unit circle — the conclusion of 366 obtained from a symmetry of the background instead.
- 2026-08-05 — statements 396–397: **the Floquet exponent is bounded by the background strength.**
  Taking logarithms in the annulus gives `|log|k|| ≤ b·|T|`, hence `|log|k|/T| ≤ b`: a mode grows or
  decays no faster than `e^{b|t|}`, whatever the period. The energy estimate of 186 in spectral form.
- 2026-08-05 — statements 393–395: **a clock cannot drift without a potential.** Both extreme branches
  of the trichotomy need a multiplier off the unit circle, and the annulus of 392 prices that at
  `b·|T| > 0`. A free clock, or one whose period is instantaneous, can neither decay nor break.
- 2026-08-05 — statements 391–392: **the multipliers live in an annulus.** Reversibility gives the
  inverse the same bound as the monodromy, and the spectrum of an inverse is the inverse of the
  spectrum, so every Floquet multiplier satisfies `e^{−b|T|} ≤ |k| ≤ e^{b|T|}`. The annulus closes
  onto the unit circle as the potential weakens: drift per period is rate-limited by the energy
  estimate the card began with.
- 2026-08-05 — statements 387–390: **the observations decide the fate.** The monodromy depends only on
  the background, so the reconstruction results transfer: observationally identical clocks have the
  same Floquet spectrum and the same spectral radius, hence the same verdict in the trichotomy — and
  for a periodic clock one period of band-limited data settles it.
- 2026-08-05 — statements 385–386: **one period reads a periodic potential.** The operator family of
  a periodic potential is periodic, so the periodic reduction of 379 applies and a periodic moving
  real potential is determined a.e. at every instant by one period of short-time clock observations at
  every cut-off — the mirror of the Floquet criterion, which decides the clock's fate from the same
  data.
- 2026-08-05 — statements 383–384: **the potential may move.** The four-term combination of
  multiplication operators is again one, so a pointwise Lipschitz bound on the potentials gives the
  operator Lipschitz hypothesis; with strong continuity in time — what the moving theory assumes
  anyway — a moving bounded real potential is determined a.e. at every instant by short-time clock
  observations at every cut-off.
- 2026-08-05 — statements 380–382: **from the operator to the potential.** The converse the corpus
  lacked — a symbol whose multiplication operator vanishes vanishes a.e. — follows by testing on ball
  indicators and exhausting the space. So a bounded real potential is determined by its multiplication
  operator, and with 378 a static real potential is determined a.e. by short-time clock observations
  at every cut-off: the inverse problem in the register the card was written for.
- 2026-08-05 — statements 377–379: **the inverse problem closed with no band hypothesis.** What a
  band experiment recovers is `P_RWP_R`; the compressions determine the operator (216), so observing
  every cut-off recovers `W` itself, and for a periodic background one period of instants suffices.
  Like the Floquet criterion, the inverse problem reduces to the band models and transfers back.
- 2026-08-05 — statements 375–376: **the reconstruction class is inhabited.** The band compressions
  satisfy the two band hypotheses of 371 by statement 210, and compression is linear and contracting,
  so it preserves the Lipschitz hypothesis. The reconstruction theory applies to the band models the
  rest of the card computes on.
- 2026-08-05 — statements 372–374: **one period of experiments suffices.** A periodic background is
  invariant under integer multiples of its period, so restarting at `s` is restarting at the
  representative of `s` in `[0,P)`; the observation hypothesis of 371 need only be imposed on a single
  period. The inverse problem is now closed in the register the Floquet theory works in.
- 2026-08-05 — statements 370–371: **exact observations determine the moving background exactly.**
  Every sufficiently short probe is admissible, so with vanishing noise the reconstruction bound
  collapses to zero at every instant. Injectivity of 152–154 recovered quantitatively, with the
  cube-root modulus of 369 as its noisy form.
- 2026-08-05 — statements 368–369: **the moving background is read at every instant.** Restarting the
  probe at time `s` is solving the shifted background from zero, and every hypothesis of 174 transfers
  to the shift, so the conditional-stability bound and the cube-root law hold at every instant with
  the same constants — the reconstruction does not degrade with time.
- 2026-08-05 — statements 365–367: **a two-way clock can only oscillate.** Stability in both
  directions of time — the reflected background being periodic with the same period — puts every
  Floquet multiplier on the unit circle and pins the spectral radius at exactly one. The trichotomy
  of 335 has only its marginal branch available to an instrument that keeps time.
- 2026-08-05 — statements 360–364: **time reversal inverts the Floquet multipliers.** The flip is a
  unit, conjugation by a unit fixes the spectrum, and for a periodic background the backward monodromy
  is the inverse of the forward one — so `σ(M_{W(−·)}(T)) = σ(M_W(T))⁻¹`. A mode growing by `k` per
  period forwards decays by `k` backwards: the spectral form of reversibility, and the reason the
  marginal case is the only one a two-way clock can occupy.
- 2026-08-05 — statements 356–359: **oscillation on a band.** The backward monodromy is the flip
  conjugate of the reflected background's forward one, so conjugation by the isometric involution
  leaves the norms of powers alone and the forward band transfer applied to `W(−·)` bounds the
  backward powers. With both bounds, 349 puts every multiplier on the unit circle: oscillation, like
  stability, is decidable on the band models.
- 2026-08-05 — statements 352–355: **time reflection at the level of the state.** The field-level
  reflection of 149 lifts through the velocity flip `(g,h) ↦ (g,−h)`: the gradient is unchanged by
  injectivity of `⟨D⟩⁻¹`, the velocity changes sign as the derivative of a curve composed with `s ↦ −s`.
  Every forward statement about the state now has a backward counterpart.
- 2026-08-05 — statements 348–351: **purely oscillatory clocks.** Two-sided power boundedness alone
  puts a spectrum on the unit circle, since the spectrum of an inverse is the inverse of the spectrum.
  A clock in a weak static real potential has that — its monodromies over `T` and `−T` are inverse and
  both are bounded by `√((1+b)/(1−b))` — so all of its multipliers have modulus one: no secular growth
  and no decay.
- 2026-08-05 — statements 345–347: **the free multipliers lie on the unit circle.** The free monodromy
  is a unit whose inverse is the monodromy over `-T`, also an isometry, so a multiplier of modulus
  below one would make `k·1 − M₀ = −M₀(1 − kM₀⁻¹)` a unit by the Neumann series. With 326 every free
  multiplier has modulus exactly one — the spectral form of exact energy conservation.
- 2026-08-05 — statements 340–344: **the multipliers exist.** The ball indicator built for 114–116
  makes `L²`, the energy space and the operator algebra nontrivial, so every monodromy has nonempty
  spectrum and its radius is attained. The same nontriviality gives `‖M₀ⁿ‖ = 1` exactly for the free
  clock, hence `spectralRadius M₀ = 1`: the free field sits on the boundary of the trichotomy —
  stable but not decaying, which is what keeping time looks like.
- 2026-08-05 — statements 336–339: **the monodromy is Lipschitz in the background**, with constant
  `2Te^{2bT}` against the uniform operator-norm distance. So the decaying regime is open: a strict
  contraction survives every small enough perturbation and the clock still damps out — the Floquet
  verdict survives an inexactly known background.
- 2026-08-05 — statements 332–335: **the Floquet trichotomy.** Passing between the spectral radius and
  its multipliers is the contrapositive both ways, and it collects the pieces into the classical
  statement: radius below one gives decay, above one gives an unbounded solution, and stability
  confines the spectrum to the closed unit disc.
- 2026-08-05 — statements 329–331: **the sharp decay criterion.** mathlib has Gelfand's formula but
  not the consequence that a spectral radius below one makes the powers vanish in norm; that is built
  here for an arbitrary complex Banach algebra and applied to the monodromy, giving decay of the state
  at every time when all Floquet multipliers lie in the open unit disc.
- 2026-08-05 — statements 325–328: **the Floquet multipliers.** From `‖k‖ⁿ = ‖kⁿ‖ ≤ ‖Mⁿ‖‖1‖`: the
  multipliers lie in the disc `|k| ≤ e^{b|T|}`, a stable clock has all of them in the closed unit disc,
  and one multiplier outside it produces a datum whose state is unbounded in time — the classical
  instability criterion, unconditional.
- 2026-08-05 — statements 320–324: **stability can be decided on a band.** The band compression of a
  periodic background is periodic, and the state estimate at equal data makes `M_R → M` strongly; the
  uniform bound `‖M_R‖ ≤ e^{b|T|}` propagates that to every power. So a bound on the powers of the band
  monodromies, uniform in the cut-off, bounds the powers of the true monodromy — the Floquet criterion
  is checkable on the models where the Cauchy problem is a genuine strong problem.
- 2026-08-05 — statements 316–319: **the stable class is inhabited.** A constant background is
  periodic with every period, so the free field gives a monodromy that is an isometry, and a
  self-adjoint potential of strength `b < 1` gives `‖Mⁿ‖ ≤ √((1+b)/(1−b))` uniformly in `n`. The
  criterion of 310 is met with explicit constants, so it is not vacuous.
- 2026-08-05 — statements 311–315: **the dichotomy from the monodromy norm.** The state is contracted
  by `‖M‖` each period and the leftover time costs one factor `e^{bT}`, so `‖M‖ ≤ 1` bounds the clock
  at every time and `‖M‖ < 1` damps it to zero at every time — the two extreme cases of the criterion,
  decided by a single number.
- 2026-08-05 — statements 306–310: **the stability criterion.** A periodic background is periodic
  backwards too, so the monodromy is invertible with `‖M‖, ‖M⁻¹‖ ≤ e^{b|T|}`. Bounded powers give
  boundedness at every time (the leftover piece is shorter than a period); bounded orbits give bounded
  powers by uniform boundedness on the energy space. So a periodically driven clock is stable **iff**
  `sup_n‖Mⁿ‖ < ∞`.
- 2026-08-05 — statements 301–305: **the monodromy operator.** The state is linear in the datum,
  proved by superposition plus Volterra uniqueness, so the period map is a bounded operator `M` with
  `‖M‖ ≤ e^{b|T|}` and `v(nT) = Mⁿ v(0)`. The long-time behaviour of a periodically driven clock is
  the behaviour of the powers of one operator; any bound on them bounds the clock.
- 2026-08-05 — statements 293–300: **a periodically driven clock has a period map.** The evolution
  family of 152 is lifted from the field to the state — the velocity by differentiating the field
  restart, the gradient by injectivity of `⟨D⟩⁻¹` — so a periodic background makes the evolution over
  one period a single map whose `n`-th iterate is the state after `n` periods, and the estimate takes
  the Floquet form `‖v(nT)‖ ≤ ‖v(0)‖e^{nb|T|}`.
- 2026-08-05 — statements 289–292: **the band work accounting approximates the true one.** One lemma
  does it — the compressions act correctly along any convergent curve of states — applied to the
  solution for the potential term and to the derivative family for the work density; the work density
  is bounded by a constant on the interval, so dominated convergence carries the accumulated work as
  well. Both sides of the classical balance of 287 converge as the cut-off grows.
- 2026-08-05 — statements 282–288: **the classical work–energy balance on a band.** Compression is
  linear in the operator, so a switched real potential compressed to a band is the switched
  compression, still self-adjoint and still norm-differentiable; the gradient on a band is `⟨D⟩_R u`
  in a moving background too, and the potential term is an honest integral because the solution is
  band-limited. The abstract identity of 202 becomes
  `Δ[‖⟨D⟩_R u‖² + ‖∂ₜu‖² − φ∫V|u|²] = −∫φ'∫V|u|²`, with the adiabatic bound `e^{L|t|/(1−b)}`.
- 2026-08-05 — statements 274–281: **the strong theory moves.** The energy identity of the strong
  layer evaluates the perturbation at the same instant as everything else, so it holds verbatim for a
  curve of operators; Grönwall uses only the uniform bound and uniqueness only the linearity of each
  `W(t)`. On a band the moving mild solution is again twice differentiable with
  `∂ₜ²u = −⟨D⟩²_R u + W(t)u`, so the strong Cauchy problem in a moving background is well posed there,
  with no smoothing hypothesis on the background.
- 2026-08-05 — statement 273: the moving energy converges uniformly on the window too; the
  approximation thread is now closed in both registers, for field, state, gradient, velocity and
  energy.
- 2026-08-05 — statements 266–272: **the energy converges uniformly, and the whole state thread moves.**
  Both states are bounded on the window by the same constant, so squaring is uniformly continuous
  there and the energy inherits the state's uniform convergence. The state estimate, its endpoint
  monotonicity and the uniform band approximation of state, gradient and velocity then transfer
  verbatim to a moving background — the energy-space kernel is `P(t−s)∘S(W(s))` and the splitting is
  pointwise in the time.
- 2026-08-05 — statements 259–265: **the sharp difference estimate belongs to the state.** The state
  solves its own Volterra equation in the energy space, and the source difference there is the same
  quantity as in the field estimate — `‖(S(W₁)−S(W₂))v₂‖ = ‖(W₁−W₂)u₂‖` — so the whole state obeys the
  bound of 234. Its monotonicity in the endpoint upgrades the pointwise state/energy limits of 243–244
  to uniform convergence on every window, for the state, the gradient and the velocity.
- 2026-08-05 — statements 254–258: **the state and the energy converge in a moving background.** The
  perturbed source converges by the same splitting as in the autonomous case, so both propagator terms
  of the Duhamel formulas converge by domination, and with them the state and the energy. The
  approximation thread is now complete in the moving register: field, state, energy, and uniformity
  over a finite window.
- 2026-08-05 — statements 247–253: **the band approximation for a moving background.** The
  compression at each time inherits the uniform bound and the strong continuity, the splitting that
  gives the sharp difference estimate is pointwise in the time and so survives verbatim for curves of
  operators, and the rest of the approximation thread repeats: convergence at every time and
  uniformly on every window. The clock's background is now allowed to change.
- 2026-08-05 — statements 241–246: **the energy converges and the approximation is uniform on a
  window.** The gradient converges by the sine version of the velocity argument, so the state
  converges in the energy space and with it the energy itself — the sharp estimate 182 and the exact
  conservation 189 are statements about the limit too. And because the bound of 234 is monotone in
  its endpoint, its value at `T` majorises the error over all of `[0,T]`, giving uniform convergence
  on every finite observation window rather than a separate limit at each instant.
- 2026-08-05 — statements 237–240: **the whole state converges, not only the field.** Splitting the
  *source* as `W_Ru_R − Wu = (W_R−W)u + W_R(u_R−u)` makes the Duhamel integrand of the velocity
  converge pointwise — the first term by strong convergence (215), the second by 236 — under a
  constant bound on the interval, so dominated convergence gives `∂ₜu_R(t) → ∂ₜu(t)`. The band
  approximation is therefore faithful on the state a clock reads, not only on the field.
- 2026-08-05 — statements 235–236: **the band approximation is faithful.** Along the true solution the
  discrepancy `(P_RWP_R − W)u(s)` vanishes pointwise and is dominated by `2‖W‖‖u(s)‖`, so dominated
  convergence plus statement 234 gives `u_R(t) → u(t)` for every time. The whole band theory is
  therefore an approximation of the general equation, not a parallel theory about a different one.
- 2026-08-05 — statements 233–234: a difference estimate that measures the perturbations by their
  **action along the second solution** rather than by their operator norm,
  `‖u₁−u₂‖ ≤ (‖f₁−f₂‖+‖h₁−h₂‖+∫₀ᵗ‖(W₁−W₂)u₂‖)e^{bt}`. Statement 136 is the special case where the
  source is bounded by `‖W₁−W₂‖‖u₂‖`; the sharper form survives strong convergence, where that bound
  is vacuous — which is what the band approximation needs.
- 2026-08-05 — statements 230–232: on a band the abstract gradient of the energy thread is literally
  `⟨D⟩_R u`, so the conservation law of 189 for a real band potential reads
  `‖⟨D⟩_R u‖² + ‖∂ₜu‖² − ∫V|u|² = const` — the classical conserved energy, every term a quantity of
  the solution itself.
- 2026-08-05 — statements 227–229: the band solution **is** a `SolvesKGSource` — divide the band
  equation twice by the frequency and use that `⟨D⟩⁻²⟨D⟩²_R` is the band projection — so the
  uniqueness of statement 74 applies verbatim. What was missing was existence, and the band supplies
  it: the strong Cauchy problem is well posed on every band with no hypothesis on the perturbation
  beyond boundedness.
- 2026-08-05 — statements 225–226: **the strong solution on a band, with no smoothing hypothesis.**
  `∂ₜ²u = −⟨D⟩²_R u + Wu` for band-limited data and any bounded perturbation compressed to the band.
  The obstruction of 103–109 — the unbounded `⟨D⟩sin(τ⟨D⟩)` — never appears, because on a band the
  sine propagator factors as `(sin(t⟨D⟩)/⟨D⟩)⟨D⟩_R`: differentiable times bounded.
- 2026-08-05 — statements 221–224: the symbol calculus of `⟨D⟩_R`. `⟨D⟩⁻¹⟨D⟩_R = P_R`, so the
  regularity hypothesis of the differentiated theory is automatic on a band; and
  `sin(t⟨D⟩)P_R = (sin(t⟨D⟩)/⟨D⟩)⟨D⟩_R`, so the propagator whose differentiation was blocked is the
  differentiable one composed with a bounded operator. These are the inputs a strong solution on a
  band needs.
- 2026-08-05 — statements 217–220: the band is **invariant** under the evolution — the projection
  commutes with the propagators and is absorbed by a band-compressed perturbation on both sides, so
  uniqueness carries it through the Duhamel formula. On the band `⟨D⟩²` is a bounded operator of norm
  `≤ 1 + R²` whose double division by the frequency is the projection, so the obstruction behind the
  smoothing hypothesis of 103–109 is absent there.
- 2026-08-05 — statements 213–216: the bands **exhaust** the potential. The indicator symbols converge
  pointwise to one, so the corpus's strong-convergence criterion (48) gives `P_R x → x`, and hence
  `P_R W P_R x → W x`; two perturbations with the same compression on every band are equal. With 211
  this says what the observations determine: on each band quantitatively, across all bands exactly.
- 2026-08-05 — statements 209–212: **the two threads meet.** Conditional stability wanted
  `A = P_R A P_R`, which a multiplication operator never satisfies; the band compression
  `A ↦ P_R A P_R` does, because the low-pass projection is idempotent, and stays self-adjoint,
  because the projection is. So on each band the same class carries both the well-posed inverse
  problem and exact energy conservation.
- 2026-08-05 — statements 205–208: the last abstraction removed. Composing the real potential of 193
  with the switching profile of 203 gives `∂ₜ²u = -⟨D⟩²u + φ(t)V(x)u`, whose work density is
  `φ̇(t)∫V|u|²` and whose adiabatic estimate and exact work accounting have every constant read off
  from `sup|φ|`, `sup|φ̇|` and `sup|V|`.
- 2026-08-05 — statements 202–204: the **exact** work accounting `E(t) − E(0) = −∫₀ᵗ re⟪Ẇ u, u⟫`,
  of which the adiabatic bound is the sign-discarded form; and the canonical instance, a fixed
  self-adjoint perturbation switched by a scalar profile `W(t) = φ(t)W₀`, where the hypotheses reduce
  to bounds on `φ` and `φ̇`.
- 2026-08-05 — statements 197–201: **the adiabatic estimate.** The work–energy identity
  `d/dt E = −re⟪Ẇ(t)u, u⟫` says the energy changes only at the rate at which the background moves;
  with `‖W‖ ≤ b < 1` and `‖Ẇ‖ ≤ L` it integrates to `E(t) ≤ E(0)e^{L|t|/(1−b)}`. No Grönwall is
  needed — `E(t)e^{∓Kt}` is monotone because its derivative has a sign, which is shorter and
  two-sided. `L = 0` recovers exact conservation.
- 2026-08-05 — statements 193–196: the self-adjointness hypothesis is **inhabited** — multiplication
  by a bounded real potential. Conservation, the uniform bound, and the identification of the
  potential term with `∫V|u|²` all specialise; for an attractive potential `V ≤ 0` that integral is
  non-positive, so no smallness is needed and the field stays bounded for all time.
- 2026-08-05 — statements 190–192: what conservation buys. For a **self-adjoint** perturbation the
  exponential of the general estimate disappears entirely: `‖W‖ = b < 1` gives the uniform-in-time
  bound `(1+b)/(1−b)` times the initial energy, and a confining potential (`re⟪Wx,x⟫ ≤ 0`) needs no
  smallness at all. The mechanism is `‖u‖ ≤ ‖⟨D⟩u‖`, the operator form of the mass gap.
- 2026-08-05 — statements 187–189: **exact conservation for a self-adjoint perturbation.**
  `‖⟨D⟩u‖² + ‖∂ₜu‖² − re⟪Wu,u⟫` is constant, in the mild theory and with no smallness. The classical
  term-by-term differentiation is unavailable — each half involves the unbounded generator — so the
  state is carried back to time zero by the free evolution, where the fundamental theorem of calculus
  applies and the generator never appears; unitarity of the propagator transports the inner products
  back, and self-adjointness cancels the two derivatives.
- 2026-08-05 — statements 183–186: the energy estimate is **sharp** — with `W = 0` the Duhamel term
  vanishes, the state is the propagator applied to the datum, and the estimate is an equality — and it
  **survives a moving background**, because the argument never used the autonomy of the perturbation:
  the Volterra kernel `v ↦ (0, W(s)⟨D⟩⁻¹v₁)` obeys the same uniform bound.
- 2026-08-05 — statements 178–182: **the estimate the card is named after, sharp.** For the mild `L²`
  solution with an *arbitrary* bounded perturbation and no regularity hypothesis,
  `‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖² ≤ (‖⟨D⟩u(0)‖² + ‖∂ₜu(0)‖²)e^{2‖W‖|t|}` — constant one, rate exactly `‖W‖`,
  both sharp. The energy method is read through the propagator: the pair `(⟨D⟩u, ∂ₜu)` solves a
  Volterra equation whose free term is an isometry and whose kernel has norm `‖W‖` because `⟨D⟩⁻¹` is
  a contraction, which is the operator form of `‖u‖ ≤ ‖⟨D⟩u‖`.
- 2026-08-05 — statements 175–177: **the cube-root law.** The reconstruction bound `A/x² + Bx` has a
  genuine optimum at `Bx³ = 2A`, where the noise term is exactly half the drift term and the total is
  `(3/2)Bx`; optimality is the identity `(A/y²+By) − (A/x²+Bx) = A(x−y)²(x+2y)/(x³y²)`, a square times
  a positive factor, so no inequality of means is needed. Since the balance point is `(2A/B)^{1/3}`,
  both the optimal probing time and the optimal reconstruction error scale like the **cube root** of
  the observational noise.
- 2026-08-04 — statements 169–174: the probing time can always be chosen, giving conditional
  stability with **no free parameter** and a two-sided band statement; and the reconstruction is
  redone for a **moving** background, where it is necessarily local in time —
  `‖W₁(0)−W₂(0)‖ ≤ 8η(1+bT)/x² + 8Le^{bT}x`, noise over probe-time-squared plus drift times probe
  time, the shape that gives such a measurement an optimal integration time.
- 2026-08-04 — statements 160–168: **conditional stability.** `|sin(τω)/ω| ≤ |τ|` makes the
  perturbation enter at second order in time; cutting to `‖ξ‖ ≤ R` makes both propagators
  Taylor-accurate (the cubic sine estimate is built here, mathlib has only the quadratic cosine one);
  and the two together let the perturbation be read off the short-time field. On perturbations that
  only couple frequencies below `R` the forward map is bounded below, `‖W₁−W₂‖ ≤ 8η(1+bT)/x²`, with
  the admissible probing time of order `(1+R²)^{-1/2}`. The ill-posedness of 155–159 is therefore
  purely a high-frequency phenomenon.
- 2026-08-04 — statements 155–159: **the inverse problem is ill-posed.** The high-pass multiplier of
  height `c` has operator norm exactly `c`, but composed with `sin(τ⟨D⟩)/⟨D⟩` its norm is
  `≤ c/√(1+R²)` — a bound visible only at the symbol level. So for every tolerance and every
  observation window there is a perturbation of fixed size whose field is indistinguishable from the
  free field, uniformly over all data. The forward map is not bounded below and its inverse admits no
  modulus of continuity; the exponential factor in 136/150 is not an artefact of the proof.
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
