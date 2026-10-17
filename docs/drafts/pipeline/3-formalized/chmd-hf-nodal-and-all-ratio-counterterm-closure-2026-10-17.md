# CHMD Nodal-Cross vs. Prime-Shift Closure & HF All-Ratio Secular/Window Counterterm Closure

- **ID:** chmd-hf-nodal-and-all-ratio-counterterm-closure-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md · Routes `CHMD` + `HF` + `OWU`
- **Statement:** (1) On `SourceGraph`, `-4 sourcePair(posGraph p, negGraph p)` decomposes into the sum of two non-negative terms — `-4 ⟪(fullGroundEquiv p⁺).snd, (fullGroundEquiv p⁻).snd⟫` (strictly positive on sign-changing vectors) and `4 ⟪primeShiftOperator p⁺.fst, p⁻.fst⟫` — which reinforce each other in the primitive-contraction nodal bound, satisfy three-term individual nodal-lobe energy identities and exact odd half-mass lobe laws, and force `ν ≤ μ_max` (or `ν < μ_max` when the primitive `oneL`-defect is dominated by the prime-shift cross term alone). (2) On `HF`, the `M`-stage secular counterterm potential `secantStagePotential M n` telescopes `secantCombinedSecularWeight n * (2 / √n)` exactly for `2 ≤ n ≤ M` with zero square-root relaxation loss on `Finset.Icc 2 N` (`N ≤ M`), decreases monotonically in `M`, and combines with the `+ 2 * sinhHalfMoment f ^ 2` plastic bonus and `oddShift` window laws to establish all-ratio (`S / L` unrestricted) conservation, prime-blind vanishing, and `markovEnergy ≥ 0` laws whenever `2 * sinhHalfMoment f ^ 2` covers the high-frequency secant excess.

## Goal
Close the two coupled analytic steps identified in the frontier review of `CHMD` + `HF` + `OWU`:
1. **Target 1 (`CHMD`):** Bridge the nodal-cross term `-4 sourcePair(p⁺, p⁻)` in `CHMDSpectralBesselAndPrimitiveContractionNodalBounds.lean`, the stationary-vs.-prime-shift decomposition in `CHMDStationaryNodalDecompositionAndPrimeShiftPositivity.lean`, and the nodal-lobe Rayleigh algebra in `CHMDEigenvectorNodalLobeEnergiesAndPrimitiveLobeBounds.lean` into bilateral nonnegative decompositions, odd half-mass lobe laws, universal primitive-contraction resolvent polarization identities, and explicit eigenvalue upper-bound (`ν ≤ μ_max` and `ν < μ_max`) criteria.
2. **Target 2 (`HF`):** Generalize the finite 4-stage secular counterterm telescoping in `MarkovDegreeSixteenFirstCellAndTwentySevenRatioPBAP.lean` to an arbitrary `M`-stage potential `secantStagePotential M n` (with adaptive zero-loss telescoping at `M ≥ N` and stage-monotonicity in `M`) and unify it with the `+ 2 * sinhHalfMoment f ^ 2` bonus and `oddShift` window laws in `MarkovOddShiftWindowAndPlasticCrossoverPBAP.lean` and `MarkovOddSectorFarkasAndOneSidedPBAP.lean` to obtain all-ratio (`S / L` arbitrary) conservation, prime-blind vanishing, and `markovEnergy ≥ 0` criteria.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules `CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure` and `MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP`, `lake build --old` green, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`), wired into `formal/GaloisForLFunctions/RHTower.lean`
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Formalized Modules & Key Theorems
1. **`formal/GaloisForLFunctions/RHTower/CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure.lean`:**
   - `neg_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift` & `neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift`
   - `stationary_and_primeShift_le_neg_sourcePair_posGraph_negGraph` & `primeShift_lt_neg_sourcePair_posGraph_negGraph_of_ne_zero`
   - `stationary_and_primeShift_nodal_cross_le_of_primGraph_absGraph_rayleigh_le`
   - `eigenvector_stationary_and_primeShift_nodal_cross_le_of_primGraph_absGraph_rayleigh_le`
   - `eigenvector_stationary_and_primeShift_nodal_cross_le_spectral_gap_mul_oneL_sq`
   - `eigenvalue_le_of_oneL_defect_le_neg_four_sourcePair` (`ν ≤ μ_max`)
   - `eigenvalue_lt_of_primitive_oneL_defect_le_four_primeShift` (`ν < μ_max`)
   - `posGraph_three_term_nonneg_decomposition_of_eigenvector` & `negGraph_three_term_nonneg_decomposition_of_eigenvector`
   - `stationary_and_primeShift_posGraph_negGraph_le_lobe_fst_sq_of_eigenvector`
   - `norm_posGraph_snd_sq_add_negGraph_snd_sq` & `norm_posGraph_and_negGraph_snd_sq_of_odd`
   - `odd_eigenvector_lobe_energy_and_snd_sq`
   - `inner_resolvent_primGraph_absGraph_sub_self`
   - `inner_resolvent_primGraph_posGraph_negGraph_eq_of_primitive`
   - `eigenvector_primGraph_absGraph_rayleigh_excess`
2. **`formal/GaloisForLFunctions/RHTower/MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP.lean`:**
   - `secantStagePotential` & `secantCombinedSecularWeight_mul_two_div_sqrt_eq`
   - `secantStagePotential_sub_succ_eq_of_le` & `secantStagePotential_eq_of_succ_le`
   - `secantCombinedSecularWeight_mul_two_div_sqrt_le_secantStagePotential_sub_succ`
   - `secantStagePotential_add_le`, `secantStagePotential_nonneg_of_succ_le`, `secantStagePotential_nonneg`
   - `secantStagePotential_sub_succ_stage_eq`, `secantStagePotential_succ_stage_le`, `secantStagePotential_add_stage_le`
   - `secantStagePotential_four_two_eq` & `two_forty_seven_three_hundredths_le_stage_surplus`
   - `sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_eq_of_le_stage` & `sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le_stage`
   - `abs_primeBlindCounterterm_secantCombinedSecularWeight_le_stage`
   - `stage_surplus_l2_add_secantNumerator_le_rightCellQuadratureDefect`
   - `all_ratio_conservation_bound_of_cosh_zero`, `all_ratio_conservation_bound_of_cosh_zero_of_logValue_nonneg`, `all_ratio_conservation_bound_of_cosh_zero_of_logVector_eq_zero`
   - `all_ratio_l2_eq_zero_of_cosh_zero_of_logVector_eq_zero_of_sinh_sq_dominates`
   - `all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates_secant_excess` & `all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates_secant_excess_of_logValue_nonneg`
   - `oddShift_all_ratio_conservation_bound_of_even` & `oddShift_all_ratio_markovEnergy_nonneg_of_even`

## Log
- 2026-10-17 — created in 1-in-progress
- 2026-10-17 — both modules formalized, verified with `lake env lean`, `lake build --old`, and `#print axioms`, wired into `formal/GaloisForLFunctions/RHTower.lean`, and moved to `3-formalized`
