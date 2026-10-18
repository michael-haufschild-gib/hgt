# APT stage-2 → stage-3 formalization status

## Done (moved to `3-formalized/`), all `propext/Classical.choice/Quot.sound` only
- `APT-ROOT-RAMP-LIMIT`, `APT-ROOT-RAMP-MARGIN` — `FactorialRampFullWeilSmoothingLimit.lean`.
- `APT-ROOT-WINDOW` — `FactorialPhaseHarmonicLayers.lean`, `FactorialPhaseWindowAndPhysicalRieszBounds.lean`.
- `APT-ROOT-BOHR` — `FactorialPhaseBohrCoercivityAndTailIndependence.lean`.

## Remaining: `APT-ROOT-SPAN-COERCIVITY`
Target (Lean form): `∃ c > 0, ∃ C ≥ 0, ∀ M ≥ 2, ∀ S b, (∀ n ∈ S, M ≤ n + 1) →`
`Summable (zetaZeroConfig.Wsummand f f) ∧ (c log M - C) ∑‖b_n‖² ≤ Re zetaZeroConfig.W f f`,
with `f x = ∑_{n∈S} (b_n / a_n) T_n(x) = e^{3x/2} B_b(e^{-x}) 1_{x≤0}`.

Reusable corpus pieces (found with `scripts/formal_tools.py research`):
- explicit formula on decay class: `RHTower.WeilSpectral.archPoleEnergy_eq_re_W_add_abelPrimePairing`
  (`ExpDecayTest`, `ExpDecayTest.add` in CHMDGraphDivisorPairing, `DecayBound.expDecayTest`);
  `atomPairing_eq_abelPrimePairing_of_decay` (NullRayDilationCriticality);
  `factorialMuntzSmoothedTail_abelPrimePairing_eq`, `factorialMuntzSmoothedTail_crossCorr_bound`.
- Plancherel for decay tests: `expDecayTest_fourier_mass_eq`, `expDecayTest_fourier_sq_gamma_integrable`
  (BiScaleUncertainty.ExpDecayFourierMass); general `HTGeometry.integral_norm_sq_fourier`.
- Gamma bracket: `exposing_archimedean_scalar_quarter`, `WeilPoleWeight.gammaBracket_eq_archimedeanWeilSymbol`.
- zero side: `FactorialMuntzZeroSideLimit` pattern (dominated tsum over zeros), `FactorialTailSampling`
  (`factorialTail_zeroSquare_summable`), `weil_mixed_norm_le_sqrt_square_mass`,
  `conj_mem_zetaZeroConfig`, `mult_conj_zetaZeroConfig`, `CHMDGrowthCollapse.reflectZero`.
- mollifier readouts: `mollifier_readout_tendsto`, `factorialMuntzSmoothed_readout`,
  `WeilHerglotz.norm_paperFT_mollC_le_one`, `integral_exponential_tilt_convolution`.
- scalar assembly already in APT: `high_scale_archimedean_log_coercivity`,
  `high_scale_span_weil_coercivity_bound`, `nonstationary_mellin_majorant_le_five_div_abs`,
  `low_band_plancherel_energy_le_half_arch`, `polar_readout_product_bound`, `canonicalPrimeMajorantConstant`.
- window/weighted bounds (dilated): `factorialPhaseCombination_dilated_window_upper`,
  `factorialPhaseCombination_weighted_upper/lower`, `integral_norm_sq_sum_factorialMuntzCorrectedTail`.

Work items:
1. literal Mellin nonstationary bound `|∫_1^∞ v^{-5/2} e^{i(ωv - t log v)}| ≤ 5/|ω|` (IBP), then
   `|F_b(t)|² ≤ 2D²S/M` for `|t| ≤ πM` (harmonic expansion termwise).
2. correlation identity `C_b(log r) = r^{-3/2}∫_1^∞ v^{-4} B(v) conj B(rv)` and prime budget.
3. polar readouts `P_0, P_1` and budget `6JS`.
4. exact identity `Re W(f,f) = (1/2π)∫|F|²g + 2Re(P_0 P̄_1) - prime(f)` via mollification
   (zero / Gamma / prime / polar channels) and real/imaginary splitting.
5. assembly with `high_scale_span_weil_coercivity_bound`.
