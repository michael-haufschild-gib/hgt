# The theta compact inverse has an infinite zero-Jordan history — Lean certificate

- **Paper card:** `theta-compact-inverse-zero-jordan-history.md`
- **Lean modules (46):** RHTower `ThetaPowerWeightedDerivativeHistory`, `HedenmalmThetaDerivativeJordan`,
  `HedenmalmThetaZeroHistoryNoGo`, `HedenmalmThetaDerivativeHistorySpectrum`, `HedenmalmThetaDerivativeHistoryQuotient`,
  `HedenmalmThetaDerivativeHistoryRiesz`, `HedenmalmThetaDerivativeHistoryFourier`,
  `HedenmalmThetaDerivativeOscillatoryPrimitive`, `HedenmalmThetaDerivativePrimitiveBounds`,
  `HedenmalmThetaQuotientEigenmodeDecay`, `ThetaRealShiftHistory`, `ThetaWeightedTranslationDomain`,
  `ThetaQuantileTranslationHistory`, `ThetaGradedFiniteHistory`, `ThetaWeightedHistoryProperness`,
  `ThetaUnweightedDerivativeHistory`, `ThetaTranslationDensityRatio`, `ThetaInterWeightTranslation`,
  `ThetaTemperedEvaluationBoundary`, `ThetaTemperedMultiplicityJets`, `ThetaTemperedSourceJets`,
  `ThetaCuspSchwartzComplexTranslation`, `ThetaCuspStripTaylorRemainder`, `ThetaCuspSchwartzTranslationCurve`,
  `ThetaTemperedTranslationAnnihilator`, `ThetaTemperedFiniteJetFactorization`, `ThetaTemperedFourierOrbit`,
  `ThetaTemperedFourierCorrelation`, `ThetaTemperedFourierKernel`, `ThetaTemperedPointSupport`,
  `ThetaTemperedCompactDivision`, `ThetaTemperedLocalization`, `ThetaTemperedCompactReconstruction`,
  `ThetaTemperedLocalCoefficients`, `ThetaTemperedCompactCore`, `ThetaTemperedGlobalJets`,
  `ThetaTemperedEndpointClassification`, `TwoGaussianSourceCounterexample`, `TwoGaussianSourceDerivativeAdmission`,
  `TwoGaussianDerivativeFunctionHistory`, `TwoGaussianDerivativeHilbertHistory`, `TwoGaussianDerivativeCenteredHistory`;
  HTGeometry `GeneralizedEigenspaceQuotient`, `CompactInvariantQuotient`, `LpContinuousMultiplierNorm`,
  `L2MeasureCongruence`.
- **Umbrellas:** every module is imported once by `GaloisForLFunctions.RHTower` or `GaloisForLFunctions.HTGeometry`.
- **Verification (2026-10-04):**
  - `#print axioms` for all 779 public declarations of the 46 modules: exactly `propext`, `Classical.choice`, `Quot.sound`.
  - No `sorry`, `axiom`, `admit` or heartbeat option in any of the 46 sources.
  - The last module, `TwoGaussianDerivativeCenteredHistory` (G3c), passed `lake build --old` and a clean final `lake env lean`.
  - The other 45 modules were built and audited by the earlier formalization runs recorded in git history at `0451e007b`.
- **Hypotheses:** only the card's quantifiers (weights `0 < q < 2`, shifts `a`, Xi zeros `z`, finite prime words, tempered functionals). There is no zero-location, RH, compactness or admission premise.

| Card clause | Lean theorem(s) |
|-|-|
| weighted derivative admission `k^{(r)} ∈ L²(k^{-q}dx)` for all `r` and `0<q<2`; `∫k^{(r)} = 0`, `k^{(r)} → 0` at both ends | `thetaWeightedDerivative_memLp`, `thetaSourceDerivativeFunction_memLp`, `integral_thetaSourceDerivativeFunction_succ`, `thetaSourceDerivativeFunction_tendsto_atBot/atTop` |
| **(1)** `Bv₀ = 0`, `Bv_r = i v_{r−1}`, `v₀ = √M·1`, linear independence | `thetaCompactSourceInverse_thetaQuantileDerivativeVector_zero`, `thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ`, `thetaQuantileDerivativeVector_zero`, `linearIndependent_thetaQuantileDerivativeVector`, `thetaCompactSourceInverse_pow_derivative_self/eq_zero` |
| **(2)** centered chain `Dv₁ = 0`, `Dv_r = i v_{r−1}` | `thetaOrthogonalCenteredInverse_thetaCenteredDerivativeVector_zero/succ`, `linearIndependent_thetaCenteredDerivativeVector` |
| **(3)** dense range, injective adjoint, no bounded injective intertwiner (full and centered) | `thetaKernelOperator_no_injective_bounded_symmetrizer`, `thetaOrthogonalCenteredInverse_no_injective_bounded_symmetrizer`, `thetaOrthogonalCenteredInverse_dense_range`, `thetaOrthogonalCenteredInverse_adjoint_injective` |
| `R` invariant, `B|_R` quasinilpotent (spectrum `{0}`), `R` proper | `thetaQuantileDerivativeHistory_invariant`, `thetaDerivativeHistoryInverse_spectrum`, `thetaQuantileDerivativeHistory_ne_top` |
| quotient `B̄` compact, keeps every nonzero Xi eigenvalue with full multiplicity; finite-level root equivalence | `isCompactOperator_continuousInvariantQuotient`, `finrank_genEigenspace_eq_quotient`, `finrank_maxGenEigenspace_eq_quotient`, `analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_thetaDerivativeHistoryQuotientInverse` |
| Riesz projector kills `R` and descends | `ker_thetaDerivativeHistoryRieszProjection`, `analyticOrderAt_XiC_eq_finrank_range_thetaDerivativeHistoryRieszProjection` |
| `L_z` bounded, nonzero, annihilates `R`, left eigenfunctional at `−1/z` | `thetaDerivativeHistoryFourierFunctional_ne_zero`, `thetaDerivativeHistoryFourierFunctional_surjective`, `thetaDerivativeHistoryFourierFunctional_left_eigen` |
| rapid quotient decay `‖πf_z‖ ≤ C_A(1+|z|)^{−A}` | `thetaCanonicalSourceQuotientMode_rapid_decay`, `norm_thetaCanonicalSourceQuotientMode_le_inverse_power` |
| **(4)** `k_a ∈ H_s ⇔ |a| < log 2/2`; `R = closure span{U k_a}`; prime words not admitted | `thetaRealShiftSource_ofReal_memLp_source_iff`, `thetaWeightedDerivativeHistory_eq_realTranslationHistory`, `finiteComplexPrimeThetaShift_not_memLp_source` |
| holomorphic translation orbit on the Gaussian-slack domain | `thetaWeightedTranslationClass_mem_derivativeHistory_of_domain` |
| **(5)** `T_a : H_q → H_{q'}` bounded ⇔ `q' < q e^{−2|a|}` (`a ≠ 0`), `q' ≤ q` (`a = 0`); norm = ess sup | `exists_thetaWeightedTranslation_log_iff`, `exists_thetaWeightedTranslation_prime_iff`, `not_exists_thetaWeightedTranslation_fixed`, `thetaTranslationDensityRatio_bddAbove_iff`, `ofReal_norm_sq_eq_essSup_of_ae_mul_continuous` |
| **(6)** translation history at every `0<q<2`; finite Euler words in history at a common weight | `thetaWeightedDerivativeHistory_eq_realTranslationHistory`, `exists_pos_weight_finitePrimeEuler_history` |
| **(7)** `R_q ≠ H_q` for `0<q<2`, `R_0 = H_0` | `thetaWeightedDerivativeHistory_ne_top`, `thetaWeightedDerivativeHistory_zero_eq_top`, `thetaDerivativeHistory_endpoint_dichotomy` |
| **(8)** tempered annihilator `= 𝓕⁻¹{Q : XiC·Q = 0}` | `thetaUnscaledTemperedDerivativeAnnihilator_eq_Xi_kernel_map/comap`, `thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_realTranslates` |
| **(8)** local structure: Dirac jets of order `< m(t)` | `thetaTemperedPointSupport_Xi_kernel_iff_lowerJetSpan`, `thetaXiTemperedMultiplier_ker_inter_diracJetSpan` |
| **(8)** global locally finite sums with tempered growth (joint seminorm bound) | `thetaXiRawJetJointBound_iff_existsUnique_kernel_coefficients`, `thetaXiRawJetJointBound_iff_existsUnique_sourceAnn_coefficients`, `thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_existsUnique_globalJets` |
| off-real exponential evaluations are not tempered | `thetaOffRealEvaluation_not_tempered`, `exists_thetaTemperedFourierLaplaceEvaluation_iff` |
| two-Gaussian `k_* = e^{−x²}+e^{−2x²}`: positive, even, strictly log-concave, off-real Fourier zero | `source_counterexample`, `strictConcaveOn_log_density`, `density_neg`, `transform_offRealZero`, `offRealZero_im_ne_zero` |
| two-Gaussian: same derivative history, full chain (source and quantile carriers) | `linearIndependent_functionHistoryDerivativeVector`, `sourceHistory_infinite_zero_chain`, `quantileHistory_infinite_zero_chain` |
| two-Gaussian: same centered chain in the mean-zero quotient | `centeredHistory_infinite_zero_chain`, `centeredHistoryInverse_literal`, `starProjection_meanZeroHyperplane` |
