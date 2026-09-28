# Theta Xi as a positive-renewal phase and waiting-time law — Lean certificate

- **Paper card:** `theta-renewal-phase-cosh-factorization.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaRenewalIncrement`, `ThetaRenewalLogKernel`,
  `ThetaRenewalAnalyticContinuation`, `ThetaRenewalCoshFactorization`, `ThetaRenewalSeamGerm`,
  `ThetaRenewalWaitingTime`, `ThetaRenewalProbabilityPhase`, `ThetaRenewalPhaseSlope`,
  `ThetaRenewalPhaseLevel`, `ThetaRenewalExitDensity`; general layers
  `GaloisForLFunctions.HTGeometry.VolterraConvolutionAlgebra`, `VolterraConvolutionCalculus`,
  `DecreasingSineTransformPositivity`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`.

Dictionary: `a = 1/4`, `Θ = HurwitzZeta.evenKernel 0`, `c = Θ 1`, `P = thetaLogProfile`,
`ν = thetaRenewalIncrement`, `v = thetaRenewalDensity`, `q = thetaRenewalMass`,
`ν^{⋆(m+1)} = thetaRenewalPower m`, `Q = thetaRenewalLogKernel` (defined on all of `ℝ` by oriented
convolutions, hence equal to `Q†`), `W = thetaRenewalOddKernel`, `N = thetaRenewalLaplace`,
`D = thetaRenewalDenominator`, `Q̂ = thetaRenewalLogKernelLaplace`, `C = thetaRenewalCosTransform`,
`S = thetaRenewalSinTransform`, `η = thetaRenewalPhase`, `B = thetaWaitingPole`,
`ρ = thetaWaitingRate`, `M = thetaWaitingCDF`, `s = thetaRenewalReflectionProfile`,
`w̃ = thetaRenewalWeightedMoment`, `μ = thetaWaitingTimeLaw`, `Si = thetaSineIntegral`,
`Φ = thetaWaitingPhase`, `k = thetaCuspFullSource`, `g = thetaRenewalExitDensity`,
`H = thetaOneSidedConnection`, `v̂ = thetaRenewalDensityLaplace`, `R = thetaRenewalLevyDensity`.

| Card item | Lean theorem |
|-|-|
| `P` even; `ν = aP - P' = 2π Σ n² e^{(a+1)t-πn²e^t} > 0` | `thetaLogProfile_neg`, `hasDerivAt_thetaLogProfile`, `thetaRenewalIncrement`, `thetaRenewalIncrement_pos` |
| `P'(0) = 0`, `v(0) = a`; `0 < v ≤ a e^{-βt}` | `thetaRenewalIncrement_zero`, `thetaRenewalDensity_zero`, `thetaRenewalDensity_pos`, `thetaRenewalDensity_le` |
| (1) convolution-log kernel, `q < 1/6`, `Q > 0` | `thetaRenewalLogKernel`, `thetaRenewalMass_pos`, `thetaRenewalMass_lt`, `thetaRenewalLogKernel_pos` |
| `v^{⋆m}` bound; `∫ e^{at}Q = -log(1-q) < 1/5` | `thetaRenewalDensityPower_le`, `integral_exp_mul_thetaRenewalLogKernel`, `neg_log_one_sub_thetaRenewalMass_lt` |
| (2) `0 < Q ≤ e^{-βt}(1-e^{-at})/t ≤ a e^{-βt}`, `Q(0) = a` | `thetaRenewalLogKernel_le`, `thetaRenewalLogKernel_le_quarter`, `thetaRenewalLogKernel_zero` |
| real-analytic continuation | `analyticAt_thetaRenewalLogKernel` (holomorphic `thetaRenewalLogKernelC`, `differentiableOn_thetaRenewalLogKernelC`) |
| (3) `Q†(-t) + Q(t) = 2 sinh(at)/t`; `Q†(-t) > 0`; `Q†(-t) ~ e^{at}/t` | `thetaRenewalLogKernel_neg_add`, `thetaRenewalLogKernel_neg_pos`, `tendsto_thetaRenewalLogKernel_neg` |
| even jets `Q^{(2j)}(0) = a^{2j+1}/(2j+1)` | `iteratedDeriv_even_thetaRenewalLogKernel_zero` |
| (3a) positive Volterra law | `thetaRenewal_volterra_law` |
| `W > 0`, `W†(-t) = -W(t)` | `thetaRenewalOddKernel_pos`, `thetaRenewalOddKernel_neg` |
| (3b) `η + S = ∫₀^∞ W sinh(λt)` (Frullani) | `thetaRenewalPhase_add_sin_eq_integral`, `thetaRenewalFrullani_eq` |
| (4) cosh factorization; prefactor analytic and nonvanishing; `‖S‖ < 1/5` | `XiC_two_I_mul_eq_cosh`, `differentiableOn_thetaRenewal_prefactor`, `thetaRenewal_prefactor_ne_zero`, `norm_thetaRenewalSinTransform_lt` |
| (5) upper/lower half zero levels `±iπ/2` | `XiC_two_I_mul_eq_zero_iff`, `XiC_two_I_mul_eq_zero_iff_of_im_neg`, `im_thetaRenewalPhase_mem`, `cosh_eq_zero_iff'` |
| (6) real-frequency amplitude–phase law | `XiC_two_mul_ofReal_eq`, `thetaRenewalPhase_I_mul` |
| (7) `D = (λ-a)L = c - ν̂ = c e^{-Q̂}`, no zeros on `Re λ ≥ -a` | `thetaRenewalDenominator_eq_laplace`, `thetaRenewalDenominator_eq`, `thetaRenewalLogKernelLaplace_eq`, `thetaRenewalDenominator_eq_exp`, `thetaRenewalDenominator_ne_zero` |
| (8) `Ξ(2iλ) = (a+λ)D(λ) + (a-λ)D(-λ)`; `Q̂ = C - S`; `e^{2η} = (a+λ)/(a-λ)` | `thetaRenewal_two_ended`, `thetaRenewalLogKernelLaplace_eq_cos_sub_sin`, `cexp_two_mul_thetaRenewalPhase` |
| (10) `ρ ≥ (1-e^{-βt})B > 0`; `M = tρ`; `M(0)=0`, `M → 1`, `M` strictly increasing | `thetaWaitingRate_ge`, `thetaWaitingRate_pos`, `thetaWaitingCDF_eq_mul_rate`, `thetaWaitingCDF_zero`, `tendsto_thetaWaitingCDF_atTop`, `strictMonoOn_thetaWaitingCDF` |
| `μ` probability law, `s = μ((t,∞))`, `M = μ([0,t])` | `isProbabilityMeasure_thetaWaitingTimeLaw`, `thetaWaitingTimeLaw_Ioi`, `thetaWaitingTimeLaw_Icc` |
| `M`, `s` even and real-analytic; `ρ`, `M'` odd | `thetaWaitingCDF_neg`, `thetaRenewalReflectionProfile_neg`, `analyticAt_thetaWaitingCDF`, `thetaWaitingRate_neg`, `deriv_thetaWaitingCDF_neg` |
| (11) `ρ = μ([0,t])/t`, `W = μ((t,∞))/t` | `thetaWaitingRate_eq_measure`, `thetaRenewalOddKernel_eq_measure` |
| (12) `w̃ = τv + v⋆w̃`, `w̃' = v + τv' + aw̃ + v'⋆w̃`, `M' = e^{-at}[a - v - tv' - v'⋆w̃] > 0`; `v < a`, `v' < 0` | `thetaRenewalWeightedMoment_law`, `hasDerivAt_thetaRenewalWeightedMoment`, `hasDerivAt_thetaWaitingCDF`, `deriv_thetaWaitingCDF_pos`, `thetaRenewalDensity_lt_quarter`, `deriv_thetaRenewalDensity_neg` (Leibniz rule `hasDerivAt_volterraConv`) |
| tail bound; `∫ e^{σt} μ(dt) < ∞` for `σ < a` | `thetaRenewalReflectionProfile_le`, `lintegral_exp_mul_thetaWaitingTimeLaw_lt_top`, `integrableOn_exp_mul_deriv_thetaWaitingCDF` |
| `Si` entire and odd | `differentiable_thetaSineIntegral`, `thetaSineIntegral_neg`, `mul_thetaSineIntegralDeriv` |
| (13) `Φ = ∫ (s/t) sin(zt) = arctan(z/a) + ∫ Q sin(zt)`; holomorphic on the strip | `thetaWaitingPhase_eq_oddKernel`, `thetaWaitingPhase_eq_arctan_add`, `neg_I_mul_thetaRenewalPhase_I_mul`, `differentiableOn_thetaWaitingPhase` |
| (14) `Φ' = ∫ s cos(zt) = ∫ sin(zt)/z μ(dt)`, `Φ'(0) = ∫ t μ(dt) > 0` | `hasDerivAt_thetaWaitingPhase`, `hasDerivAt_thetaWaitingPhase_eq_expectation`, `hasDerivAt_thetaWaitingPhase_zero`, `integral_id_thetaWaitingTimeLaw`, `integral_id_thetaWaitingTimeLaw_pos` |
| `Φ'` positive definite on `ℝ`, Fourier transform of `s(\|t\|)/2` | `sum_sum_mul_conj_mul_thetaWaitingPhaseSlope`, `sum_sum_mul_conj_mul_thetaWaitingPhaseSlope_nonneg`, `thetaWaitingPhaseSlope_eq_fourier`, `thetaWaitingPhaseSlope_eq_integral_abs`, `hasDerivAt_thetaWaitingPhase_ofReal` |
| (15) `Ξ(2z) = 2c(a²+z²)^{1/2} e^{-∫Q cos} cos Φ`; branch analytic, `= a` at `0`; prefactor `≠ 0`; zeros `Φ = ±π/2` | `XiC_two_mul_eq_cos_thetaWaitingPhase`, `differentiableOn_one_sixteenth_add_sq_cpow`, `one_sixteenth_add_sq_cpow_zero`, `thetaWaitingPhase_prefactor_ne_zero`, `XiC_two_mul_eq_zero_iff_of_re_pos`, `XiC_two_mul_eq_zero_iff_of_re_neg` |
| (16) `π/2 - Φ(u) = lim ∫₀^T ρ sin(ut) = ∫ (π/2 - Si(us)) μ(ds)`; range `(-1/5, π/2+1/5)`; `Ξ(2u) = 0 ⟺ (16) = 0`; `O_N(u^{-N})` | `tendsto_integral_thetaWaitingRate_mul_sin`, `thetaWaitingPhaseGap_eq_expectation`, `thetaWaitingPhaseGap_mem`, `XiC_two_mul_ofReal_eq_zero_iff`, `exists_abs_thetaWaitingPhaseGap_le` (Dirichlet `connes_dirichlet_integral`, `integral_exp_mul_sin_div_eq_arctan`, Schwartz decay `exists_pow_mul_norm_XiC_le`) |
| (17) `Q'(0) = a²/2 - P''(0)/c = (5-π²c⁸)/32 < 0`; `P''(0)/c = -1/8 + π²c⁸/32` | `deriv_thetaRenewalLogKernel_zero`, `deriv_thetaRenewalLogKernel_zero_eq_seam`, `deriv_thetaRenewalLogKernel_zero_neg`, `iteratedDeriv_two_thetaLogProfile_zero` |
| modular ODE along renewal time; every seam jet of `Q` (and of `P/c`, `ν/c`) in `ℚ[πc⁴]` | `hasDerivAt_thetaLogProfile_drift`, `thetaRenewalIncrement_eq_drift`, `thetaRenewalScaleCoord_zero`, `thetaRenewalMomentKernel_jet_recursion`, `iteratedDeriv_thetaRenewalLogKernel_zero_mem`, `iteratedDeriv_thetaLogProfile_zero_mem`, `iteratedDeriv_thetaRenewalIncrement_zero_mem` |
| (18) `v'(2x) = -e^{x/2}k(x)/(2c) < 0`; `g` probability density with mean `q/a < 2/3` | `hasDerivAt_thetaRenewalDensity_two_mul`, `thetaCuspFullSource_eq_thetaMoment`, `thetaRenewalDensity_eq_thetaMoment`, `integral_thetaRenewalExitDensity`, `integral_mul_thetaRenewalExitDensity`, `integral_mul_thetaRenewalExitDensity_lt` |
| (19) `Ξ(2z) = 2ac ∫ e^{-at} cos(zt) g(t) dt` | `XiC_two_mul_eq_exitDensity`, `thetaCuspFullSource_half_eq_exitDensity` |
| (19a) `H(2z) = ac E_g[e^{-(a-iz)T}] = (a-iz)D(-iz) + icz`; seam terms cancel | `thetaOneSidedConnection_two_mul_eq_exitDensity`, `thetaOneSidedConnection_two_mul_eq_denominator`, `thetaOneSidedConnection_add_eq_two_ended` |
| (20) `E[e^{-sY}] = (1-q)/(1-v̂(s)) = exp ∫(e^{-st}-1)R`; `D(λ) = c(1-q)/E[e^{-(a+λ)Y}]`; `s = e^{-at}(1+tR)` | `integral_cexp_compoundGeometric`, `cexp_integral_thetaRenewalLevyDensity`, `thetaRenewalDenominator_eq_compoundGeometric`, `thetaRenewalReflectionProfile_eq_levy`, `exists_compoundGeometric` |
| (21) `e^{-xt}ν` strictly decreasing, `Re D ≥ c(1-q)`, `Im D > 0`; quadrants of `D(±λ)` | `strictAntiOn_exp_mul_thetaRenewalIncrement`, `re_thetaRenewalDenominator_ge`, `im_thetaRenewalDenominator_pos`, `thetaRenewalDenominator_quadrant`, `thetaRenewalDenominator_conj` (general: `integral_mul_sin_pos_of_strictAntiOn`) |
| (22) `0 < Im S(λ) < 1/5`; `0 < Re[Φ(z) - arctan(z/a)] < 1/5` | `im_thetaRenewalSinTransform_mem`, `im_thetaRenewalLogKernelLaplace`, `re_thetaWaitingPhase_sub_arctan_mem` |

Proof-route notes. (3) is proved by a Volterra uniqueness argument for the even profile
`e^{-at} + tQ(t)` instead of Laplace coefficient comparison; the even-jet formula is then a
corollary. The `O_N(u^{-N})` decay in (16) is proved from the amplitude–phase law, the elementary
bound `|x| ≤ 3|sin x|` on `(-1/5, π/2 + 1/5)` and the Schwartz decay of `Ξ` (the Fourier transform of
the Schwartz theta source), instead of integrating by parts against derivatives of `ρ`. Statement (20)
is proved for every probability space carrying a geometric `N` independent of independent increments
with density `v/q`, and such a space is constructed.
