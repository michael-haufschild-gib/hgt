# Causal-germ cancellation and the translation ideal at the theta port — Lean certificate

- **Paper card:** `theta-causal-germ-translation-ideal-phase-selection.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.HalfLineTransformCalculus` (half-line sine
  transforms, jet expansion, (5), (5a)), `GaloisForLFunctions.RHTower.ThetaCausalGermPort` ((1)–(5a),
  sharp receiver), `GaloisForLFunctions.RHTower.ThetaPrimeMomentPorts` ((8)–(17), gauge ports (22),
  (10) for every gauge, wall symbol (20)), `GaloisForLFunctions.RHTower.ThetaTranslationIdealSources`
  ((6), (7), (8), (9) as source identities), `GaloisForLFunctions.RHTower.XiWallLogDerivativeCones`
  ((18), (19), (19a), (33)–(35), height-8 cone), `GaloisForLFunctions.RHTower.ThetaPrimePacketPorts`
  ((20)–(32), phase-aperture classification, minimum-width geometry),
  `GaloisForLFunctions.RHTower.ThetaPacketHarmonicObstructions` ((36)–(38), two-scale theorem,
  three-scale height-8 failure with prime scales), `GaloisForLFunctions.HTGeometry.FiniteRankPhaseMoments`
  ((39) and its sharpness); corpus `CausalThetaHalfLaplace` (`H`), `ThetaHalfLinePortGauge`
  (`X`, `#`, `X# = X`), `XiRelativeResolventTrace` (`X'/X` as the reciprocal-square resolvent),
  `XiReciprocalSquareSecondMomentRadius` (`γ² > 599/4`), `ThetaHalfLinePortCrossings` (`exists_simpleCrossing_above`:
  two-sign simple critical zeros), `VolterraConvolutionCalculus` (`iteratedDeriv_id_mul_real`),
  `ThetaCommutatorKernelInertia` (`exists_prime_log_near`, from the
  prime number theorem)
- **Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `lake env lean` audit clean on all eight modules;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`.
  The only hypotheses are the card's own quantifiers: the explicit regularity class of the causal
  correction (`CausalCorrection a`: smooth, exponential moment in a strip, all derivatives of `k + a`
  integrable and vanishing at `+∞`), the order hypotheses of the no-go statements, and the packet
  data (weights, scales, gauges).

Dictionary: `k = thetaCuspFullSource`, `H = thetaHalfLaplace`, `X = thetaSymmetrizedPort`
(`X(w) = XiC(iw)`), `F#(w) = halfPortReflect F w`, `Q_a = causalCorrectionTransform a`,
`E_a = causalPort a`, `D_a = causalPortImbalance a`, `c_a = causalPortSine a` (`halfLineSine`),
`D_E = portImbalance E`, `j = translationOddPart`, `U = logTimeClock`, `T_h = logTimeShift`,
`g_p = primeDeletedSource`, `A_p = primeDeletionSymbol`, `A_p' = primeDeletionSymbolDeriv`,
`E_{p,μ} = primeGaugePort p μ`, `E_p^cov = primeCovariantPort` (`μ = 0`),
`E_p = primeMomentPort` (`μ = log p`), `z = X'/X = thetaPortLogDeriv`, `A_R = packetSymbol`,
`E_{R,μ} = packetGaugePort`, `B_R(β) = packetPhase`, `b_n = unitPhaseMoment`.

| Card item | Lean theorem |
|-|-|
| (1) `E_a + E_a# = X` | `causalPort_add_reflect` |
| (2) `E_a(iγ) = i c_a(γ)` at a real Xi zero | `causalPort_mul_I` |
| (3) `D_a = 2Re(E_a X̄) - |X|²`, `∂_α D_a(α + iγ)|₀ = -2c_a(γ)Ξ'(γ)` | `causalPortImbalance_eq`, `hasDerivAt_causalPortImbalance` |
| (4) all-order causal-germ theorem (zero-neighbourhood and collar forms) | `causalPort_even_jets_eq_zero`, `causalPort_even_jets_eq_zero_of_collar` |
| (5) `c_a(γ) = (-1)^m f^{(2m)}(0)γ^{-2m-1} + o(γ^{-2m-1})`, fixed eventual sign | `HalfLineTransformCalculus`: `halfLineSine_eq_jet`, `tendsto_pow_mul_halfLineSine`, `eventually_sign_halfLineSine` |
| analytic case: the corrected germ is odd | `causalPort_odd_germ` (`eventually_neg_of_even_iteratedDeriv_eq_zero`) |
| (5a) all even jets vanish ⇔ `c_a = O(γ^{-N})` for every `N` | `causalPort_even_jets_iff_rapid` (`even_jets_eq_zero_iff_rapid`) |
| sharp receiver `a_* = -k + 2uk`: `E_{a_*} = X/2 + X'`, normal derivative `2Ξ'(γ)² > 0` | `causalCorrection_causalReceiverCorrection`, `causalPort_causalReceiverCorrection`, `hasDerivAt_causalPortImbalance_receiver` |
| (6) `Q_a = -X Σ c_j sinh(h_j w)`, vanishing at every Xi zero; `a(0) = 0`; unchanged raw derivative at simple critical zeros | `integral_cexp_mul_translationOddPart`, `causalCorrectionTransform_translation`, `causalCorrectionTransform_translation_eq_zero`, `translationOddPart_zero`, `hasDerivAt_causalPortImbalance_translation` |
| a finite spectral limit of such corrections at an Xi zero is zero | `translation_limit_eq_zero_of_zero` |
| (7) `[U, T_h] = -hT_h`; its odd source part is a translation polynomial | `logTimeClock_shift_commutator`, `oddPart_logTimeClock_commutator` |
| (8) `Y_p = [1 - r cosh(Lw)]X`; `a_p` cancels every even jet | `integral_cexp_mul_primeDeletedSource`, `iteratedDeriv_even_primeMomentCorrection` |
| (9) `E_p = X/2 + Y_p'` | `causalPort_primeMomentCorrection`, `primeMomentPort_eq` |
| (10) `E_p(iγ) = -i[1 - r cos(Lγ)]Ξ'(γ)`, normal derivative `2[1 - r cos(Lγ)]Ξ'(γ)² > 0` (every real gauge) | `primeGaugePort_mul_I`, `hasDerivAt_primeGaugePort_imbalance`, `primeGaugePort_normal_pos` |
| at a zero of `X` (on or off the line) `E_p# = -E_p` and `D = 0` | `halfPortReflect_eq_neg_of_zero`, `portImbalance_eq_zero_of_zero`, `primeGaugePort_reflect_of_zero` |
| the whole right half-plane fails | `eventually_primeMomentPort_imbalance_neg` |
| (11) center curvature condition, satisfied for all large `p` | `primeMomentPort_center_condition`, `eventually_primeMomentPort_center` |
| (11a) wall values and the wall shear failure | `primeDeletionSymbolReal_half`, `primeDeletionSymbolRealDeriv_half`, `primeMomentReal_half`, `exists_primeMomentPort_imbalance_neg`, `eventually_exists_primeMomentPort_imbalance_neg` |
| (12) `E_p → X/2 + X'` locally uniformly on `|Re w| < 1/2` | `tendstoUniformlyOn_primeMomentPort` |
| (13) `E_p^cov + (E_p^cov)# = X`; the order difference is `A_p'X` | `primeGaugePort_add_reflect`, `halfPortReflect_primeGaugePort` |
| (14) `r cosh(L/2) = (1 + p⁻¹)/2 < 1`, `D_p^cov(α) > 0` on `(0, 1/2]` | `rpow_mul_cosh_le`, `one_add_inv_div_two_lt_one`, `primeCovariantPort_imbalance_ofReal_pos` |
| (15) `D = 2|X|² Re[(E - X/2)/X]`, `D_{p,μ} = 2|X|² Re[A_p z + (μ/L)A_p']` | `portImbalance_eq_re_div`, `primeGaugePort_imbalance_eq` |
| `|1 - A_p(α + iβ)| ≤ r cosh(Lα) ≤ (1 + p⁻¹)/2 < 1` | `norm_one_sub_primeDeletionSymbol_le`, `norm_one_sub_primeDeletionSymbol_lt_one` |
| (16) phase-aperture criterion | `primeCovariantPort_imbalance_pos` |
| (17) critical-boundary normal derivative | `hasDerivAt_primeCovariantPort_imbalance` |
| (18) `z(w) = w Σ_q 1/(w² + ζ_q²)`, absolutely convergent | `thetaPortLogDeriv_eq`, `summable_wallTerm` |
| `X(1/2 + ih) ≠ 0` for every real `h` | `thetaSymmetrizedPort_wall_ne_zero` |
| (19), (19a), (33) termwise cone; (35) `Im z_h > k_h Re z_h > 0` for `h = 2, 4, 6` (`k = 11/4, 15/4, 4`), `h = 8` (`k = 2`) | `wallTerm_cone`, `wallLogDeriv_cone`, `thetaPortLogDeriv_cone_two`, `thetaPortLogDeriv_cone_four`, `thetaPortLogDeriv_cone_six`, `thetaPortLogDeriv_cone_eight` |
| `Re z₀/|z₀| < 4/√137 < 1/2` | `thetaPortLogDeriv_two_aperture` |
| (20) exact wall symbol, and its steered value `1 - [e^{iθ} + p⁻¹e^{-iθ}]/2` | `primeDeletionSymbol_wall`, `primeDeletionSymbol_wall_of_phase` |
| phase steering `|β_p - h| ≤ π/L`, `e^{iLβ_p} = e^{iθ}` | `exists_wall_phase` |
| (21) `Re[A_p(1/2 + iβ_p)z(1/2 + iβ_p)] → Re z₀ - |z₀|/2 < 0` | `exists_prime_wall_steering`, `thetaPortLogDeriv_two_re_sub_half_norm_neg` |
| (21) conclusion: `D_p^cov < 0` in the open strip for all large `p`; same for clock-after-deletion | `exists_primeCovariantPort_threshold`, `exists_primeMomentPort_threshold` |
| phase-aperture classification: cofinal strip order with wall multiplier `1 - c e^{iLβ} + o(1)` forces `Re z_h ≥ c|z_h|`; at `w₀` this forces `c < 4/√137` | `strip_order_forces_phase_aperture`, `phase_aperture_lt_of_strip_order`, `portImbalance_wall_nonneg` |
| (22), (23) gauge port and its wall expansion (single prime and packets) | `primeGaugePort`, `packetGaugePort_unit`, `packetSymbol_wall`, `primeDeletionSymbolDeriv_wall` |
| (24) one prime threshold for every real gauge at once | `exists_primeGaugePort_threshold` |
| deterministic wall-defect bound behind (24), (30) | `wall_re_le` |
| continuity moves a wall defect into the open strip | `exists_interior_of_wall_neg`, `continuous_packetGaugePort`, `continuous_portImbalance` |
| (26) packet symbol and port, `E + E# = X`, `D = 2|X|²Re[Az + (μ/L)A']` | `packetSymbol`, `packetGaugePort`, `packetGaugePort_add_reflect`, `packetGaugePort_imbalance_eq` |
| (27) both wall packets are `1 + o(1)` for `|β - 2| ≤ π/L_R`; reverse-frequency packets `o(1)` | `eventually_packetPhase_near_one`, `norm_packetPhase_sub_le`, `norm_scale_weighted_sub_le`, `norm_packet_negative_sum_le` |
| (28) wall expression within `η(1 + |μ|)` of `z - e^{iL_Rβ}(z + μ)/2` | `eventually_lognarrow_wall_approx` |
| log-narrow packets fail for every gauge | `eventually_lognarrow_packet_defect` |
| (29), (30) coherence threshold, uniform in the gauge (general height; height 2) | `exists_packet_wall_threshold`, `eventually_packet_threshold`, `eventually_packet_coherence_defect` |
| (31) `limsup |B_R(2)| ≤ 2a₀/b₀ < 8/11` under cofinal order | `eventually_norm_packetPhase_lt_of_order`, `thetaPortLogDeriv_two_threshold_lt` |
| `|B_R(2)| ≥ Re B_R(2) ≥ cos Δ_R` | `cos_le_re_phase_sum`, `cos_le_re_packetPhase` |
| (32) `liminf Δ_R ≥ arccos(2a₀/b₀) > arccos(8/11)` | `eventually_arccos_le_width_of_order`, `eventually_width_ge_of_order`, `arccos_eight_elevenths_lt`, `eventually_width_gt_arccos_of_order` |
| minimum width: `|B(2)| = cos Δ` iff all weight at the two endpoints with equal masses | `norm_phase_sum_eq_cos_iff` |
| (36) thresholds `8/11, 8/15, 1/2` | `wall_aperture_thresholds` |
| (37) `|B(2n)|² = cos²(nΔ) + (1 - 2v)² sin²(nΔ) ≥ cos²(nΔ)` | `packetPhase_two_scale`, `sq_norm_two_point_phase`, `abs_cos_le_norm_two_point_phase` |
| (38) three-harmonic cosine inequality | `three_harmonic_cos` |
| two-scale theorem (quantitative and sequence forms, every gauge, `Δ_R = o(L_R)`) | `exists_two_scale_packet_threshold`, `eventually_two_scale_packet_defect` |
| balanced three-scale packet: `B(2n) = (1 + 2cos(nπ/2))/3`, amplitudes `1/3` at `2, 4, 6`, `B(8) = 1` | `packetPhase_three_scale_ideal`, `three_scale_ideal_amplitudes` |
| three-scale repair fails at height 8, with prime scales supplied by the prime number theorem | `exists_three_scale_packet_failure`, `norm_packetPhase_sub_packetPhase_le` |
| (39) `max_{1≤n≤m}|b_n| ≥ 1/m` (Toeplitz kernel from `∏(x - u_j)`) | `sum_coeff_mul_unitPhaseMoment_eq_zero`, `exists_one_div_le_norm_unitPhaseMoment` |
| sharpness: omitted `(m+1)`-st root gives `b_n = -u_*^n/m`, `b_{m+1} = 1` | `unitPhaseMoment_omitted_root`, `norm_unitPhaseMoment_omitted_root` |

The three-scale ideal packet is the `m = 3` omitted-root configuration rotated to phases
`-i, 1, i`: `three_scale_ideal_amplitudes` gives `b_n = -(-1)^n/3` for `n = 1, 2, 3` and `b_4 = 1`.
