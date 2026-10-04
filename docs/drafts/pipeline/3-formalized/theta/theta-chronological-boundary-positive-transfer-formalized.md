# Positive transfer and singular deconvolution of theta Euler boundary currents — Lean certificate

- **Paper card:** `theta-chronological-boundary-positive-transfer.md`
- **Lean modules (umbrella `GaloisForLFunctions.RHTower`):**
  - `ThetaChronologicalCutoffCurrent`: Gaussian polynomial atoms `ψ_Q = e^{3y}Q(e^{2y})e^{−πe^{2y}}` closed under `∂`, uniform lattice bounds, `C = Σ μ(d)/d φ(y+log d)` (14), every derivative of `C` bounded/continuous, Mellin law of log-shift series, `ℒ(C^{(j)})(z) = −(−z)^j G(z)/ζ(1+z)`.
  - `ThetaChronologicalPositiveTransfer`: `D`, `T`, kernel mass, positivity/forwardness/continuity of `T`, Laplace law of `T` (Fubini + beta integral), `A`, (6), (7), the pointwise identity (4), `H` holomorphic and zero-free with pole transport (8), three-frame identity and genuine pole of the causal continuation (9).
  - `ThetaChronologicalCausalJumps`: right-continuity, continuity off the sites, left limits and the jump (10), coefficient recovery (11), seed initial value (12), `b = J + c` with `c` Lipschitz on every `(−∞, X]` (13), regular-transport obstruction.
  - `ThetaChronologicalSingularDeconvolution`: atomic measures, `ν_σ` with its Jordan decomposition (15), `C_σ = ν_σ * φ_σ` (16), Fourier injectivity of convolution by `φ_σ` and atom readout, singular readout (17), unit dipoles (18), total variation (19).
  - `ThetaChronologicalPacketResolution`: packets (20), compact-family resolution failure (21), two-atom estimate (22), `W^{1,1}` bound (23), resolution cost (24), weighted adjacent ratio, the counting remark.
- **Corpus inputs used (already formalized):** `integral_cexp_mul_cofinalBoundaryProfile` (1), `integral_cexp_mul_movingCuspDualLimit` + `XiC_I_mul_eq_xi_half_add` (2), `causalTailMellin_add_correction`, `thetaHalfLaplace_add_neg`, `re_mul_thetaHalfLaplace_neg_pos`, `thetaHalfLaplace_ne_zero_of_riemannZeta_eq_zero`, `riemannHypothesis_iff_causalMobiusThetaTail_subpower` (9), `HedenmalmThetaSource.thetaCuspFullSource_pos` (`k(0) > 0`), `eq_zero_of_fourier_eq_zero` (Fourier uniqueness), `Measure.ext_of_charFun`, `HTGeometry.integral_norm_translation_le`, `LSeries_squarefree_mul_riemannZeta_two_mul`, `prime_between` (PNT), `Chebyshev.pi_le_log4_mul_div`, `Chebyshev.theta_le_log4_mul_x`, `Sieve.abs_window_squarefree_sub_le`, `Sieve.sum_sqrtInv_squarefree_le/ge`, `cofinalBoundaryProfile_takes_both_signs`, `movingCuspDualLimit_takes_both_signs`.
- **Verification (2026-10-04):** targeted `lake build --old` of each new module; final `lake env lean` audit of each source with empty output; `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 249 declarations of the five modules; no `sorry`, no axiom, no heartbeat options.
- **Hypotheses:** only the card's quantifiers (Mellin parameters in the stated half-planes, `σ > 0` or `σ ≥ 0`, bounded continuous inputs of `T`, `m ≥ 1`, compact `K ⊂ L¹`, `0 < t`, `0 < t < 1`, hypothetical zeros `1/2 < Re ρ < 1`).

Dictionary: `C = cofinalBoundaryProfile`; `R = movingCuspDualLimit`; `k = thetaCuspFullSource`; `h = thetaSeedAtom`; `φ = gaussPolyAtom cutoffAtomPoly`; `G = commutatorGammaFactor`; `D = chronoDerivOp`; `DC = cutoffTransferSource`; `T = positiveTransfer`; `A = transferMultiplier`; `H = transferMultiplierH`; `B = causalMobiusThetaTail`; `ℒ_tB = causalTailMellin`; `K = thetaHalfLaplace`; `E = causalFrameCorrection`; `b = causalLogTail`; `ν_σ = deconvMeasure σ` (`deconvPos σ`, `deconvNeg σ`); `φ_σ = weightedCutoffAtom σ`; `C_σ = weightedCutoffCurrent σ`; `(μ₁ − μ₂) * f = signedMeasureConv μ₁ μ₂ f`; `λ_{q,σ} = packetJordan σ q`.

| Card item | Lean theorem |
|-|-|
| **(1)** `C = −2πe^{3y}Σμ(d)d²e^{−πd²e^{2y}}`, `ℒC = −G/ζ(1+z)` | `cofinalBoundaryProfile`, `thetaFluxTerm_eq`, `integral_cexp_mul_cofinalBoundaryProfile` (corpus) |
| **(2)** `ℒR(w) = ξ(w+1/2)/ζ(w−1/2)`, `Re w > 3/2` | `integral_cexp_mul_movingCuspDualLimit`, `XiC_I_mul_eq_xi_half_add`; shifted form `integral_cexp_mul_reflectedCurrent` |
| **(3)** `T` defined; absolute convergence for bounded `f`; kernel mass `ζ(2)/π`; positive forward dilation | `positiveTransfer`, `summable_positiveTransfer_terms`, `abs_forwardDilationAverage_le`, `positiveTransfer_one`, `positiveTransfer_nonneg`, `positiveTransfer_congr_forward`, `forwardDilationShift_nonneg` |
| `C, C', C''` (all derivatives) bounded and continuous; `DC` bounded continuous | `exists_abs_iteratedDeriv_cofinalBoundaryProfile_le`, `continuous_iteratedDeriv_cofinalBoundaryProfile`, `contDiff_cofinalBoundaryProfile`, `exists_abs_cutoffTransferSource_le`, `continuous_cutoffTransferSource` |
| `T` of a bounded continuous function is continuous | `continuous_positiveTransfer` |
| `ℒ(DC) = (z+1)(z+2)ℒC` | `integral_cexp_mul_cutoffTransferSource` (via `integral_cexp_mul_iteratedDeriv_cofinalBoundaryProfile`) |
| **(5)** `ℒ(Tf) = A ℒf`, `A = (2π)^{−1}ζ(z+2)∫₀¹t^{z/2}(1−t)^{−1/2}dt = ζ(z+2)Γ((z+2)/2)/(2√πΓ((z+3)/2))` | `integral_cexp_mul_positiveTransfer`, `forwardDilationAverage_laplace`, `forwardDilationBeta_eq`, `transferMultiplier_eq_beta`, `integral_cexp_mul_positiveTransfer_eq` |
| **(6)** `ξ(z+2) = A(z)(z+1)(z+2)G(z)` | `xi_add_two_eq_transferMultiplier` |
| **(7)** `ℒ(e^{3·/2}R) = ξ(z+2)/ζ(1+z) = ℒ(−TDC)` | `integral_cexp_mul_reflectedCurrent`, `integral_cexp_mul_neg_positiveTransfer_cutoff` |
| **(4)** `e^{3y/2}R(y) = −T(DC)(y)` for every `y` | `exp_mul_movingCuspDualLimit_eq_neg_positiveTransfer` |
| **(8)** `H = A(z+1)(z+2) = ξ(z+2)/G` holomorphic, zero-free on `Re z > −1` | `transferMultiplierH_eq`, `differentiableOn_transferMultiplierH`, `transferMultiplierH_ne_zero` |
| **(8)** pole location and order unchanged between the two currents | `meromorphicOrderAt_reflected_eq_cutoff` |
| **(8)** `D` has no positivity-preserving sign | `chronoDerivOp_gaussian_neg` |
| **(8)** cusp sign changes of both currents | `cofinalBoundaryProfile_takes_both_signs`, `movingCuspDualLimit_takes_both_signs` (corpus) |
| half-line identity `ℒ_tB = K(1/ζ(w+1/2) − 1) − E` | `causalTailMellin_eq_frame`, `causalFrameCorrection`, `differentiable_causalFrameCorrection` |
| **(9)** three-frame identity `ℒ_tB = −[K/G(w−1/2)]ℒC(w−1/2) − K − E` | `causalTailMellin_three_frame` |
| **(9)** `K + K(−·) = ξ(·+1/2)`, `Re(wK(−w)) > 0`, `K ≠ 0` at right-half zeros | `thetaHalfLaplace_add_neg`, `re_mul_thetaHalfLaplace_neg_pos`, `thetaHalfLaplace_ne_zero_of_riemannZeta_eq_zero` (corpus) |
| **(9)** the correction cannot hide an off-line pole (pole of exact order `ord_ρ ζ`) | `causalTailMellin_eq_continuation`, `meromorphicOrderAt_causalFrameContinuation`, `meromorphicOrderAt_riemannZeta_pos_ne_top` |
| **(9)** subpower bound is an exact RH criterion | `riemannHypothesis_iff_causalMobiusThetaTail_subpower` (corpus) |
| **(10)** `b` right-continuous; continuous off `log m`; jump `−k(0)μ(m)/√m` | `continuousWithinAt_causalLogTail_Ici`, `continuousAt_causalLogTail`, `tendsto_causalLogTail_left`, `causalLogJump_eq` |
| `k(0) > 0`; jump nonzero exactly at squarefree `m` | `HedenmalmThetaSource.thetaCuspFullSource_pos`, `causalLogJump_ne_zero_iff`, `not_continuousAt_causalLogTail` |
| **(11)** `μ(m) = −√m[b(log m+) − b(log m−)]/k(0)` | `moebius_eq_of_causalLogJump` |
| **(12)** `B(t) = h(−log t)`, `0 < t < 1` | `causalMobiusThetaTail_eq_seed`, `mulConvWeight_moebiusInvSqrt_invSqrt` |
| **(13)** singular part of `db/dx` is `−k(0)Σμ(m)/√m δ_{log m}`: `b = J + c`, `J` the pure jump function, `c` Lipschitz on each `(−∞,X]` | `causalLogTail_eq_jump_add_regular`, `causalJumpPart`, `causalJumpPart_eq_of_mem`, `causalJumpPart_eq_zero_of_neg`, `exists_lipschitzOnWith_causalRegularPart`, `continuous_causalRegularPart` |
| regular-transport obstruction: `y ↦ ∫P(∂)C(y+a)dν(a)` continuous for every finite complex Borel measure (finite complex combination of finite measures); never equals `b`; nor does `T` with finite-order derivatives | `continuous_regularCutoffObservation`, `regularCutoffObservation_sum_ne_causalLogTail`, `positiveTransfer_derivatives_ne_causalLogTail` |
| **(14)** `C(y) = Σμ(n)/n φ(y+log n)` | `cofinalBoundaryProfile_eq_logShiftSeries` |
| **(15)** finite signed measure `ν_σ` | `deconvJordan`, `deconvMeasure`, `deconvMeasure_eq`, `deconvPos_isFinite`, `deconvNeg_isFinite` |
| **(16)** `C_σ = ν_σ * φ_σ`, both in `L¹` | `signedMeasureConv_deconv_eq`, `integrable_weightedAtom`, `integrable_weightedCutoffCurrent` |
| Fourier transform of `φ_σ` is `−G(σ+it) ≠ 0`; convolution by `φ_σ` injective on finite signed measures; `C_σ` determines `ν_σ` | `integral_cexp_mul_weightedCutoffAtom`, `signedMeasureConv_weightedCutoffAtom_injective`, `eq_deconvMeasure_of_conv` |
| atoms: `μ(n) = n^{1+σ}ν_σ({−log n})` | `deconvMeasure_singleton`, `moebius_eq_rpow_mul_deconvMeasure` |
| **(17)** `B(t) = ∫_{a<−log t} e^{−(σ+1/2)a}k(−a−log t)dν_σ(a)`, atomwise | `causalMobiusThetaTail_eq_deconv_readout`, `deconvWeight_mul_causalReadoutKernel` |
| **(18)** `‖λ_n‖_TV = 2`, `‖λ_n * φ_σ‖₁ → 0`; no bounded inverse | `unitDipole_totalVariation`, `tendsto_unitDipole_conv_L1`, `not_exists_bounded_inverse_unitDipole` |
| **(18)** same ratio → 0 with coefficient weights `n^{−1−σ}` | `tendsto_weighted_adjacent_ratio` |
| **(19)** `‖ν_σ‖_TV = Σμ(n)²/n^{1+σ} = ζ(1+σ)/ζ(2+2σ)`, `σ‖ν_σ‖_TV → 1/ζ(2)`, `‖ν_σ‖_TV → ∞` | `deconvMeasure_totalVariation_univ`, `tsum_moebius_sq_rpow_eq`, `tendsto_mul_tsum_moebius_sq_rpow`, `tendsto_tsum_moebius_sq_rpow_atTop` |
| **(20)** `m = 2q`, `p` least prime `> m`, `μ(m) = 1`, `μ(p) = −1`, `p/m → 1` (PNT), `δ_q → 0`; `λ_{q,σ}` a literal two-atom submeasure of `ν_σ`, `‖λ_{q,σ}‖_TV = A + B` | `packetPrime_le`, `two_mul_lt_packetPrime`, `moebius_two_mul_of_prime`, `moebius_packetPrime`, `tendsto_packetPrime_div`, `tendsto_packetGap`, `deconvMeasure_packet_atoms`, `packetJordan`, `packet_totalVariation` |
| **(21)** every compact `K ⊂ L¹`: `sup_K ‖λ_{q,σ}*ψ‖₁/‖λ_{q,σ}‖_TV → 0`; uniform translation continuity on compacts | `packet_conv_le_of_isCompact`, `eventually_forall_norm_realL1Shift_sub_lt`, `norm_twoShift_eq` |
| **(22)** `‖λ*ψ‖₁ ≤ |A−B|‖ψ‖₁ + B‖ψ − ψ(·+δ)‖₁` | `integral_abs_twoAtom_le` |
| **(23)** `|A−B|/(A+B) = tanh((1+σ)δ/2) ≤ (1+σ)δ/2`; ratio `≤ δ/2((1+σ)‖ψ‖₁ + ‖ψ'‖₁)` | `exp_sub_exp_neg_le_mul`, `rpow_neg_sub_div_add_le`, `twoAtom_ratio_le` |
| **(24)** `‖ψ_q'‖₁ ≥ 2c/δ_q − (1+σ)M` | `deriv_norm_ge_of_separation` |
| counting: `O(X/log X)` packets vs `X/ζ(2) + o(X)` squarefree sites | `isBigO_card_packetPrimes`, `isLittleO_squarefreeCount`, `abs_squarefreeCount_sub_le`, `tendsto_card_packetPrimes_div_squarefreeCount` |
| counting: half-power packet weight `O(√X/log X)` vs order `√X` | `isBigO_packetHalfWeight`, `sum_primesLE_rpow_neg_half_le`, `sum_primesLE_log_mul_rpow_neg_half_le`, `squarefreeHalfWeight_le`, `eventually_squarefreeHalfWeight_ge`, `tendsto_packetHalfWeight_div_squarefreeHalfWeight` |
