# Theta quantile action is an electrical potential kernel — Lean certificate

- **Paper card:** `theta-quantile-resistance-network.md`
- **Lean modules (umbrella `GaloisForLFunctions.RHTower`):**
  - corpus, already present: the quantile profile calculus (`ThetaQuantileProfileCalculus`: `h = 1/q`, `h' = H(Q)`, strict concavity, `t² H(Q) q ≤ t`), the CDF actions `Φ_n = cdfAction n` and their quantile form (`ThetaCdfFixedShiftAction`: `cdfAction_eq_quantileSpeed`, the fixed-shift law `n(Φ_{n+a} − Φ_n) → 0`), `Φ_{2n} < 2Φ_n` (`ThetaCdfActionDyadic`), the CDF-action matrices of `B` and `D` and the determinant bridge (`ThetaQuantileFourierQuotient`), the exact opposite-frequency blocks (`ThetaQuotientOppositeFrequencyBlocks`), the theta envelopes (`HedenmalmThetaKernelEnergy`), the first-atom derivative asymptotics (`ThetaCuspNativeOddSchurFarTail`), exponential derivative moments (`ThetaCuspFullDerivativeExponentialMoments`), the pinned primitive and its boundary defect (`HedenmalmPinnedVolterraBoundaryDefect`, `HedenmalmClosedWeightedDerivative`), and from the one-port card the pencil `TD = A − bβ`, `β = −i∫Q·`, the flat tests and the charged modes `f_z`;
  - new: `FourierPositiveJumpNetwork` (the abstract potential-kernel theorem, (1)–(5), grounded positivity), `ThetaQuantileResistanceNetwork` (the theta profile is a Fourier-positive jump profile, theta (1)–(6), decaying gauge, isolated blocks), `ThetaQuantileScoreProjection` (score, (7)), `ThetaQuantileKronReduction` ((8)–(11)).
- **Verification (2026-10-05):** targeted `lake build --old` of each new module; final `lake env lean` audit of each source with no errors; a `Lean.collectAxioms` sweep over all 388 constants of the four modules finds only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no axiom, no heartbeat options.
- **Hypotheses:** the abstract theorem assumes exactly the card's list (`IsJumpProfile`: `h` continuous on `[0,1]`, `h(1−t) = h(t)`, `h > 0` on `(0,1)`, `h(0) = 0`, `ĥ(n) < 0` for `n ≥ 1`, `Φ_m < ∞`), and `isJumpProfile_thetaNetworkProfile` discharges all of them for theta.  The theta statements are unconditional; (10) and (11) are stated for every divisor eigenmode of `D` on `H₀` and specialized to every Xi zero.

Dictionary: `h = thetaNetworkProfile` (`= thetaQuantileProfile = 1/q` on `(0,1)`, `metricReal` its `L²` symbol), `ĥ(n) = profileCoeff h n`, `a_n = jumpConductance h n` (`thetaConductance`), `Φ_m = profileAction h m` (`= cdfAction m` for theta), `L_a = jumpLaplacian`, `v^(n)_m = potentialVoltage h n m`, `K = groundedKernel`, `H = thetaLogHazard`, `s = thetaScoreFun` (`thetaScoreVec`), `Q = quantileVec`, `Π = scoreProjection`, `h₀ = thetaProfileMass`, `G = kronMetric`, `γ = clockInput`, `b = onePortOutputVector`, `I = rootIntegral`, `E = rootEnergy`, `X_n = thetaDiagonalBlock`.

| Card item | Lean theorem |
|-|-|
| Fejér positivity, `Σ_{n≤K} a_n ≤ ĥ(0)`, summability | `fejer_identity`, `fejerSum_nonneg`, `IsJumpProfile.fejer_coeff_nonneg`, `IsJumpProfile.sum_range_jumpConductance_le`, `IsJumpProfile.summable_jumpConductance` |
| **(1)** `Σ a_n = ĥ(0)/2`, `h = 2Σ a_n(1 − cos 2πnt)` absolutely and uniformly on `[0,1]` | `IsJumpProfile.hasSum_jumpConductance`, `IsJumpProfile.hasSum_profile`, `IsJumpProfile.tendstoUniformlyOn_profile` (via `IsJumpProfile.hasSum_fourier_profile`, `IsJumpProfile.fourierCoeff_profileCircle`, `IsJumpProfile.summable_fourierCoeff_profileCircle`) |
| **(2)** `L_a` on bounded sequences and on `Φ`; symbol `h` | `summable_jumpLaplacian_term`, `IsJumpProfile.summable_green`, `IsJumpProfile.jumpLaplacian_fourierMode` |
| **(3)** `2Σ a_nΦ_n = 1` | `IsJumpProfile.hasSum_unitCapacity` |
| **(4)** `(L_aΦ)_m = −1_{m=0}`, absolutely | `IsJumpProfile.hasSum_green`, `IsJumpProfile.jumpLaplacian_profileAction`, `IsJumpProfile.action_bracket`, `IsJumpProfile.abs_action_bracket_le`, `cos_bracket` |
| **(5)** `L_a v^(n) = δ_n − δ₀`; drop `v_n − v_0 = 2Φ_n` | `IsJumpProfile.jumpLaplacian_potentialVoltage`, `potentialVoltage_drop` |
| theta hypotheses: continuity at the endpoints, symmetry, positivity, `ĥ(n) < 0`, finite actions | `continuousOn_thetaNetworkProfile`, `thetaNetworkProfile_one_sub`, `profileCoeff_thetaNetworkProfile_neg` (two integrations by parts: `integral_profile_cos_eq`, `tendsto_profile_boundary`, `thetaProfileCurvature_neg`), `intervalIntegrable_thetaAction`, `isJumpProfile_thetaNetworkProfile` |
| theta actions are the CDF actions; positive conductances | `profileAction_thetaNetworkProfile`, `thetaConductance_pos` |
| theta (1), (3), (4), (5), grounded positivity | `hasSum_thetaNetworkProfile`, `hasSum_theta_unitCapacity`, `hasSum_theta_green`, `jumpLaplacian_cdfAction`, `jumpLaplacian_thetaVoltage`, `thetaVoltage_drop`, `theta_groundedKernel_form` |
| decaying gauge `v^(n)_m → 0` as `m → ±∞` | `tendsto_thetaVoltage_atTop`, `tendsto_thetaVoltage_atBot` (from `tendsto_cdfAction_add_sub`) |
| **(6)** `D_(m,n) = v^(n)_m/(2πn)`; the pinned-mean row of `B` | `inner_unitFourierBasis_thetaQuotientOperator_eq_voltage`, `inner_unitFourierBasis_thetaKernelOperator_eq_voltage` |
| grounded kernel positive: `Σ c̄_m c_n K(m,n) = ∫|Σ c_m(1−e_m)|²/h ≥ 0`; `v = K − Φ_n`; the gauge shift is not `ℓ²` | `IsJumpProfile.sum_groundedKernel_eq`, `IsJumpProfile.groundedKernel_form_nonneg`, `IsJumpProfile.integral_grounded`, `potentialVoltage_eq_groundedKernel_sub`, `not_summable_sq_gauge_shift` |
| every isolated `{n,−n}` block has nonzero (real) eigenvalues | `thetaDiagonalBlock_comp_self` (`X_n² = (d² − o²)Π_n`), `blockOff_sq_lt_blockDiag_sq`, `eq_zero_of_thetaDiagonalBlock_eq_zero`, `sq_eq_of_thetaDiagonalBlock_eigen` |
| `|k'/k| = O(e^{2x})`, `∫k'²/k < ∞`, `s ∈ L²`; `Q h → 0` at both ends | `exists_abs_thetaLogHazard_le`, `integrable_thetaFisherInformation`, `integrable_thetaLogHazard_sq_mul_normalized`, `memLp_thetaScore`, `tendsto_thetaQuantile_mul_profile_nhdsGT_zero`, `tendsto_thetaQuantile_mul_profile_nhdsLT_one` |
| `∫Q s = 1`, `β(f) = −i⟨Q,f⟩`, `V s = −h`, `A s = −i P h`, `s ∈ H₀` | `integral_thetaQuantile_mul_score`, `inner_quantileVec_thetaScoreVec`, `onePortInput_eq_inner_quantileVec`, `pinnedVolterraCLM_thetaScoreVec`, `onePortPrimitive_thetaScoreVec`, `thetaScoreVec_mem` |
| **(7)** `Π² = Π`, `ran Π = Q^⊥`, `ker Π = ℂs`, `TD = AΠ`, `ker D ∩ H₀ = ℂs` | `scoreProjection_idem`, `mem_range_scoreProjection_iff`, `scoreProjection_eq_zero_iff`, `scoreProjection_mem`, `onePortMetric_thetaQuotientOperator_eq_scoreProjection`, `thetaQuotientOperator_thetaScoreVec`, `thetaQuotientOperator_eq_zero_iff` |
| `h₀ > 0`; `γ(f) = i∫(1/2 − t) f` | `thetaProfileMass_pos`, `thetaProfileMass_eq`, `clockInput_eq_integral`, `inner_constMode_pinnedVolterraCLM` |
| `⟨f,Gf⟩ = ∫h|f|² − |∫hf|²/h₀`, strictly positive on `H₀`, real | `inner_kronMetric`, `inner_kronMetric_eq_variance`, `inner_kronMetric_eq_metricEnergy`, `re_inner_kronMetric_pos`, `im_inner_kronMetric` |
| **`G` is not bounded below** | `not_kronMetric_boundedBelow` |
| **(8)** `TD = A − bβ`, `⟨b, Df⟩ + h₀β(f) = γ(f)`, `GD = A − (b/h₀)γ` | `onePortMetric_thetaQuotientOperator` (one-port card), `inner_onePortOutputVector_thetaQuotientOperator`, `kronMetric_thetaQuotientOperator` |
| `b_n = −a_|n|`, `γ(e_n) = −1/(2πn)` | `inner_unitFourierBasis_onePortOutputVector`, `clockInput_unitFourierBasis` |
| **(9)** `(GD)_(m,n) = 1_{m=n}/(2πn) − a_|m|/(2πn h₀)` | `inner_unitFourierBasis_kronMetric_thetaQuotientOperator` (with `inner_unitFourierBasis_onePortPrimitive`) |
| the clock is singular in the `G`-energy | `not_clockInput_bounded` (flat tests `clockTestField`) |
| a nonreal eigenmode has `γ(f) ≠ 0` | `im_eq_zero_of_clockInput_eq_zero`, `clockInput_portEigenmode_ne_zero` |
| **(10)** `(v/|z|²)⟨f,Gf⟩ = −(1/h₀) Im(γ(f)⟨f,b⟩)` | `boundaryWork_law`, `boundaryWork_law_portEigenmode` |
| root equation `g' + 1 = −izqg`; `γ(g') = iI`, `∫hg' = −h₀ − izI` | `root_ode_ae`, `clockInput_eq_rootIntegral`, `inner_onePortOutputVector_root` |
| **(11)** `⟨g',Gg'⟩ = |z|²(E − |I|²/h₀)` | `re_inner_kronMetric_root`, `metricEnergy_root`, `integrable_rootEnergy`, `re_inner_kronMetric_portEigenmode` |
| (10) + (11) give `Re I(z) = v E(z)` | `rootIntegral_re`, `rootIntegral_re_portEigenmode` |

The card proves no orientation of the decaying-gauge dipole operator and no zero exclusion; none is formalized.  Its "finite-energy" qualifier for `v^(n)` is descriptive; the formalized content is the dipole equation (5) and the drop `2Φ_n`.  The remark that generic even strictly log-concave densities also satisfy (1)–(9) is covered for (1)–(5) by the abstract theorem (any profile satisfying `IsJumpProfile`).
