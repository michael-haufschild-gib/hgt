# Theta CDF quotient has no coercive finite-range Fourier symmetrizer — Lean certificate

- **Paper card:** `theta-cdf-no-finite-range-symmetrizer.md`
- **Lean modules (umbrella `GaloisForLFunctions.RHTower`):**
  - `ThetaCdfFixedShiftAction`: hazard `h = k'/k` (strictly decreasing, odd, `→ ±∞`), tangent bound, `I ≤ k/h`, endpoint ratio `r = I/k = tq(t)` (nondecreasing, `→ 0`, integrable derivative), the action `Φ_n` in both coordinates, nonlinear Riemann–Lebesgue along the CDF phase, the weight `w_a = g_a ∘ F` with integrable derivative and zero endpoint limits, integration by parts, the fixed-shift law (1), `Φ_n → ∞`.
  - `ThetaCdfFiniteRangeSymmetrizerNoGo`: the quotient matrix `D`, entry asymptotics (3)/(4), vanishing row sums, bounded block quadratic form, abstract banded no-go, the operator theorem on `ℓ²(ℤ∖{0})`.
- **Corpus inputs used:** `strictConcaveOn_thetaCuspLogSource` (strict log-concavity of the literal theta density), `exists_abs_thetaCuspFullSource_le` (decay at every exponential rate, used to force `h → ±∞`), `HedenmalmThetaSource.thetaSource` (positive density source), `HedenmalmIntervalAnomaly.cdfFun_neg`, `HedenmalmQuantile.integral_comp_quantile`, `PositiveDensitySource.integrableOn_comp_quantileFun_iff`, `Real.tendsto_integral_exp_smul_cocompact` (Riemann–Lebesgue).
- **Verification (2026-10-04):** targeted `lake build --old` of both modules; final `lake env lean` audit of each source with empty output; `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 99 theorem/definition declarations (`NonzeroFreq` depends on no axiom); no `sorry`, no axiom, no heartbeat options.
- **Hypotheses:** only the card's quantifiers. The operator theorem is proved without self-adjointness (stronger); the self-adjoint version of the card is a corollary. `GD = D*G` is used entrywise, `Σ_k G_{m,k}D_{k,n} = Σ_k D_{k,m}G_{k,n}`; both sums are finite because `G` has finite range.

Dictionary: `k = thetaCuspFullSource`, `M = thetaSource.mass`, `F = thetaSource.cdfFun`, `Q = thetaSource.quantileFun`, `q = HedenmalmQuantile.quantileSpeed thetaSource`, `g' = thetaLogHazard`, `I = thetaLeftMass`, `I/k = thetaEndpointRatio`, `Φ_n = cdfAction n`, `e^{2πinF} = cdfPhase n`, `g_a ∘ F = actionWeight a`, `D = cdfQuotientMatrix`, `ℓ²(ℤ∖{0}) = nonzeroFreqL2`, `u_N = blockIndicator N`.

| Card item | Lean theorem |
|-|-|
| `Φ_n = ∫₀¹ q(t)(1−cos 2πnt)dt`, `Φ_{−n} = Φ_n` (definition; x-coordinate form `∫(1−cos 2πnF)`) | `cdfAction`, `cdfAction_eq_quantileSpeed`, `cdfAction_neg`, `integrable_cdfAction_integrand` |
| **(2)** `t q(t) = I(x)/k(x)` at `t = F(x)` | `mul_quantileSpeed_eq_thetaEndpointRatio` |
| log-concavity: `g'` nonincreasing (strictly), odd | `strictAnti_thetaLogHazard`, `thetaLogHazard_neg`, `thetaLogHazard_zero` |
| double-exponential tail forces `g'(x) → +∞` as `x → −∞` | `exists_thetaLogHazard_le`, `tendsto_thetaLogHazard_atBot`, `tendsto_thetaLogHazard_atTop` |
| tangent bound `I(x)/k(x) ≤ 1/g'(x)` | `thetaCuspFullSource_le_tangent`, `thetaLeftMass_le` |
| `I/k` nondecreasing (`tq(t)` increases from zero), integrable derivative | `hasDerivAt_thetaEndpointRatio`, `thetaEndpointRatio_mul_hazard_le`, `monotoneOn_mul_quantileSpeed`, `tendsto_thetaEndpointRatio_atBot`, `integrableOn_thetaEndpointRatio_deriv_Iic` |
| reflection for `(1−t)q(t)` on the right end | `cdfFun_thetaSource_neg`, `actionWeight_neg`, `actionWeightDeriv_neg`, `cdfPhase_neg_int` |
| `g_a = q(1 − e^{2πiat}) ∈ W^{1,1}(0,1)`, zero endpoint traces | `actionWeight_eq_quantile`, `hasDerivAt_actionWeight`, `integrable_actionWeightDeriv`, `norm_actionWeightDeriv_le`, `tendsto_actionWeight_atBot`, `tendsto_actionWeight_atTop` |
| `Φ_{n+a} − Φ_n = Re ∫₀¹ g_a(t)e^{2πint}dt` | `cdfAction_add_sub_eq`, `integral_one_sub_cdfPhase_mul_eq_quantile` |
| integration by parts `= Re[−(2πin)^{−1}∫ g_a' e^{2πint}]` | `integral_one_sub_cdfPhase_mul_cdfPhase` |
| Riemann–Lebesgue | `tendsto_integral_mul_cdfPhase` |
| **(1)** `Φ_{n+a} − Φ_n = o(1/n)` for every fixed `a ∈ ℤ` | `tendsto_mul_cdfAction_add_sub` |
| `Φ_n → +∞` | `tendsto_cdfAction_atTop` |
| `D_{m,n} = (Φ_m − Φ_{n−m})/(2πn)` | `cdfQuotientMatrix` |
| **(3)** `(GD)_{m,n} = −S_mΦ_n/(2πn) + O_m(1/n)`; **(4)** `(D*G)_{m,n} = o_m(1/n)` | `tendsto_mul_cdfQuotientMatrix_add`, `tendsto_mul_cdfQuotientMatrix_neg_add`, `tendsto_cdfAction_add_sub` (inside `rowSum_eq_zero_of_intertwining`) |
| every row sum of `G` is zero | `rowSum_eq_zero_of_intertwining` |
| `⟨u_N,Gu_N⟩` bounded independently of `N` (`≤ 2W` boundary rows, `≤ 4W+2` entries each) | `norm_blockQuadForm_le`, `card_bandSet_le`, `inner_blockIndicator` |
| `‖u_N‖² = 2N`, coercivity contradiction | `norm_sq_blockIndicator`, `card_blockSupport`, `no_coercive_banded_intertwiner` |
| **Theorem:** no bounded (self-adjoint) `G`, `c > 0`, `W` with coercivity, finite range, `GD = D*G` | `no_coercive_finite_range_symmetrizer`, `no_coercive_finite_range_selfAdjoint_symmetrizer` |
| strengthening by the zero-Jordan-history theorem | `thetaKernelOperator_no_injective_bounded_symmetrizer` (corpus; see `theta-compact-inverse-zero-jordan-history-formalized.md`) |
