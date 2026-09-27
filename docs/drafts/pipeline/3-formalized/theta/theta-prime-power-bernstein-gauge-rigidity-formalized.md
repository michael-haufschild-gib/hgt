# Bernstein flux rigidifies symmetric prime-power gauges of the theta source — Lean certificate

- **Paper card:** `theta-prime-power-bernstein-gauge-rigidity.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaPrimePowerBernsteinGauge` (card), on top of
  the general real-shift gauge layer `GaloisForLFunctions.RHTower.ThetaTranslationGaugeFlux`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for all 16 audited theorems; no `sorry`.

Notation: `g = thetaTranslationGauge c (primePowerShift p)` with `primePowerShift p j = j log p`;
hypothesis `hc : Summable (|c j| * √p ^ |j|)`; `A_v = primePowerPrefix p c v`,
`Q_m = primePowerTail p c m`, `M₀ = primePowerGaugeMass c`, `M_{1/2} = primePowerGaugeCharge p c`,
`F_m = primePowerAbelWeight p m`, `C_p = primePowerStabilityConstant p`,
`B_{p,σ} = primePowerComplexConstant p σ`, `M(w) = thetaGaugeMultiplier c (primePowerShift p) w`.
All card theorems hold for every natural `p ≥ 2` (primality is not needed).

| Card item | Lean theorem |
|-|-|
| (1) `b_k(t) = 2π∑n²e^{-πn²t}`; `b_k(u) ≤ u^{-3/2}/2` | `thetaNormalizedFlux_thetaCuspFullSource`, `thetaNormalizedFlux_thetaCuspFullSource_le` |
| absolute convergence of the gauge and its moments; `L_w g = M(w) XiC(iw)` on `|Re w| ≤ 1/2`; `M(w) = ∑ c_j p^{-jw}` | `integral_exp_mul_thetaTranslationGauge`, `integral_cexp_mul_thetaTranslationGauge`, `thetaGaugeMultiplier_primePower` |
| (6) flux translation law and Gaussian atom expansion | `thetaNormalizedFlux_comp_add`, `thetaNormalizedFlux_thetaTranslationGauge`, `thetaNormalizedFlux_thetaTranslationGauge_eq_tsum` |
| (7) collected rate weight `2πr²·(rate coefficient)`; CM ⇔ grouped weights ≥ 0 (Bernstein–Widder + Laplace uniqueness) | `grouped_thetaGaugeAtom_eq`, `completelyMonotoneOn_tsum_exp_iff_grouped`, `completelyMonotoneOn_thetaNormalizedFlux_gauge_iff_rateCoeff` |
| (3) `b_g` CM ⇔ all `A_v ≥ 0` | `completelyMonotoneOn_primePowerGauge_iff` |
| (4) `Q_m = A_{-m} ≥ 0` | `primePowerPrefix_neg_eq_tail`, `primePowerTail_nonneg` |
| (5) `M_{1/2} - M₀ = ∑_{m≥1} Q_m(F_m - F_{m-1})`; increments `> 0` and `≥ a^{2m-2}(a-1)²`; gap `≥ 0` | `hasSum_primePowerChargeGap`, `primePowerAbelWeight_increment_pos`, `primePowerAbelWeight_increment_ge`, `primePowerChargeGap_nonneg` |
| equality in (5) iff `c_j = 0` for `j ≠ 0` | `primePowerChargeGap_eq_zero_iff` |
| CM + both anchors ⇒ `g = k` | `primePowerGauge_rigidity` |
| (8) `|c_m| ≤ C_p Δ a^{-m}` | `abs_primePowerCoeff_le` |
| (9) `sup_{|Re w|≤σ} |M(w) - M₀| ≤ B_{p,σ} Δ`, all heights | `norm_primePowerMultiplier_sub_mass_le` |
| `M₀ = 1`, `B Δ < 1` ⇒ no zeros of `M`, same zeros and analytic orders as `XiC(iw)` | `primePowerGauge_zero_transfer`, `analyticOrderAt_integral_cexp_mul_thetaTranslationGauge` |
| (10) `‖g - M₀k‖₁ ≤ 4 C_p Δ ‖k‖₁/(a-1)` | `integral_abs_primePowerGauge_sub_le` |
| signed example: prefixes, CM, negative `c_{±1}`, `Δ > 0`, positive rescaling to `M₀ = 1` | `primePowerSignedExample_prefix`, `completelyMonotoneOn_primePowerSignedExample`, `primePowerSignedExample_neg_coeff`, `primePowerSignedExample_chargeGap_pos`, `primePowerSignedExample_normalized` |
