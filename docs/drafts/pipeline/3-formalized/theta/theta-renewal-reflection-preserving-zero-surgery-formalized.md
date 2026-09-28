# Off-axis zero surgery inside the exact positive renewal reflection class — Lean certificate

- **Paper card:** `theta-renewal-reflection-preserving-zero-surgery.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaReflectionPreservingZeroSurgery` (planted
  coefficients, items 1–5, capstone, scalar family), `GaloisForLFunctions.RHTower.ThetaSurgeryControllability`
  (directions (2), mass (3), limits (4), limiting 3×3 matrix, controllability isomorphism),
  `GaloisForLFunctions.RHTower.ThetaProfileSurgeryVariation` (one-sided integration by parts,
  variation (5), exact mass, density (7)), `GaloisForLFunctions.RHTower.ThetaSurgeryEnvelope`
  (envelope, seam jets, Cauchy bounds, domination by `ν`, by the tail `R`, and by the first theta
  atom after all prime shifts); general layers `GaloisForLFunctions.RHTower.ProfileRenewalLogKernel`
  (renewal series, Volterra law and reflection for any even profile with `P' = aP - ν`, Laplace
  identity, stability) and `GaloisForLFunctions.RHTower.ProfileRenewalAnalyticContinuation`
  (holomorphic convolution powers, real-analytic continuation, universal even seam jets); corpus
  `HedenmalmThetaSourceSpectrumExact`, `XiHorizontalStripDecay`, `ThetaRenewalIncrement`
  (`q < 1/6`), `ThetaRenewalAnalyticContinuation`, `ThetaPrimeDeletionSpectralEscape`,
  `ThetaSeamCouplingFamily`, `ThetaSourceSurgeryToolkit`, `HTGeometry.OscillatoryPacketFourier`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `lake env lean` audit clean on all six modules;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no
  `sorry`, no hypotheses beyond the card's own quantifiers (`N ≥ 0`, `0 < v < 1/4`).

Dictionary: `a = 1/4`, `c = Θ 1`, `b = v`, `P = thetaLogProfile`, `ν = thetaRenewalIncrement`,
`q = thetaRenewalMass`, `ψ = surgeryEnvelope N`, `g = surgeryPerturbation N T ε`,
`g_j = surgeryDirection N T j` (`= g[e_j]`), `E_T(g) = surgeryTransform N T ε (T + vI)`
(`= stripEval v T g`), `M(g) = surgeryMass N T ε`, `P_g = surgeryProfile`, `ν_g = surgeryIncrement`,
`D_g = surgeryDenominator`, `X_g = surgeryXi`, `k_g = surgeryDensity`, `w_T = surgeryTarget v T`,
`ε_T = plantedCoeff N v T`, `P_T = plantedProfile`, `ν_T = plantedIncrement`,
`Q_T = plantedLogKernel = renewalLogKernel ν_T c`, `X_T = plantedXi`, `k_T = plantedDensity`,
`D_S = thetaPrimeDeletion S`, `h = thetaCuspSourceTerm · 1`, `P_r = thetaCouplingProfile r`.

| Card item | Lean theorem |
|-|-|
| scalar family: `P_r = rP + (1-r)ce^{at}` is the inverse source of `D_r/(λ - a)`; seam jump `2ac(1-r)`; constant `2ac(1-r)` in `X_r` | `integral_cexp_mul_thetaCouplingProfile`, `thetaCouplingProfile_seam_jump`, `thetaCouplingXi_eq` (corpus) |
| `r = 1` is the unique smooth member | `differentiableAt_thetaCouplingProfile_abs_iff`, `contDiff_thetaCouplingProfile_abs_iff` |
| envelope `ψ` even, entire, positive off `0`; directions (2) even, vanish through order `2N+1` | `surgeryEnvelope_pos`, `surgeryEnvelope_neg`, `surgeryDirection_zero/one/two`, `surgeryPerturbation_neg`, `iteratedDeriv_surgeryPerturbation_zero`, `analyticAt_surgeryPerturbation` |
| derivatives decay faster than every `e^{-B|t|}`; dominated by `ν` and by the first theta atom | `exists_abs_iteratedDeriv_surgeryPerturbation_le_exp`, `abs_iteratedDeriv_surgeryPerturbation_le`, `pow_mul_surgeryDecay_le_increment`, `pow_mul_surgeryDecay_le_thetaLogTail` |
| (3) `M(g) = ∫₀^∞ e^{at}(ag - g') = 2a ∫₀^∞ e^{at} g`; `M(g₀) > 0`, `M(g₁), M(g₂) → 0` | `integral_exp_mul_surgeryIncrement_sub`, `integral_exp_mul_surgeryIncrement`, `surgeryEnvelopeMass_pos`, `tendsto_surgeryMass_one`, `tendsto_surgeryMass_two` |
| (4) `E_T(g₀) → 0`, `E_T(g₁) → ½∫ψe^{bt} > 0`, `E_T(g₂) → -(i/2)∫tψe^{bt}`, `∫tψe^{bt} = 2∫₀^∞ tψ sinh(bt) > 0` | `tendsto_surgeryTransform_zero/one/two`, `integral_exp_mul_surgeryEnvelope_pos`, `integral_exp_mul_mul_surgeryEnvelope_eq`, `integral_exp_mul_mul_surgeryEnvelope_pos` |
| the real 3×3 matrix `(Re E_T, Im E_T, M)` converges to an invertible matrix | `tendsto_det_surgeryMatrix`, `surgeryMatrixLimit_ne_zero` |
| controllability: `E_T` on `ker M` is a real-linear bijection onto `ℂ` with inverse bounded uniformly in `T` | `surgery_controllability` (linearity: `surgeryTransform_eq_sum`, `surgeryMass_eq_sum`) |
| `δD(λ) = (λ - a)ĝ(λ)` by one-sided integration by parts | `renewalLaplace_deriv_surgeryPerturbation`, `surgeryDenominator_eq` |
| (5) `X_{P+g}(z) - Ξ(2z) = -(z² + a²) E_z(g)` | `surgeryXi_eq`, `renewalLaplace_add_eq_surgeryTransform`, `surgeryTransform_eq_stripEval` |
| `Ξ(2z_T) → 0` exponentially; (6) solved; coefficients `O(e^{-T})` | `exists_norm_surgeryTarget_le`, `exists_plantedCoeff_le`, `eventually_plantedCoeff_small` |
| 1. `P_T(0) = c`, jets of `P` through order `2N+1`; `P_T` even real-analytic | `surgeryProfile_zero`, `iteratedDeriv_surgeryProfile_zero`, `surgeryProfile_neg`, `analyticAt_surgeryProfile`, `analyticAt_thetaLogProfile` |
| 1. `P_T - P → 0` with every fixed-order derivative in every exponentially weighted uniform norm | `eventually_plantedProfile_sub_le` |
| 2. `ν_T > 0` on `t ≥ 0`; `c⁻¹∫₀^∞ e^{at}ν_T = q < 1/6` | `eventually_plantedIncrement_pos`, `eventually_plantedIncrement_mass`, `thetaRenewalMass_lt` (corpus) |
| 2. `Q_T` positive, `∫₀^∞e^{-λt}Q_T = -log(1 - L_T/c)`, `D_T = c e^{-∫e^{-λt}Q_T} ≠ 0` on `Re λ ≥ -a` | `eventually_plantedLogKernel` (general: `renewalLogKernel_pos`, `integral_cexp_mul_renewalLogKernel`, `renewalDenominator_eq_exp`, `renewalDenominator_ne_zero`) |
| 3. (1) `Q_T†(-t) + Q_T(t) = 2 sinh(at)/t`, `Q_T` real-analytic on the whole axis | `surgeryLogKernel_neg_add`, `analyticAt_surgeryLogKernel` (general: `renewalLogKernel_neg_add`, `renewal_volterra_law`, `analyticAt_renewalLogKernel`; holomorphic increment `surgeryIncrementC`) |
| `Q_T^{(2j)}(0) = a^{2j+1}/(2j+1)` | `iteratedDeriv_even_surgeryLogKernel_zero` (general: `iteratedDeriv_even_renewalLogKernel_zero`) |
| 4. `X_T(T + ib) = 0`, `|Im| = b < a`, reflected quartet | `eventually_plantedXi_eq_zero`, `surgeryXi_neg`, `surgeryXi_conj`, `surgeryTransform_conj` |
| 4. perturbation nonzero at arbitrarily large `T` | `frequently_XiC_ne_zero`, `plantedPerturbation_ne_zero` |
| 5. (7) `k_T(x) = k(x) + 2[g_T''(2x) - a²g_T(2x)]`, `∫e^{-iwx}k_T = X_T(w/2)`; `k_T` even | `integral_cexp_mul_surgeryDensity`, `integral_cexp_mul_plantedDensity`, `surgeryDensity_neg` |
| 5. (8) `D_S k_T(x) > 0` on `x ≥ 0`, uniformly in the finite prime set `S`; `k_T > 0` | `eventually_thetaPrimeDeletion_plantedDensity_pos`, `abs_thetaPrimeDeletion_le_sum_abs`, `sum_deletionShift_le`, `eventually_plantedDensity_pos` |
| optional `P_T(t) > e^{at}` on `t ≥ 0` | `eventually_exp_lt_plantedProfile` |
| the theorem, all items at once for arbitrarily large `T` | `reflection_preserving_zero_surgery` |
