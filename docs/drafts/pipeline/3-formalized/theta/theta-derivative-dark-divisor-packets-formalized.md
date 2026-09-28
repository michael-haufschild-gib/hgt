# Positive theta deformations with an exact invisible off-line divisor packet — Lean certificate

- **Paper card:** `theta-derivative-dark-divisor-packets.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaDerivativePacketDivisor` ((2), (3), (4), zero
  counts, reciprocal power sums, detection scale, logarithmic jet, squared coordinate),
  `GaloisForLFunctions.RHTower.ThetaSourceTailRatioCalculus` (negligible/moderate tail calculus,
  ratio approximation `k^{(j)}/k ≈ P_j/P_0`, the tail limits `A → 8m`, `B → 0`,
  `(log k)'' + 4πe^{2x} → 0`), `GaloisForLFunctions.RHTower.ThetaDerivativePacketLogConcavity`
  ((1): positivity, uniform strong log-concavity, Schwartz convergence, exponential moments,
  weighted seminorms; (5)), `GaloisForLFunctions.RHTower.ThetaDerivativePacketSpectralBoundary`
  (the one-theorem packet statement, the neighbourhood consequence, the spectral-infinity boundary
  theorem), `GaloisForLFunctions.RHTower.ThetaSourceTailDerivativeModeration`,
  `GaloisForLFunctions.RHTower.ThetaCompactTailInterpolation`,
  `GaloisForLFunctions.RHTower.ThetaCompactTailSchwartzConvergence`,
  `GaloisForLFunctions.RHTower.ThetaCompactTailImplant` (compact-tail strengthening),
  `GaloisForLFunctions.HTGeometry.HurwitzMaxModulusZeros` (zero persistence); corpus
  `ThetaCuspDerivativeLeadingSign` (degree and leading coefficient of `P_n`, positive ratio at
  infinity), `ThetaCuspDerivativeTailPositivity` (`k^{(4m)} > 0` on both tails),
  `ThetaCuspFirstAtomAllOrderApproximation` (all-order first-atom relative error),
  `ThetaCuspKernelLogConcavity` (`thetaCuspLogConcavityNumerator_neg_all`),
  `ThetaTailCapacitySharpness` (`sourceTransform_thetaDerivSourceC`), `SmoothWeight` (uniform
  window derivative bounds), `XiSuperchargeHarnackDefect` (`riemannHypothesis_iff_XiC_zeros_real`)
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** targeted `lake build` of every module; `lake env lean` audit clean on all nine
  new modules; `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 232 theorems
  of the new modules; no `sorry`. The only hypotheses are the card's own quantifiers (`m ≥ 1`,
  the deformation parameter `t`, the moment depth `J`, the neighbourhoods, the finitely many
  continuous statistics of the boundary theorem).

Dictionary: `k = thetaCuspFullSource`, `F = XiC`, `k_t = thetaDerivativePacket m t`
(`thetaDerivativePacketC` complex, `thetaDerivativePacketSchwartz` in `𝓢(ℝ, ℝ)`),
`F_t = sourceTransform (thetaDerivativePacketC m t)`, `α_j = thetaPacketRoot m t j`,
`σ_j = thetaSourceRatio j = k^{(j)}/k`, `π_j = thetaAtomRatio j = P_j(e^x)/P_0(e^x)`,
`q = thetaCuspSingleAtomReflectionScale 1 = π e^{2x}`, `𝓔 = ThetaExpDecaySource`,
`𝓗 = ThetaRealRootedSource`, `p_{A,n} = thetaExpSeminorm A n`, the source topology at `k` is
`thetaExpSourceNhds k`, `χ_R = thetaTailWindow R`, `L = thetaPacketLogRatio m t`,
`b_R = thetaTailInterpolant m t R`, `ψ = thetaImplantBump`, `ψ_ℓ = thetaImplantAtom ℓ`,
`Σ c_ℓ ψ_ℓ = thetaImplantCorrection N c`, `H = thetaImplantGram N`.

| Card item | Lean theorem |
|-|-|
| (1)–(4) as one theorem: for small `t > 0`, `k_t > 0`, even, `(log k_t)'' ≤ -δ`, every exponential moment, moments below `4m`, `F_t = XiC(1 + t z^{4m})`, same real orders, simple nonreal packet off both axes | `thetaDerivativePacket_dark_divisor` |
| (1) positivity and uniform strong log-concavity for `0 ≤ t < ε` (one `δ` for all such `t`) | `exists_thetaDerivativePacket_stronglyLogConcave`, `exists_thetaDerivativePacket_numerator_le` |
| (1) tail curvature, uniform in `t ≥ 0`: `N_t ≤ -k_t²` and `N_t ≤ (-4πe^{2x} + (8m)² + 2)k_t²` | `eventually_thetaDerivativePacketNumerator_le`, `eventually_thetaDerivativePacketNumerator_le_scale` |
| (1) the identity `(σ₂ + tσ_{r+2})(1 + ta) - (σ₁ + tσ_{r+1})² = (1+ta)²ℓ + t(1+ta)a M - t²a²A²` and its bound | `thetaPacket_numerator_algebra`, `thetaPacket_numerator_le`, `thetaPacket_numerator_le_mul` |
| (1) compact interval: strict numerator and bounded derivatives survive small `t` | `thetaPacket_compact_numerator_le` |
| (1) `(log k_t)'' = (k_t''k_t - k_t'²)/k_t²`; `k_t^{(i)} = k^{(i)} + t k^{(i+4m)}`; evenness | `iteratedDeriv_two_log_thetaDerivativePacket`, `iteratedDeriv_thetaDerivativePacket`, `thetaDerivativePacket_neg`, `thetaDerivativePacketNumerator_neg` |
| (1) Schwartz, `k_t → k` in the Schwartz topology | `thetaDerivativePacketSchwartz_apply`, `tendsto_thetaDerivativePacketSchwartz` |
| (1) every exponential moment | `integrable_exp_abs_mul_abs_thetaDerivativePacket` |
| (1) every exponentially weighted derivative seminorm of `k_t - k` is `O(|t|)` | `exists_expWeighted_iteratedDeriv_thetaDerivativePacket_sub_le` |
| tail inputs: `σ_j - π_j` negligible; `σ_{r+1}/σ_r - σ_1 → 2r`; `a''/a`-curvature `→ 0`; `(log k)'' + 4πe^{2x} → 0` | `thetaSourceRatio_close`, `tendsto_thetaSourceRatio_logSlope`, `tendsto_thetaSourceRatio_logCurvature`, `tendsto_thetaSourceRatio_curvature_add_scale` |
| recursion `P_{n+1} = P_n/2 + yP_n' - 2πy²P_n`, its curvature identity, log-derivative limits from degrees | `eval_thetaCuspLogDerivativeStep`, `eval_thetaCuspLogDerivativeStep_curvature`, `tendsto_polyLogSlope`, `tendsto_polyLogCurvature` |
| (2) `∫ x^j k^{(i)} = (-1)^i j(j-1)⋯(j-i+1) ∫ x^{j-i} k` (integration by parts) | `integral_pow_mul_iteratedDeriv_thetaCuspFullSource` |
| (2) moments below `4m` unchanged; `∫ x^{4m}(k_t - k) = t (4m)! ∫ k > 0` | `integral_pow_mul_thetaDerivativePacket_of_lt`, `integral_pow_mul_thetaDerivativePacket_sub`, `integral_pow_mul_thetaDerivativePacket_sub_pos` |
| (3) `F_t(z) = XiC(z)(1 + t z^{4m})` for every complex `z` | `sourceTransform_thetaDerivativePacketC` |
| (4) `1 + t x^{4m} > 0`, `F_t(x) = (1 + t x^{4m}) XiC(x)`, same real orders | `thetaDerivativePacketC_real_divisor` |
| (4) zeros of `1 + t z^{4m}` are exactly `α_j`, `j < 4m`; injectivity; `α_j^{4m} = -1/t` | `thetaPacketFactor_eq_zero_iff`, `thetaPacketRoot_injOn`, `thetaPacketRoot_pow`, `thetaPacketFactor_root` |
| (4) each `α_j` is an extra simple zero: `ord_{α_j} F_t = ord_{α_j} XiC + 1`; elsewhere orders agree | `analyticOrderAt_thetaPacketFactor_root`, `analyticOrderAt_thetaDerivativePacketC_root`, `analyticOrderAt_thetaDerivativePacketC_of_factor_ne_zero` |
| (4) no `α_j` on the real or imaginary axis | `thetaPacketRoot_im_ne_zero`, `thetaPacketRoot_re_ne_zero` |
| (4) conjugation and sign symmetry | `thetaPacketFactor_conj`, `thetaPacketFactor_neg` |
| (4) `|α_j| = t^{-1/(4m)} → ∞` as `t ↓ 0` | `norm_thetaPacketRoot`, `tendsto_norm_thetaPacketRoot` |
| (4) zero counts on every disc differ exactly by the packet (`0` or `4m`) | `finsum_divisor_thetaDerivativePacketC`, `finsum_divisor_thetaDerivativePacketC_sub_le`, `finsum_divisor_thetaPacketFactor` |
| (5) `((k_t - k)/k)/(t(2πe^{2x})^{4m}) → 1` and `(k_t - k)/k → +∞` | `tendsto_thetaDerivativePacket_relative_div`, `tendsto_thetaDerivativePacket_relative_atTop` |
| neighbourhood consequence (moments through `J`, full real divisor, nonreal zero, Schwartz neighbourhood) | `exists_thetaSchwartz_nearby_same_moments_real_divisor_nonreal_zero` |
| reciprocal power sums `Σ α_j^{-ℓ} = 0` (`1 ≤ ℓ < 4m`), `Σ α_j^{-4m} = -4mt` | `sum_inv_thetaPacketRoot_pow`, `sum_inv_thetaPacketRoot_pow_self` |
| detection scale `|F_t/XiC - 1| ≤ tR^{4m}` on `|z| ≤ R` | `norm_sourceTransform_thetaDerivativePacketC_div_sub_one_le` |
| `log(1 + t z^{4m})` has zero Taylor jet through degree `4m - 1` (order exactly `4m`) | `analyticOrderAt_log_thetaPacketFactor` |
| squared coordinate `1 + t z^{4m} = 1 + t(z²)^{2m}` | `thetaPacketFactor_sq_coordinate` |
| spectral-infinity boundary: `k_t ∈ 𝓔 \ 𝓗`, `p_{A,n}(k_t - k) = t p_{A,n}(k^{(4m)}) → 0`, `k_t → k` in `𝓔` | `thetaExpDecaySource_thetaDerivativePacket`, `not_thetaRealRootedSource_thetaDerivativePacket`, `thetaExpSeminorm_thetaDerivativePacket_sub`, `tendsto_thetaExpSeminorm_thetaDerivativePacket_sub`, `tendsto_thetaDerivativePacket_thetaExpSourceNhds` |
| `k` in the closure of `𝓔 \ 𝓗`, within the positive, even, strongly log-concave class | `exists_mem_thetaExpSourceNhds_not_realRooted` |
| `k ∈ 𝓗 ↔ RH`; under RH `k` lies on the boundary of `𝓗` | `thetaRealRootedSource_thetaCuspFullSource_iff`, `thetaCuspFullSource_boundary_of_riemannHypothesis` |
| strict continuous ambient margins cannot certify real-rootedness | `exists_not_realRooted_of_strict_continuous_margins` |
| compact-tail strengthening (exact literal tails, strong log-concavity, moments through `J`, nonreal zero, any Schwartz neighbourhood) | `exists_thetaCompactTailImplant` |
| even window `χ_R` with `R`-uniform derivative bounds | `thetaTailWindow`, `exists_bound_iteratedDeriv_thetaTailWindow`, `thetaTailWindow_eventuallyEq_one`, `thetaTailWindow_eq_zero` |
| `b_R = k e^{χ_R L} = k_t e^{(χ_R - 1)L}`; `b_R = k_t` near `[-R,R]`, `= k` outside `[-R-1,R+1]` | `thetaTailInterpolant_eq_mul_exp`, `thetaTailInterpolant_eventuallyEq_packet`, `thetaTailInterpolant_eq_source` |
| `(log b_R)'' = (1-χ)(log k)'' + χ(log k_t)'' + 2χ'L' + χ''L` | `iteratedDeriv_two_log_thetaTailInterpolant` |
| tail inputs `(log k)'' ≤ -4πe^{2x} + 1`, `|L'| ≤ 8m + 1`, `L ≤ επe^{2x}` | `eventually_iteratedDeriv_two_log_thetaCuspFullSource_le`, `eventually_abs_deriv_thetaPacketLogRatio_le`, `eventually_thetaPacketLogRatio_le_mul_scale` |
| global strong log-concavity of `b_R` for large `R` | `exists_thetaTailInterpolant_stronglyLogConcave` |
| all derivatives of `ρ_j = h^{(j)}/h`, of `log h` and of `L` are moderate on the tail | `thetaTailModerate_iteratedDeriv_ratio`, `thetaTailModerate_iteratedDeriv_log`, `thetaTailModerate_iteratedDeriv_thetaPacketLogRatio` |
| `|x|^p |(b_R - k_t)^{(n)}(x)| ≤ C e^{-R}` (Faà di Bruno for `e^{φ_R}`) | `exists_weighted_iteratedDeriv_thetaTailInterpolant_sub_le`, `abs_iteratedDeriv_exp_comp_le` |
| `b_R → k_t` in Schwartz, in every weighted `L¹` norm, in every moment | `tendsto_thetaTailInterpolantSchwartz`, `tendsto_integral_exp_mul_abs_thetaTailInterpolant_sub`, `tendsto_integral_pow_mul_thetaTailInterpolant` |
| Gram matrix `∫x^{2(i+ℓ)}ψ` positive definite (quadratic form `∫P²ψ`), hence invertible | `dotProduct_thetaImplantGram_mulVec`, `thetaImplantGram_mulVec_eq_zero`, `thetaImplantGram_mulVec_injective` |
| correction moments `∫ x^{2i} Σc_ℓψ_ℓ = (Hc)_i`; small coefficients give `C²`-small, weighted-`L¹`-small corrections | `integral_pow_mul_thetaImplantCorrection`, `eventually_abs_iteratedDeriv_thetaImplantCorrection_le`, `tendsto_integral_exp_mul_abs_thetaImplantCorrection` |
| positivity and curvature near the bump under `C²`-small perturbation | `exists_thetaDerivativePacket_bump_region`, `thetaPacket_additive_numerator_le` |
| transforms converge uniformly on strips | `norm_sourceTransform_sub_le` |
| Rouché step (maximum modulus on `1/G`); isolated-zero circles | `exists_zero_mem_closedBall_of_norm_sub_lt`, `exists_sphere_norm_ge_of_differentiable` |
| odd moments of even sources vanish | `integral_pow_mul_eq_zero_of_odd` |

The card's degree/leading-coefficient and tail-positivity items were already in
`ThetaCuspDerivativeLeadingSign` and `ThetaCuspDerivativeTailPositivity`; the latter module had not
been compiled before and was built as a dependency of this programme.
