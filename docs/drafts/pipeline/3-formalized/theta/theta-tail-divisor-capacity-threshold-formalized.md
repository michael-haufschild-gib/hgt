# Sharp theta-tail capacity for preserving the complete Xi divisor — Lean certificate

- **Paper card:** `theta-tail-divisor-capacity-threshold.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaTailDivisorCapacity` (Legendre bound, uniform
  Fourier growth, angular Jensen coefficient `2/(πb)`, divisor comparison, the `b > 2` theorem),
  `GaloisForLFunctions.RHTower.ThetaTailSimpleCriticalThreshold` (real-divisor-only `b ≤ 3`),
  `GaloisForLFunctions.RHTower.ThetaTailCapacitySharpness` (`t k^{(4m)}`: transform, divisor,
  `b = 2` bound, no `b > 2` bound), `GaloisForLFunctions.RHTower.ThetaRelativeSourceRigidity`
  (relative-source rigidity), `GaloisForLFunctions.RHTower.ThetaTailSectorialGammaBound`
  (`D(δ)`, the sectorial comparison (3), the disc count (2), the Gaussian control violating (3)),
  `GaloisForLFunctions.HTGeometry.GammaHorizontalRatio` (`Γ(a) ≤ |Γ(a + ib)| e^{B(a,b)}`),
  `GaloisForLFunctions.HTGeometry.SectorPhragmenLindelof` (bounded on the imaginary axis and
  exponentially small on four rays ⇒ constant), `GaloisForLFunctions.HTGeometry.JensenIntegratedCountBound`
  (Jensen in integrated-count form, `∫|sin| = 4`), `GaloisForLFunctions.HTGeometry.GaussianPairControlQuotient`
  (the Gaussian control pair); the companion statements about `k + t k^{(4m)}` come from the
  derivative-packet modules (`ThetaDerivativePacketLogConcavity`, `ThetaDerivativePacketSpectralBoundary`);
  corpus `XiZeroCountRVMRemainder` / `xiSymmetricMass` (Riemann–von Mangoldt), `Zeta23`
  (`two_thirds_simpleCritical_epsilon`), `FourierUniquenessL1`, `EntireBezout`
  (`exists_entire_quotient`), `QuotientProximity`, Nevanlinna characteristic modules,
  `ThetaCuspDerivativeLeadingSign`, `CausalMobiusThetaMovingCusp`
  (`exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian`)
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** targeted `lake build` of every module; `lake env lean` audit clean on all nine
  modules; `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 120 theorems of
  these modules; no `sorry`. The only hypotheses are the card's own quantifiers (the decay
  constants `a, b, C`, measurability, the divisor containment, the relative bound `|u| ≤ Ck`).

Dictionary: `k = thetaCuspFullSource`, `F = XiC`, `H = sourceTransform u`,
`L(y) = thetaSourceLaplace y = XiC(iy)`, `n_F(c, R) = ∑ᶠ z, divisor XiC (closedBall c R) z`,
`I(a, b) = doubleExpMass a b`, `u = t k^{(4m)} = thetaCapacityPacket m t`,
`D(δ) = sectorialExponent δ`, `z_R = sectorialRay δ R`, `B(a, b) = gammaRatioBound a b`,
`k_G = gaussPairSource`, `u_G = gaussPairCosSource`, `F_G = gaussPairTransform`,
`q_G = gaussPairQuotient`.

| Card item | Lean theorem |
|-|-|
| Theorem: `|u| ≤ C exp(-a e^{b|x|})`, `b > 2`, complete divisor containment ⇒ `u = 0` a.e.; pointwise for continuous `u` | `ae_eq_zero_of_doubleExp_divisor`, `eq_zero_of_doubleExp_divisor_of_continuous` |
| equivalent form: `g = k + u` with the complete Xi sub-divisor ⇒ `g = k` | `ae_eq_thetaSource_of_subdivisor` |
| Legendre bound `yv - (a/2)e^{bv} ≤ (y/b) log(1 + 2y/(ab))` | `legendre_doubleExp_le` |
| uniform Fourier growth `log|H(z)| ≤ (y/b) log(2 + y) + O(1 + y)`; `H` entire | `norm_sourceTransform_le_doubleExp`, `measurableMomentSource_of_doubleExp`, `MeasurableMomentSource.differentiable_sourceTransform` |
| (1) angular average `≤ [2/(πb) + o(1)] R log R` via `(1/2π)∫|sin θ| = 2/π` | `circleAverage_log_norm_le_doubleExp`, `circleAverage_abs_im_le`, `integral_abs_sin_zero_two_pi` |
| (2) `n_F(c, R) = [1/π + o(1)] R log R` | `eventually_abs_finsum_divisor_XiC_sub_le`, `xiSymmetricMass_le_finsum_divisor_XiC`, `finsum_divisor_XiC_le_xiSymmetricMass` |
| divisor containment `n_H ≥ n_F` | `finsum_divisor_le_of_order_le` |
| Jensen in counting form (integrated count bounded by the circle average) | `log_norm_add_integral_le_circleAverage`, `integral_div_le_sum_log`, `integral_indicator_inv_le` |
| the contradiction `1 ≤ 2/b` | `false_of_capacity`, `exists_large_mul_log` |
| sharpness: `H = t z^{4m} F`, complete divisor with multiplicities | `sourceTransform_thetaDerivSourceC`, `sourceTransform_thetaCapacityPacket`, `analyticOrderAt_XiC_le_thetaCapacityPacket` |
| sharpness: `|t k^{(4m)}| ≤ C exp(-a e^{2|x|})` for every `a < π`; no bound with `b > 2` for `t ≠ 0` | `exists_norm_thetaCapacityPacket_le`, `not_doubleExp_bound_thetaCapacityPacket` |
| companion: `k + t k^{(4m)}` positive, even, globally strongly log-concave, close to `k` in every weighted derivative seminorm | `thetaDerivativePacket_dark_divisor`, `exists_thetaDerivativePacket_stronglyLogConcave`, `exists_expWeighted_iteratedDeriv_thetaDerivativePacket_sub_le` |
| real-divisor-only threshold: even `u`, vanishing at all simple critical zeros ⇒ `b ≤ 3` (i.e. `u = 0` for `b > 3`) | `ae_eq_zero_of_doubleExp_simpleCritical`, `eq_zero_of_doubleExp_simpleCritical_of_continuous`, `two_mul_xiSimpleCriticalZeroCount_le_finsum_divisor`, `sourceTransform_neg_of_even` |
| relative-source rigidity: `|u| ≤ Ck`, complete divisor containment ⇒ `u = ck` a.e. (`c` real for real `u`; pointwise for continuous `u`) | `relativeSource_rigidity`, `relativeSource_rigidity_real`, `relativeSource_rigidity_of_continuous` |
| the quotient `Q = H/F` is constant (so its zero count and exponential type vanish) | `relativeSource_transform_eq_const_mul` |
| `|H(z)| ≤ C F(i Im z)`; `Q` bounded on the imaginary axis | `norm_sourceTransform_le`, `norm_quotient_imag_le` |
| order-one growth of `Q` | `exists_quotient_envelope`, `exists_norm_XiC_le_exp` |
| (3) sectorial comparison `|Q(z_R)| ≤ 3C e^{(R + 1/2) D(δ)}/cos δ` from the completed gamma factor | `thetaSourceLaplace_le_sectorialRay`, `norm_quotient_le_sectorialRay`, `gammaRatioBound_eq_polar`, `Gamma_le_norm_Gamma_mul_exp` |
| `D(δ) = δ²/4 + O(δ⁴)`; `D ≥ 0`, even, monotone | `abs_sectorialExponent_sub_le`, `sectorialExponent_nonneg`, `sectorialExponent_neg`, `monotoneOn_sectorialExponent` |
| indicator collapse: `D(δ) < κ sin δ` for small `δ`, ray bounds, bounded minimal-type Liouville step | `exists_sectorialExponent_lt_linear`, `quotient_rays`, `eq_const_of_imag_of_rays` |
| Gaussian control: `F_G = √π e^{-z²/4} cos(az)`, `H_G = e^{-ω²/4} F_G cosh(ωz/2)` | `integral_cexp_mul_gaussPairSource`, `integral_cexp_mul_gaussPairCosSource` |
| control quotient even, finite type, bounded on the imaginary axis, nonconstant; the linear angular cusp violates (3) | `gaussPairQuotient_neg`, `norm_gaussPairQuotient_le`, `norm_gaussPairQuotient_I_mul_le`, `gaussPairQuotient_ne_const`, `gaussPairQuotient_not_sectorially_bounded` |

The Lean proof of relative-source rigidity does not pass through Hadamard factorisation and
Pólya's indicator diagram. It bounds the quotient by an order-one envelope (proximity function of
`H/F`), shows it is bounded on the imaginary axis and exponentially small (rate `η r cos α`,
every `η > 0`) on four rays near the imaginary axis by the sectorial gamma comparison, and then
applies a Phragmén–Lindelöf/Liouville theorem for such functions. This proves the card's theorem,
and the constancy of `Q` contains the intermediate claims (linear zero count, finite and then
minimal exponential type).
