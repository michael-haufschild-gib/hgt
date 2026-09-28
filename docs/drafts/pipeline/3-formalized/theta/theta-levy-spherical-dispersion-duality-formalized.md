# Theta Xi as a reflected Lévy dispersion and a three-dimensional spherical transform — Lean certificate

- **Paper card:** `theta-levy-spherical-dispersion-duality.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaReflectedJumpExponents` ((1)–(7), `M`, radius
  law), `GaloisForLFunctions.RHTower.ThetaJumpCompoundPoisson` (compound Poisson law),
  `GaloisForLFunctions.RHTower.ThetaSphericalRadialLift` ((8), positive definiteness),
  `GaloisForLFunctions.RHTower.ThetaJumpRenewalMeeting` ((9)–(12), Pick kernel); corpus
  `CausalThetaHalfLaplace`, `ThetaCuspOneSidedConnection` (`h`, `Ξ = h(z) + h(-z)`),
  `ThetaHalfPortStieltjesSpectral` (`σ`, `C`, `S`, `D(-ir) = c e^{-C - iS}`), `ThetaRenewalExitDensity`
  (`h(2z)` via `D`), `ThetaDeletionInversionCommutator`/`ThetaRenewalIncrement` (`h(2iλ)`, `N`),
  `PrimeArchThetaFirstMoment` (`Ξ(0) = 2∫₀^∞ k`), mathlib `charFun`, `integral_fun_norm_addHaar`,
  `Submodule.reflection_sub`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `lake env lean` audit clean on all four modules;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`,
  no hypotheses beyond the card's own quantifiers.

Dictionary: `k = thetaCuspFullSource`, `ω = thetaJumpDensity = -k'`, `h = thetaOneSidedConnection`,
`K = thetaJumpExponent`, `B = thetaJumpCosineMass`, `σ = thetaPortDensity`, `ν = thetaLevyDensity`
(`ω/x`; continued through the seam as `thetaLevyProfile`), `G = thetaDispersionExponent`
(real form `thetaDispersionExponentReal`), `m = thetaLevyMass`, `M = Xi 0`,
`P_R = thetaRadiusDensity`, `sin w / w = complexSinc`, `f₃ = thetaSphericalDensity`,
`C(r) = thetaRenewalRealCos r`, `S(r) = thetaRenewalRealSin r`, `a = 1/4`, `c = Θ 1`,
`N = thetaRenewalLaplace`, `H = thetaRenewalPositiveReal`.

| Card item | Lean theorem |
|-|-|
| `ω > 0` on `(0, ∞)`, total mass `k(0)`, exponential decay | `thetaJumpDensity_pos`, `integral_thetaJumpDensity`, `exists_abs_thetaJumpDensity_le` |
| (2) `K(z) = -iz h(z)`, `K(z) - K(-z) = -izΞ(z)` for all complex `z` | `thetaJumpExponent_eq`, `thetaJumpExponent_sub_neg` |
| nonzero Xi zeros ⇔ `K(z) = K(-z)` | `XiC_eq_zero_iff_thetaJumpExponent_eq` |
| (3) `B(u) > 0`, `K(u) = B(u) - iuΞ(u)/2`, `uh(u) = uΞ(u)/2 + iB(u)`, `B(u) = πuσ(u²)` | `thetaJumpCosineMass_pos`, `thetaJumpExponent_ofReal`, `mul_thetaOneSidedConnection_ofReal`, `thetaJumpCosineMass_eq_pi_mul_thetaPortDensity` |
| at a positive real zero `K(u)` is strictly positive real | `thetaJumpExponent_of_Xi_eq_zero` |
| (4) `k'(0) = 0`, `ω(x)/x` bounded at `0`, finite positive `ν` | `deriv_thetaCuspFullSource_zero`, `exists_abs_deriv_thetaCuspFullSource_le_mul`, `exists_abs_thetaLevyDensity_le`, `integrableOn_thetaLevyDensity`, `thetaLevyMass_pos` |
| `G` entire and even | `differentiable_thetaDispersionExponent`, `thetaDispersionExponent_neg` |
| (5) `G'(z) = ∫ω sin(zx) = zΞ(z)/2`, `K(z) - K(-z) = -2iG'(z)` | `hasDerivAt_thetaDispersionExponent`, `integral_thetaJumpDensity_mul_sin`, `thetaJumpExponent_sub_neg_eq_deriv` |
| `G(u) > 0` for real `u ≠ 0` | `thetaDispersionExponentReal_pos`, `thetaDispersionExponent_ofReal`, `integral_mul_one_sub_cos_pos` |
| `e^{-tG(u)}` is the characteristic function of the symmetric compound Poisson law (rate `tm`, fair sign, magnitude `∝ ν`) | `charFun_thetaCompoundPoissonLaw`, `isProbabilityMeasure_thetaCompoundPoissonLaw`, `charFun_thetaSymmetricJumpLaw`, `thetaSymmetricJumpLaw_map_neg`, `charFun_thetaJumpConvPow`, `hasSum_thetaPoissonWeight` |
| the characteristic function extends to an entire nowhere-zero function | `differentiable_cexp_neg_mul_thetaDispersionExponent` |
| (6) `d/dz e^{-tG} = -(tzΞ/2)e^{-tG}`; nonzero Xi divisor = critical points | `hasDerivAt_cexp_neg_mul_thetaDispersionExponent`, `deriv_cexp_neg_mul_thetaDispersionExponent_eq_zero_iff` |
| (7) `∫₀^u vΞ(v) dv = 2G(u) > 0` | `integral_mul_Xi_eq`, `integral_mul_Xi_pos` |
| `M = Ξ(0) = 2∫₀^∞ k = 2∫₀^∞ xω` | `Xi_zero_eq_two_mul_integral_thetaCuspFullSource` (corpus), `integral_mul_thetaJumpDensity`, `Xi_zero_eq_integral_mul_thetaJumpDensity` |
| `f₃` continuous with value `-k''(0)/(2πM)` at `0`, nonnegative, probability density | `continuous_thetaSphericalDensity`, `thetaSphericalDensity_zero`, `thetaSphericalDensity_of_ne`, `thetaSphericalDensity_nonneg`, `integral_thetaSphericalDensity`, `continuous_thetaLevyProfile` |
| (8) `∫_{ℝ³} e^{i⟨ξ,y⟩} f₃(y) dy = Ξ(|ξ|)/M` | `integral_cexp_inner_mul_thetaSphericalDensity` (axis: `integral_cexp_axis_mul_thetaSphericalDensity`; slices: `integral_thetaLevyProfile_slice`; split: `measurePreserving_euclideanThreeSplit`) |
| radius law `2xω/M dx` is a probability law and `Ξ(z)/M = E[sin(zR)/(zR)]` | `integral_thetaRadiusDensity`, `integral_thetaRadiusDensity_mul_complexSinc` |
| `ξ ↦ Ξ(|ξ|)/M` positive definite on `ℝ³` | `XiC_norm_positiveDefinite` |
| (9) `G'(2r) = 2cr e^{-C(r)}[a cos S(r) - r sin S(r)]` | `hasDerivAt_thetaDispersionExponentReal_two_mul`, `Xi_two_mul_eq_renewal` |
| (10) `B(2r) = 2cr{r - e^{-C(r)}[r cos S(r) + a sin S(r)]} > 0` | `thetaJumpCosineMass_two_mul_eq` |
| (11) `∫₀^r s e^{-C(s)}[a cos S(s) - s sin S(s)] ds = G(2r)/(4c) > 0` | `integral_renewal_phase_eq`, `integral_renewal_phase_pos` |
| `h(2iλ) = ac - (a + λ)N(λ)` for every complex `λ` | `thetaOneSidedConnection_two_I_mul_eq_renewal` |
| (12) `H(λ) = ½∫₀^∞ ω(1 - e^{-2λx})`, `Re H > 0` on `Re λ > 0` | `thetaRenewalPositiveReal_eq`, `re_thetaRenewalPositiveReal_pos` |
| the Pick kernel of `H` is positive semidefinite | `thetaRenewalPickKernel_nonneg` (Cauchy kernels: `sum_div_add_conj_eq_integral`, `sum_one_sub_exp_div_eq_integral`; `conj_thetaRenewalPositiveReal`) |
| nonzero zeros ⇔ `H(λ) = H(-λ)`; at such zeros `Re H(-λ) > 0` when `Re λ > 0` | `thetaRenewalPositiveReal_sub_neg`, `XiC_two_I_mul_eq_zero_iff_positiveReal`, `re_thetaRenewalPositiveReal_neg_pos` |
