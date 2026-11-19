# Structural Laws, Pole Isolations, Probe Decompositions, and Recurrence Obstructions of a Single Off-Line Quartet

- **ID:** zfc-ecs-elt-single-quartet-insights
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1811/obstacles-summary.md` §2.17
- **Statement:** Unconditional structural theorems on `HasSingleOffLineQuartet ρ₀`, Euler dilation pole isolation, Eisenstein zero-scattering duals, rank-two Weil completion, translated-probe Laplace-tent and pole-neutral triple decompositions, self-return confinement, `N`-smooth alternating Euler-product Rouché domination, universal two-prime dilation spanning, and fractional-part Mellin/divisor laws.

## Goal
Formalize unconditionally all analytic, spectral, and arithmetic insights uncovered during the investigation of single-quartet exclusion (§2.17), across `ZeroForcingCalculus`, `ExclusionOfTheCriticalState/Index`, and `ExceptionalLayerTheory`.

## Gates
- [x] 0 → 1  in-progress: well-posed, unconditional mathematical statements
- [x] 1 → 2  fully-proven: complete paper proofs (`[PROVED HERE]`), zero open dependencies
- [x] 2 → 3  formalized: Lean 4 modules audited via `lake --old env lean` with zero errors/warnings and wired into domain umbrellas

## Formalized Lean Modules & Declarations

1. **`GaloisForLFunctions.ZeroForcingCalculus.SingleQuartetRationalRaysAndDilationPoles`**
   (`formal/GaloisForLFunctions/ZeroForcingCalculus/SingleQuartetRationalRaysAndDilationPoles.lean`)
   - `dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le`, `isRuler_dilatedPowerQuotient`, `dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le_of_seven_le`, `dilatedPowerQuotient_poleFree_iff_riemannHypothesis`
   - `riemannZeta_pos_real_mul_eq_zero_imp`, `subsingleton_other_ray_zeros_of_singleQuartet`, `riemannZeta_rat_ray_ne_zero_of_irrational_re`
   - `riemannZeta_div_nat_ne_zero_of_singleQuartet`, `dilatedPowerQuotient_neg_order_of_singleQuartet`, `riemannZeta_nat_mul_ne_zero_of_singleQuartet_ge_four`

2. **`GaloisForLFunctions.ZeroForcingCalculus.SingleQuartetDilationIsolationAndScatteringDuals`**
   (`formal/GaloisForLFunctions/ZeroForcingCalculus/SingleQuartetDilationIsolationAndScatteringDuals.lean`)
   - `meromorphicOrderAt_riemannZeta_eq_quartetCopyMult`, `meromorphicOrderAt_riemannZeta_eq_of_mem_zeroQuartetSet`
   - `riemannZeta_one_sub_div_nat_ne_zero_of_singleQuartet`, `riemannZeta_shift_div_nat_ne_zero_of_singleQuartet`, `riemannZeta_two_sub_and_sub_one_ne_zero_of_strip`, `riemannZeta_two_sub_and_sub_one_ne_zero_of_singleQuartet`
   - `dilatedPowerQuotient_rightHalf_poles_eq_of_singleQuartet`, `dilatedPowerQuotient_leftHalf_poles_of_singleQuartet`, `squarefreeDilationQuotient_quarter_pole_isolation`
   - `eisensteinDualMinus`, `eisensteinDualPlus`, `eisensteinDualModes_scattering_and_spectral_split`

3. **`GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetRankTwoCompletionAndProbeResonance`**
   (`formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/SingleQuartetRankTwoCompletionAndProbeResonance.lean`)
   - `rankTwoCompletedWeil_eq_onLineMixed_add_cosh`, `bareMixedEnergy_add_sinhFunctional_sq_eq`, `coshFunctional_sq_le_bareMixedEnergy_add_sinhFunctional_sq`, `bareMixedEnergy_sinhOrthogonal_eq_and_ge`, `bareMixedEnergy_coshOrthogonal_eq`, `rankTwoCompletedWeil_cauchy_schwarz`
   - `bareMixedEnergy_eq_onLineMixed_of_riemannHypothesis`, `rankTwoCompletedWeil_nonneg_of_riemannHypothesis`, `abs_bareMixedEnergy_probe_shiftProfile_le_of_riemannHypothesis`
   - `probe_shiftProfile_unbounded_above_and_below_of_singleQuartet`, `not_hasSingleOffLineQuartet_of_probeShift_bddAbove`, `not_hasSingleOffLineQuartet_of_probeShift_bddBelow`, `exists_coshSurplus_violation_of_riemannHypothesis`

4. **`GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TranslatedProbeTentDecompositionAndPoleNeutralTriples`**
   (`formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TranslatedProbeTentDecompositionAndPoleNeutralTriples.lean`)
   - `integral_probe_mul_shiftProfile_sub`, `integral_probe_mul_shiftProfile_add`, `primePairTerm_probe_shiftProfile`, `primeMixedForm_shiftProfile_probe_eq`, `primeMixedForm_probe_shiftProfile_nonneg`, `primeMixedForm_probe_shiftProfile_horizon_split`
   - `polePart_probe_shiftProfile`, `abs_gammaMixedForm_shiftProfile_le`, `bareMixedEnergy_probe_shiftProfile_le_exp_half`, `nonneg_twoProbe_bareMixedEnergy_unbounded_of_singleQuartet`
   - `poleNeutralTriple`, `negativeHalfLineLaplace_poleNeutralTriple`, `poleNeutralTriple_changes_sign`, `halfMoments_shiftProfile_poleNeutralTriple_eq_zero`, `poleNeutralTriple_primeMixed_bounded_of_riemannHypothesis`, `poleNeutralTriple_primeMixed_unbounded_of_singleQuartet`, `not_hasSingleOffLineQuartet_of_poleNeutralTriple_primeMixed_bddAbove`, `not_hasSingleOffLineQuartet_of_poleNeutralTriple_primeMixed_bddBelow`

5. **`GaloisForLFunctions.ExceptionalLayerTheory.SingleQuartetRecurrenceSmoothTailAndUniversalDilations`**
   (`formal/GaloisForLFunctions/ExceptionalLayerTheory/SingleQuartetRecurrenceSmoothTailAndUniversalDilations.lean`)
   - `not_zetaZeroDiscWeaklyRecurrent_of_singleQuartet`, `zetaReturnSet_confined_of_singleQuartet`
   - `smoothAltEulerProduct`, `altDirichletPoly`, `smoothAltTail`, `hasSum_smoothAltEulerProduct`, `smoothAltEulerProduct_eq_head_add_tail`, `smoothAltEulerProduct_analytic_and_ne_zero_on_strip`, `smoothAltTail_lower_bound_near_zero`
   - `sin_mul_log_two_ne_zero_or_three_ne_zero`, `dilationAlpha`, `dilationBeta`, `cpow_eq_dilationAlpha_add_dilationBeta`, `singleQuartet_universal_twoPrime_chebyshev_span`
   - `riemannZeta_eq_zero_iff_fract_mellin_strip`, `sum_vonMangoldt_mul_fract_eq_harmonic_sub_log`, `sum_vonMangoldt_mul_fract_upper_sqrt_concentration`

## Paper Proofs (`[PROVED HERE]`)

### 1. Affine-Reflected Nonvanishing, Half-Quartet Pole Isolation, and Eisenstein Dual Modes
Assume `HasSingleOffLineQuartet ρ₀`, so $\frac12 < \beta := \operatorname{Re}\rho_0 < 1$, $\gamma := \operatorname{Im}\rho_0$ satisfies $|\gamma| > 4$, and $\{\rho \in (0,1) + i\mathbb{R} : \zeta(\rho)=0,\ \operatorname{Re}\rho \neq \frac12\} = Q(\rho_0)$.
- For $k \ge 2$ and $\rho \in Q(\rho_0)$, both $1 - \rho/k$ and $((k-1)+\rho)/k$ lie in $\{\frac12 < \operatorname{Re} s < 1\}$ with $|\operatorname{Im}| = |\gamma|/k < |\gamma|$, so $\zeta$ vanishes at neither point; $\operatorname{Re}(2-\rho) > 1$ and $\xi(\rho-1) = \xi(2-\rho) \neq 0$ ($\operatorname{Im}(\rho-1) \neq 0$) give $\zeta(2-\rho) \neq 0$ and $\zeta(\rho-1) \neq 0$.
- Writing $F_{k,m}(s) = ((s-1)\zeta(s))^m/\zeta(ks) = u(s)^m(ks-1)/u(ks)$ via $u(z)=(z-1)\zeta(z)$ ($u(1)=1$), the poles in $\{\operatorname{Re} s > \frac{1}{2k}\}$ are precisely $\{\rho_0/k, \bar\rho_0/k\}$ with exact order $-\operatorname{ord}_{\rho_0}\zeta < 0$, while $\{(1-\rho_0)/k, (1-\bar\rho_0)/k\}$ lies in $\{0 < \operatorname{Re} s < \frac{1}{2k}\}$ with the same order.
- The Eisenstein zero-scattering roots $w_- = 1 - \rho_0/2$ and $w_+ = (1+\rho_0)/2$ satisfy $\frac12 < \operatorname{Re} w_- < \frac34 < \operatorname{Re} w_+ < 1$, $\xi(2w_\pm - 1) = 0$, $\xi(2w_\pm) \neq 0$, $\zeta(w_\pm) \neq 0$, and $w_-(1-w_-) - w_+(1-w_+) = \frac{2\rho_0 - 1}{4} \neq 0$.

### 2. Translated-Probe Laplace-Tent Decomposition and Pole-Neutral Three-Probe Profiles
- For $p > 0$ and $L, R \ge 0$, $\int e_p(t) e_p(t - L + R)\,dt = \frac{e^{-p|L-R|}}{2p}$ and $\int e_p(t) e_p(t + L + R)\,dt = \frac{e^{-p(L+R)}}{2p}$, making $\operatorname{primeMixedForm}(e_p, \tau_R e_p) \ge 0$ symmetric and splitting it at $\lfloor e^R \rfloor_+$ into the finite sub-horizon moment $\frac{e^{-pR}}{2p}\sum_{n=1}^{\lfloor e^R\rfloor_+} \Lambda(n)n^{p-1/2}$, the super-horizon tail, and the reflected Dirichlet series.
- The polar cross-pairing equals $\frac{2\cosh(R/2)}{p^2 - 1/4}$, $|\operatorname{gammaMixedForm}(F, \tau_R F)| \le \frac{1}{2\pi}\int \|\widehat{F}(r)\|^2 |\gamma(r)|\,dr$, and $\operatorname{primeMixedForm}(e_p, \tau_R e_p) \ge 0$ yields $\operatorname{bareMixedEnergy}(e_p, \tau_R e_p) \le \Gamma_{\max}(p) + \frac{2e^{R/2}}{p^2 - 1/4}$, while $G_R = e_p + \tau_R e_p \ge 0$ diverges to both $+\infty$ and $-\infty$ in diagonal Weil energy under `HasSingleOffLineQuartet ρ₀`.
- For $4 < p < q < r$, $H_{p,q,r} = \sum_{\alpha \in \{p,q,r\}} \frac{\alpha^2 - 1/4}{\prod_{\beta \neq \alpha}(\alpha - \beta)} e_\alpha$ satisfies $\mathcal{L}H(w) = \frac{w^2 - 1/4}{(p+w)(q+w)(r+w)}$, changes sign on $(-\infty, 0)$, has $C(\tau_R H) = S(\tau_R H) = 0$ for all $R \in \mathbb{R}$, and reduces $\operatorname{bareMixedEnergy}(H, \tau_R H)$ up to $O(1)$ to the pure prime pairing, which is bounded under `RiemannHypothesis` and unbounded both above and below under `HasSingleOffLineQuartet ρ₀`.

### 3. Self-Return Confinement, Smooth Alternating Euler Tail Floor, Universal Two-Prime Dilations, and Fractional-Part Laws
- Under `HasSingleOffLineQuartet ρ₀`, `¬ ZetaZeroDiscWeaklyRecurrent`, and for $\varepsilon < \operatorname{zetaNonvanishingDistance}(\rho_0, r)$, every $\tau \in \operatorname{zetaReturnSet}(\overline{B}(\rho_0, r), \varepsilon)$ satisfies $|\tau| \le r$ or $|\tau + 2\operatorname{Im}\rho_0| \le r$.
- For $N \ge 2$, $|\omega(p)| \le 1$, and $|\omega(2)| = 1$, $\widetilde{E}_N(s;\omega) = (1 - 2^{1-s}\omega(2))\prod_{p \le N} (1 - \omega(p)p^{-s})^{-1}$ equals $\sum_{P^+(n) \le N} (-1)^{n-1}\omega(n)n^{-s}$ on $\operatorname{Re} s > 0$, is holomorphic and nonvanishing on $\{0 < \operatorname{Re} s < 1\}$, and forces $\sup_{\overline{B}(\rho_0, r)} |T_N^{\mathrm{sm}}(z;\omega)| \ge (2^{1 - (\operatorname{Re}\rho_0 + r)} - 1)\operatorname{zetaNonvanishingDistance}(\rho_0, r) - \varepsilon$.
- By irrationality of $\log 3 / \log 2$, some $q_0 \in \{2, 3\}$ satisfies $\sin(\operatorname{Im}\rho_0 \cdot \log q_0) \neq 0$, giving $u^{\rho_0} = \alpha(u) + \beta(u) q_0^{\rho_0}$ and universal all-scale $O(\sqrt{ux}\log^2(ux) + (|\alpha(u)| + |\beta(u)|)\sqrt{x}\log^2 x)$ reconstruction of $\psi(ux) - ux$ and $\theta(ux) - ux$ from $\{x, q_0 x\}$ across all $u \ge 1$, $x \ge 16$.
- On $\{0 < \operatorname{Re} s < 1\}$, $\zeta(s) = 0 \iff \int_0^\infty \{ct\}t^{-s-1}\,dt = 0 \iff \int_1^\infty \{t\}t^{-s-1}\,dt = \frac{1}{s-1}$, and $\sum_{d=1}^{\lfloor X \rfloor_+} \Lambda(d)\{X/d\} = X\sum_{d=1}^{\lfloor X \rfloor_+} \frac{\Lambda(d)}{d} - \sum_{m=1}^{\lfloor X \rfloor_+} \log m$ with $1 \le d \le \lfloor\sqrt{X}\rfloor_+$ bounded in $[0, \psi(\sqrt{X})]$.

## Log
- 2026-11-18 — paper proofs written in `2-fully-proven`; all five Lean 4 modules audited via `lake --old env lean` (exit code 0, zero warnings) and wired into `ZeroForcingCalculus.lean`, `ExclusionOfTheCriticalState.lean`, and `ExceptionalLayerTheory.lean`; promoted to `3-formalized`.
