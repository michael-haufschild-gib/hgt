# Complete Weil Positivity at Power-of-Logarithm Overlap

- **ID:** complete-weil-positivity-power-log
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../reports/review-3110/obstacles-summary.md · §2.5.1
- **Statement:** Define $\alpha_0 := \operatorname{powerLogPositivityExponent} := \min\!\big(\frac{1}{500},\, \frac{1}{60 \cdot \operatorname{conductorCutoffConstant}}\big) > 0$ and $\kappa := \operatorname{tiltedSplineSpectralFloorConstant} := \frac{2 \cdot \operatorname{tiltedSplineTailConstant}}{\int \varphi_0^2} > 0$, where $\varphi_0 := \operatorname{tiltedUnitSpline}$. For every $0 < \alpha < \alpha_0$, eventually in $N$, for all $1 \le c \le (\log N)^\alpha$: (1) $W_{c,N} := \operatorname{completeWeilMatrix}(\varphi_0, c, N)$ is positive definite on all vectors; (2) $\frac{\kappa}{2 c^7}\|x\|^2 \le \operatorname{completeWeilEnergy}(\varphi_0, c, N, x)$ for all $x \in \operatorname{EuclideanSpace}\;\mathbb{R}\;(\operatorname{PrimeHorizonIndex}\;N)$; (3) $0 \le \operatorname{weilQuad}(\operatorname{atomicTest}(N, y, \operatorname{atomDilate}(\varphi_0, c/N)))$ for all $y : \mathbb{N} \to \mathbb{R}$; and (4) there exists an explicit $b_1 > 0$ independent of $\alpha, c, N$ such that $\frac{b_1}{c^{23}}\operatorname{poleDefect}_N(x) \le \operatorname{completeWeilEnergy}(\varphi_0, c, N, x)$ and $\frac{b_1}{\log N}\operatorname{poleDefect}_N(x) \le \operatorname{completeWeilEnergy}(\varphi_0, c, N, x)$ for all $x$.

## Goal
Resolve §2.5.1 of `docs/reports/review-3110/obstacles-summary.md` unconditionally on all vectors in $E_N := \operatorname{EuclideanSpace}\;\mathbb{R}\;(\operatorname{PrimeHorizonIndex}\;N)$ across a power-of-logarithm overlap window $1 \le c \le (\log N)^\alpha$, bypassing the exponential conductor-confinement barrier $\exp(O(c^{16})) \gg (\log N)^A$ that restricted individual quasimode residual assembly to $1 \le c \le (\log \log N)^\alpha$.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, multiscale orthogonal decoupling across $[1, Q_1]$, $(Q_1, R']$, and $V_{R'}^\perp$
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems formalized unconditionally in `CompletedArithmeticForms` and `CriticalArithmeticCorrelationTheory`, standalone `lake --old env lean` checks green, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`)

## Lean Declarations

- `formal/GaloisForLFunctions/CompletedArithmeticForms/ConductorBandTopTailBounds.lean`
  - `exists_quantitative_exponential_conductor_cutoff_of_poleDefect_le`
  - `poleDefect_ge_of_norm_sub_starProjection_gt`
  - `low_band_norm_le_of_mem_orthogonal`
  - `poleDefect_ge_of_supported_above`
  - `sum_Ioc_sq_le_of_mem_conductorSubspace`
  - `sum_linear_moment_sq_le_of_mem_conductorSubspace`
- `formal/GaloisForLFunctions/CompletedArithmeticForms/ConductorBandPrimeAndCenterBounds.lean`
  - `sum_linear_moment_sq_le_four_div_log`
  - `fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one`
  - `abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace`
  - `norm_separatedCrossErrorMatrix_le`
  - `abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace`
  - `exists_divisorJetHorizonVector_norm_le`
  - `exists_fullPrimeMatrix_packet_residual_norm_le`
  - `exists_fullPrimeMatrix_orthog_inner_le`
- `formal/GaloisForLFunctions/CompletedArithmeticForms/ConductorBandOverlapAndNonRatioBounds.lean`
  - `fullWeilNonRatioMatrix_eq_downward_add_upward`
  - `upwardPrimeVector_self_inner_eq_downward`
  - `overlap_sub_nonRatio_inner_eq`
  - `completedConductorEnergy_le_of_one_le`
  - `exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace`
  - `exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace`
  - `exists_overlapMatrix_inner_le_of_mem_conductorSubspace`
  - `exists_overlapMatrix_midBand_inner_le`
- `formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap.lean`
  - `powerLogPositivityExponent`, `powerLogPositivityExponent_pos`
  - `tiltedSplineSpectralFloorConstant`, `tiltedSplineSpectralFloorConstant_pos`
  - `spectralFloorWeilMatrix`
  - `eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_powerLog`
  - `eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_powerLog`
  - `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_powerLog`
  - `exists_powerLog_exponent_tiltedUnitSpline_completeWeilMatrix_posDef`
  - `eventually_tiltedUnitSpline_weilQuad_nonneg_powerLog`
  - `exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_powerLog`

## Proof Summary

Set $Q_1(N) := \lfloor (\log N)^{1/12} \rfloor$, $v_m := \operatorname{normalizedRamanujanHorizonVector}(m, N)$, and $V_M := \operatorname{conductorSubspace}\;M\;N$. Shifting by half of the polynomial conductor floor (`tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor`), $M_{c,N} := \operatorname{spectralFloorWeilMatrix}(c, N) = W_{c,N} - \frac{\kappa}{2 c^7} I$ retains conductor diagonal $\ge \frac{\kappa}{2 c^7}$ and unchanged quasimode residuals $r_m(c, N) := W_{c,N} v_m - E_m(c) v_m$. By `exists_tiltedUnitSpline_uniform_conductor_residual_bound` at $A = \frac{1}{12}$, eventually in $N$ across $1 \le c \le (\log N)^\alpha$ ($\alpha < \alpha_0 \le \frac{1}{500}$), both $\sum_{m=1}^{Q_1} \|r_m(c, N)\|^2$ and its ratio to $(\frac{\kappa}{2 c^7})^2$ decay as $O((\log N)^{5/12 + 24\alpha - 1/2}) \le O((\log N)^{-1/50})$. By `matrix_posDef_of_uniform_conductor_budget` with $R = Q = Q_1$, positive definiteness of $M_{c,N}$ reduces to ruling out unit vectors $x \in E_N$ satisfying $\operatorname{completeWeilEnergy}(\varphi_0, c, N, x) \le \frac{\kappa}{2}$ and $\|x - P_{V_{Q_1}} x\|^2 > \frac{1}{4}$.

1. **Low-band orthogonal decoupling (`low_band_decoupling_unit_orthogonal`).** Writing $x = p + z$ with $p := P_{V_{Q_1}} x \in V_{Q_1}$ and $z \in V_{Q_1}^\perp$, orthogonality $\langle v_m, z \rangle = 0$ ($m \le Q_1$) cancels the diagonal conductor energies in $\langle W_{c,N} p, z \rangle$, leaving $|\langle W_{c,N} p, z \rangle| \le \sqrt{2 \sum_{m=1}^{Q_1} \|r_m\|^2} \le \frac{1}{8}$. Polarized harmonic Gram bounds (`normalizedRamanujanHorizonVector_gram_exact`) and $0 < E_m(c) \le |S_1| + 2\log m + 3 c^4$ (`completedConductorEnergy_le_of_one_le`) yield $\langle W_{c,N} p, p \rangle \ge -\frac{1}{4}$, so $\hat{z} := z / \|z\| \in V_{Q_1}^\perp$ satisfies $\|\hat{z}\| = 1$ and $\operatorname{completeWeilEnergy}(\varphi_0, c, N, \hat{z}) \le 2\kappa + 2$.
2. **High-tail cross-pairing suppression (`exists_high_tail_suppression`).** Polynomial defect reserve (`exists_completeWeil_matrix_polynomial_reserve`) forces $\operatorname{poleDefect}_N(\hat{z}) \le K_{\mathrm{coef}} c^{16}$. Quantitative exponential confinement (`exists_quantitative_exponential_conductor_cutoff_of_poleDefect_le`) at $\eta := (M_1^2 c^{10})^{-1}$ supplies $R' := \max(R, Q_1)$ with $\log R' \le C_R c^{46} + \log Q_1 \ll (\log N)^{1/5}$ (hence $(R')^6 \le N$) such that $u := P_{V_{R'}} \hat{z} \in V_{R'} \cap V_{Q_1}^\perp$ and $w := \hat{z} - u \in V_{R'}^\perp$ satisfy $\|w\|^2 \le \eta$ and $\|u\|^2 \ge \frac{3}{4}$. On $V_{R'} \cap V_1^\perp$ against $V_{R'}^\perp$:
   - the scalar diagonal and two-pole kernels vanish identically (`fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one`);
   - the center collar has bilinear bound $O(c(1 + \log R')/\sqrt{\log N})$ (`abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace`) via `sum_linear_moment_sq_le_four_div_log` and periodic Abel summation past $|n - j| > (R')^4$;
   - the separated cross error has whole-space norm $O(c^2)$ (`norm_separatedCrossErrorMatrix_le`);
   - subtracting the diagonal adjunction packet $\sum_{m=1}^{R'} a_m (\log N - \operatorname{ramanujanAdjunctionEnergy}(m)) v_m \in V_{R'}$ reduces the prime residual to a Mertens envelope, a deep-quotient tail ($n \le N/(R')^4$), and a reduced-conductor top-strip Plancherel sum of norm $O((1 + (1 + \log R')^2/\sqrt{\log N})\|u\|)$ (`exists_fullPrimeMatrix_orthog_inner_le`);
   - sub-horizon quotient-tail torsion cancellation (`sum_Ioc_sq_le_of_mem_conductorSubspace`) bounds $(\operatorname{overlapMatrix} - \operatorname{downwardPrimeVector})u$ and $\operatorname{upwardPrimeVector}(u)$ by $O(c^3 \|u\|)$ (`exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace`, `exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace`).
   Together these give $|\langle W_{c,N} u, w \rangle| \le C_{\mathrm{cross}} c^3 \|u\|\|w\| \le \frac{1}{4}$ and $\langle W_{c,N} w, w \rangle \ge -\frac{1}{4}$, hence $\operatorname{completeWeilEnergy}(\varphi_0, c, N, u) \le 2\kappa + 3$.
3. **Coercivity on $V_{R'} \cap V_{Q_1}^\perp$ (`exists_high_band_coercivity`).** Transpose symmetry of the non-ratio prime kernel (`overlap_sub_nonRatio_inner_eq`) reduces $\langle W_{c,N} u, u \rangle$ to $\operatorname{renormalizedPrimeEnergy}_N(u) - \langle \operatorname{overlapMatrix} u, u \rangle - \log c - O(1)$ (`exists_completeWeilEnergy_ge_prime_sub_overlap`). Splitting $u = u_{\mathrm{low}} + y$ along $[1, Q_1]$ and $(Q_1, R']$:
   - $\|u_{\mathrm{low}}\| \le 54(1 + \log R')/\log N$ (`low_band_norm_le_of_mem_orthogonal`), so all low-band prime and overlap couplings are $o(1)$ and $\|y\|^2 \ge \frac{1}{2}$;
   - periodic summation by parts of the smooth autocorrelation weight over lag periods $m \cdot l \le (R')^2$ suppresses off-diagonal lags ($m \ne l$) to $O(c^3 (R')^4 / N)\|y\|^2$ and diagonal lags ($m = l > Q_1$) via $\varphi(m) \ge \sqrt{m/2}$ to $O(c^4 / \sqrt{Q_1})\|y\|^2$ (`exists_overlapMatrix_midBand_inner_le`), giving $|\langle \operatorname{overlapMatrix} y, y \rangle| \le 4$;
   - the reverse exponential-confinement gap (`poleDefect_ge_of_supported_above`) combined with `poleDefect_le_primeEnergy_add_row_cost` forces $\operatorname{renormalizedPrimeEnergy}_N(y) \ge \frac{\log Q_1}{2 D_0} - O(1)$.
   Since $\frac{\log Q_1}{2 D_0} - \log c \ge (\frac{1}{24 D_0} - \alpha)\log \log N - O(1) \to +\infty$ for $\alpha < \alpha_0$, $\operatorname{completeWeilEnergy}(\varphi_0, c, N, u) > 2\kappa + 3$ eventually, contradiction.

## Log
- 2026-10-31 — paper proof completed and formalized unconditionally in Lean 4 (`3-formalized`)
