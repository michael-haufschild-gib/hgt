# Resolution of the finite-layer logarithmic wall-cusp question

- **ID:** ecs-qic-finite-layer-wall-cusp-resolution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Obstacles summary §2.17 / §2.19](../../../reports/review-1911/obstacles-summary.md#one-question)
- **Statement:** Critical-line crowding, bounded rescaled unit-window sample sums, bounded `σ = -4` Poisson rows, bounded imaginary-axis derivative, and the shift-invariant `Γ_ℝ` half-line energy domain unconditionally admit `O(1/√(log y))` rescaled Laplace amplitudes and sustain a strictly positive logarithmic wall-cusp coefficient; on `ζ`, all six vanishing/summability formulations are equivalent to `BacklundConverse.FiniteOffLine → RiemannHypothesis` and discharge single-quartet exclusion across QIC, PDR, PPC, and ZCG, while leaving isolated outer tails above infinite approaching backgrounds open.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean modules `TheLogarithmicWallCuspOfAFiniteLayer`, `CrowdingSaturatesTheLogarithmicWallCusp`, `TheFiniteLayerWallCuspPayoff`; `#print axioms` verified (`[propext, Classical.choice, Quot.sound]` only)

## 1. Exact cusp laws and first-moment asymptotics on `ζ`

Module: `GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheLogarithmicWallCuspOfAFiniteLayer`

Let $F$ be a threshold ground state at $W_0 > 0$, $a = \operatorname{criticalAliasCoefficient}(W_0)$, $M = \int F(u)^2 e^{-8u}\,du$, and $m_F(q) = \|\mathcal{L}F(\operatorname{centredZero} q)\|^2$ on `onLineCopies`.

1. **Logarithmic Abel and vertical-line $L^2$ cusp laws** (`halfLineEnergyMinimizer_tendsto_mul_log_dampedMass`, `halfLineEnergyMinimizer_tendsto_mul_log_vertical_laplace_sq`, `criticalState_tendsto_mul_log_dampedMass`, `criticalState_tendsto_mul_log_vertical_laplace_sq`):
   $$
   \lim_{x\to+\infty} (x\log x)\int_0^\infty e^{-2xv} F(-v)^2\,dv = 4aM, \qquad
   \lim_{x\to+\infty} (x\log x)\int_{\mathbb{R}} \|\mathcal{L}F(x+iy)\|^2\,dy = 8\pi aM.
   $$
2. **Continuous boundary tail and sub-logarithmic first moment** (`criticalState_boundary_fourier_tail_zero`, `criticalState_boundary_fourier_firstMoment_sublogarithmic`):
   $$
   \lim_{T\to+\infty} T \int_{|y|>T} \|\mathcal{L}F(-4+iy)\|^2\,dy = 0, \qquad
   \lim_{T\to+\infty} \frac{1}{\log T}\int_{-T}^T |y|\,\|\mathcal{L}F(-4+iy)\|^2\,dy = 0.
   $$
3. **Exact critical-line ordinate tail and logarithmic first moment under `FiniteOffLine`** (`criticalState_criticalLine_tail_asymptotic`, `criticalState_criticalLine_firstMoment_asymptotic`, `criticalState_criticalLine_firstMoment_not_summable`, `criticalState_criticalLine_cosine_cusp`):
   $$
   \lim_{T\to+\infty} T \sum_{\substack{q\in\mathrm{onLineCopies} \\ |\gamma_q|>T}} m_F(q) = \frac{8aM}{\pi}, \qquad
   \lim_{T\to+\infty} \frac{1}{\log T}\sum_{\substack{q\in\mathrm{onLineCopies} \\ |\gamma_q|\le T}} |\gamma_q|\,m_F(q) = \frac{8aM}{\pi},
   $$
   $$
   \sum_{q\in\mathrm{onLineCopies}} |\gamma_q|\,m_F(q) = +\infty, \qquad
   \lim_{h\to 0^+} \frac{1}{h}\sum_{q\in\mathrm{onLineCopies}} (1 - \cos(h\gamma_q))\,m_F(q) = 4aM.
   $$

## 2. Unconditional saturation of crowding, sample, Poisson, and fixed-window axioms

Module: `GaloisForLFunctions.ExclusionOfTheCriticalState.Index.CrowdingSaturatesTheLogarithmicWallCusp`

For every $\ell \in \mathbb{R}$, the compactly supported collar profile $F_\ell(u) = \ell(1+8u)^2(\log(1/|u|))^{-1/2}\mathbf{1}_{(-1/8,0)}(u)$ (`smoothedWallLogProfile ℓ`) lies in `CriticalHalfLineEnergyDomain` (`criticalHalfLineEnergyDomain_smoothedWallLogProfile`) and satisfies unconditionally:
- **Sustained wall cusp vs. vanishing unscaled trace and increment quotient** (`smoothedWallLogProfile_tendsto_terminal_sq`, `smoothedWallLogProfile_no_vanishing_cusp_subsequence`, `smoothedWallLogProfile_tendsto_mul_log_dampedMass`, `smoothedWallLogProfile_tendsto_mul_log_vertical_laplace_sq`, `smoothedWallLogProfile_mean_square_wall_trace_zero`, `smoothedWallLogProfile_weighted_sq_increment_div_zero`):
  $\frac{\log(1/h)}{h}\int_{-h}^0 F_\ell(u)^2\,du \to \ell^2$ (no vanishing subsequence when $\ell \neq 0$), $(x\log x)\int_{\mathbb{R}} \|\mathcal{L}F_\ell(x+iy)\|^2\,dy \to \pi\ell^2$, $\frac{1}{h}\int_{-h}^0 F_\ell(u)^2\,du \to 0$, and $\frac{1}{h}\int (F_\ell(u)-F_\ell(u+h))^2 e^{-8u}\,du \to 0$.
- **Half-plane decay, axis Lipschitz regularity, and exact imaginary-axis asymptotic** (`norm_rescaled_laplace_smoothedWallLogProfile_le`, `smoothedWallLogProfile_axis_lipschitz`, `tendsto_axis_laplace_smoothedWallLogProfile`, `tendsto_sq_axis_laplace_smoothedWallLogProfile`):
  $\|(w+5)\mathcal{L}F_\ell(w)\| \le 500|\ell|/\sqrt{\log(\|w\|+4)}$ on $\operatorname{Re} w \ge -4$, $y\mapsto (iy+5)\mathcal{L}F_\ell(iy)$ is $500|\ell|$-Lipschitz, $y\sqrt{\log y}\,\mathcal{L}F_\ell(iy) \to -i\ell$ as $y\to+\infty$, and $y^2(\log y)\|\mathcal{L}F_\ell(iy)\|^2 \to \ell^2$.
- **Unconditional sample-sum and Poisson-row bounds on `onLineCopies` of `ζ`** (`smoothedWallLogProfile_local_critical_line_mass`, `smoothedWallLogProfile_poisson_row_bound`):
  $(1+y^2)\sum_{|\gamma_q-y|\le 1} m_{F_\ell}(q) \le C_1\ell^2$ and $(1+y^2)\sum_q m_{F_\ell}(q)\frac{4}{16+(y-\gamma_q)^2} \le C_2\ell^2$ uniformly for all $y\in\mathbb{R}$.
- **Window-width and multiplicity saturation** (`smoothedWallLogProfile_window_crowding_lower_bound`, `smoothedWallLogProfile_saturates_criticalLine_under_finiteOffLine`, `rvmOrdinate_crowding`, `smoothedWallLogProfile_rvmOrdinate_unit_window_bound`, `smoothedWallLogProfile_crowding_firstMoment_not_summable`, `smoothedWallLogProfile_rvmOrdinate_firstMoment_not_summable`):
  On any multiplicity-indexed ordinate family with $c_h\log y \le \#S_y$ in $[y-h, y+h]$ (both on `onLineCopies` under `FiniteOffLine` and unconditionally on `RvmCopy`), $y^2\sum_{q\in S_y} \|\mathcal{L}F_\ell(i\gamma_q)\|^2 \ge \frac{c_h}{2}\ell^2$, the rescaled `σ = -4` Poisson row is $\ge \frac{2c_h}{16+h^2}\ell^2$, and $\sum_q |\gamma_q|\,\|\mathcal{L}F_\ell(i\gamma_q)\|^2 = +\infty$ for $\ell \neq 0$.
- **Shift-invariant variational ground states** (`exists_halfLineMinimizer_sustaining_wallCusp`):
  Every $R > 0$ admits a half-line minimizer $F_R$ sustaining positive logarithmic wall cusp $8a(R)M_R > 0$ while satisfying $h^{-1}\int_{-h}^0 F_R^2 \to 0$.

## 3. Equivalences, global cross-route payoff, and outer-tail scope boundary

Module: `GaloisForLFunctions.ExceptionalLayerTheory.TheFiniteLayerWallCuspPayoff`

1. **Seven-way equivalence** (`finiteLayer_wallCusp_targets_tfae`):
   `SequentialWallCuspVanishingTarget`, `SequentialVerticalTraceSubCuspTarget`, `FiniteFirstOrdinateMomentTarget`, `SequentialSubLogarithmicFirstMomentTarget`, `SequentialSubInverseOrdinateTailTarget`, `SequentialSubLinearCosineCuspTarget`, and `BacklundConverse.FiniteOffLine → RiemannHypothesis` are mutually equivalent.
2. **Global cross-route payoff corollaries** (no `FiniteOffLine` hypothesis in conclusions):
   - `no_singleOffLineQuartet_of_wallCuspTarget`: $\forall \rho_0,\ \neg\operatorname{HasSingleOffLineQuartet}(\rho_0)$;
   - `packetIndex_zero_or_top_of_wallCuspTarget`: `realPacketNegIndex = 0 ∨ realPacketNegIndex = ⊤`;
   - `twoIntervalRadialExclusionLaw_of_wallCuspTarget`: `TwoIntervalRadialExclusionLaw` (QIC);
   - `ordinary_prime_recurrences_iff_rh_of_wallCuspTarget`: `(2, 3, 6)` ordinary-prime $\theta$-dilation residual boundedness $\leftrightarrow \operatorname{RiemannHypothesis}$ (PDR);
   - `no_properPower_twoWave_quartet_of_wallCuspTarget`: exclusion of the two-wave proper-power discrepancy regime (PPC);
   - `riemannHypothesis_iff_zal_and_landing_of_wallCuspTarget`: `RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ZetaLandingLaw` (ZCG).
3. **Sharp outer-tail scope boundary** (`exists_isolatedOuterTail_above_infiniteApproachingBackground`):
   For every $\sigma_0 \in (1/2, 1)$, there exists `Z : ZeroConfig` with a nonempty finite isolated outer tail right of $1/2 + (\sigma_0 - 1/2)/2$ above an infinite off-line lower background (`(rightOf Z 0).Infinite`), satisfying `AbscissaLawAt Z 0` and `ApproachesLine Z`, yet with `zeroAbscissa Z = σ₀`, `¬ LinearAbscissaLaw Z`, and `¬ AbscissaLaw Z`.
4. **Master synthesis:** `finiteLayer_wallCusp_complete_resolution`.
