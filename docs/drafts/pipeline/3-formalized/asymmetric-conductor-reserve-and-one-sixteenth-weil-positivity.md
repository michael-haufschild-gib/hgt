# Asymmetric Conductor Reserve, Quadratic-Overlap Residuals, and Power-Log Weil Positivity Below 1/16

- **ID:** asymmetric-conductor-reserve-and-one-sixteenth-weil-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (formalized)
- **Source:** docs/reports/review-3110/obstacles-summary.md · Q1 / Q2a / Confinement & Residual Exponents
- **Lean Modules:**
  - `formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/AsymmetricTwoRegionConductorReserve.lean`
    - `exists_completeWeilEnergy_asymmetric_prefix_terminal_reserve`
    - `exists_completeWeilEnergy_asymmetric_two_region_reserve`
    - `eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal_below_one_ninth`
    - `eventually_completeWeil_global_negIndex_le_polynomialConductor_below_one_ninth`
    - `exists_completeWeil_asymmetric_conductor_cross_absorbed`
    - `exists_asymmetric_conductor_projection_with_adjunction_debit`
  - `formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/QuadraticOverlapConductorResiduals.lean`
    - `exists_completeWeil_quadratic_conductor_residual_variable_rate`
    - `exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate`
    - `exists_tiltedUnitSpline_quadratic_relative_residual_sum_le`
  - `formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/CompleteWeilPositivityBelowOneSixteenth.lean`
    - `eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_sixteenth`
    - `eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_sixteenth`
    - `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_sixteenth`
    - `eventually_tiltedUnitSpline_weilQuad_nonneg_below_one_sixteenth`
    - `exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_below_one_sixteenth`
    - `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_log_one_seventeenth`
    - `eventually_tiltedUnitSpline_all_conductors_pos_below_one_sixteenth`
- **Statement:** On $(V_1)^\perp$, a linear prefix cutoff $L_1(c) = \lceil \max(3, 256 e^2 c) \rceil$ localizes the $O(c^9)$ overlap penalty strictly onto the prefix mass $P$ and leaves only $O(c^2)$ mass cost on the terminal strip $S$, lifting polynomial conductor-complement coercivity on $(V_{\lfloor N^\theta \rfloor})^\perp$ ($0 < \theta$) from $\alpha < 1/16$ to $\alpha < 1/9$; combined with prefix-localized $O(c^{11})$ sublevel confinement and quadratic-in-$c$ ($O(c^2 (1 + \log c)^3 (\log N)^{1/k}/\log N)$) complete-Weil conductor residuals across all eight explicit-formula channels, `completeWeilMatrix tiltedUnitSpline c N` is unconditionally positive definite across $1 \le c \le (\log N)^\alpha$ for every $0 < \alpha < 1/16$.

## Goal
Break both the $\alpha < 1/16$ polynomial conductor-complement barrier (`PolynomialConductorComplementCoercivityAndSharpenedOverlap`) and the $\alpha < 1/19$ unconditional all-vector positivity ceiling (`TheCompleteWeilMatrixIsPositiveBelowTheResidualCeiling`) by:
1. Eliminating the symmetric global mass penalty $-C c^9 (P + S)$ in `TwoRegionConductorReserve`, replacing $K c^{16} \le \log R / D - 1$ by $K c^9 \le \log R / D - 1$ on $(V_R)^\perp$ and confining bounded-energy unit vectors $\hat{z} \in (V_{Q_1})^\perp$ to $\log R' \le C_R c^{11} + \log Q_1$ whenever $c^{16}/\log N \to 0$.
2. Eliminating three powers of $c$ ($c^5 \to c^2$) across all eight single-conductor residual channels of `completeWeilMatrix φ c N`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `AsymmetricTwoRegionConductorReserve`, `QuadraticOverlapConductorResiduals`, and `CompleteWeilPositivityBelowOneSixteenth`, `lake --old env lean` green, `#print axioms` PASS (`[propext, Classical.choice, Quot.sound]`)

## Approach
Three coupled theorems, proved and formalized unconditionally without added hypotheses or budget increases:

### Theorem 1 (Asymmetric Prefix/Terminal Reserve on $(V_1)^\perp$, $\alpha < 1/9$ Complement Coercivity, and Prefix-Localized Sublevel Confinement)
Let $\varphi_0 := \operatorname{tiltedUnitSpline}$, $c \ge 1$, $L_1(c) := \lceil \max(3, 256 e^2 c) \rceil$, and $M := \lfloor N / L_1(c) \rfloor$ for $N \ge L_1(c)$. For $z \in (\operatorname{conductorSubspace} 1 N)^\perp$, let $x := \operatorname{primeHorizonExtension} z$, $P := \sum_{n=1}^M x_n^2$, and $S := \sum_{n=M+1}^N x_n^2$.
1. **Exact vanishing of the pole source on $(V_1)^\perp$:** $\langle z, v_{1,N} \rangle = 0$ annihilates $\sum_{n=1}^N x_n / \sqrt{n}$, so the rank-2 pole moment product vanishes identically on $(V_1)^\perp$.
2. **Split-source logarithmic tail localization:** Outgoing prime-power edges crossing $M$ spend $(1 + \delta/4)(D_N(x) - D_M(x)) + O(c^8) P$, while edges with $m > M$ have step $t < L_1(c)$ and cost at most $(\log 4 + 4) L_1(c) S = O(c) S$ without spending prime defect.
3. **Ordered archimedean split and split-row `nonRatioForm`:** Since $w M \le c / L_1(c) \le 1/(256 e^2)$, `upInd` vanishes identically for $n \le M$, prefix-to-tail pairs cost $O(c^9) P + (\delta/8)(\log N + 1) S$, and tail-to-tail pairs cost $O(c^2) S$, yielding
   $$\frac{1}{2} D_M(x) + \frac{a}{c^7} D_N(x) + \frac{a}{c^7}(\log N) S - C_0 c^9 P - C_1 c^2 S \le \operatorname{completeWeilEnergy}(\varphi_0, c, N, z).$$
4. **Coercivity and confinement:** On $(V_R)^\perp$, $K c^9 \le \log R / D - 1$ suffices, giving coercivity on $(V_{\lfloor N^\theta \rfloor})^\perp$ for all $0 < \alpha < 1/9$ and $\theta > 0$ (extending to $\theta \ge 1/6$ by monotonicity $V_{\lfloor N^{1/12} \rfloor} \subseteq V_{\lfloor N^\theta \rfloor}$), cross-term absorption at $K c^{11} \le \log R / D - 1$, and bounded-energy unit-vector confinement $\log R' \le C_R c^{11} + \log Q_1$ under $K_S c^{16} / \log N \le 1$.

### Theorem 2 (Quadratic-Overlap Complete-Weil Single-Conductor Residuals: $c^5 \to c^2$)
For any $C^2$ profile $\varphi$ supported in $[0, 1]$ with $\int \varphi^2 > 0$, across $0 < m \le (\log N)^A$, $k \ge 1$, $c \ge 1$, and $4(e + 3)^2 c^2 \le N$:
$$\|W_{\varphi,c,N} v_{m,N} - E_\varphi(c, m) v_{m,N}\|^2 \le K \cdot m(1 + \log m)^2 \left(\frac{c^2 (1 + \log c)^3 (\log N)^{1/k}}{\log N} + c^{10}\Big(\frac{\log N}{N}\Big)^2\right),$$
yielding summed relative residual mass $O\big((c^{14} + Q^2)(1 + \log Q)^2 (c^2 (1 + \log c)^3 (\log N)^{1/k}/\log N + c^{10}(\log N/N)^2)\big)$.

### Theorem 3 (Unconditional All-Vector Complete-Weil Positivity Below $1/16$)
Combining Theorems 1 and 2 with `HighConductorWeilCoercivity` and `matrix_posDef_of_relative_conductor_budget` proves `PosDef` of `spectralFloorWeilMatrix c N`, the uniform $\frac{\kappa_{\mathrm{sp}}}{2 c^7}\|x\|^2$ spectral floor, `PosDef` of `completeWeilMatrix tiltedUnitSpline c N`, nonnegativity of `weilQuad` on all atomic test functions, and the $\frac{b_1}{c^{23}}\operatorname{poleDefect}_N(x)$ reserve across $1 \le c \le (\log N)^\alpha$ for all $0 < \alpha < 1/16$.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Alternating terminal vectors $y_n = (-1)^n \mathbf{1}_{(N - H, N]}$ ($H = \lfloor N / c^8 \rfloor$) projected onto $(V_{\lfloor N^\theta \rfloor})^\perp$ experience cubic-spline finite-difference cancellation $\|f_y\|_{L^2}^2 / G \asymp c^{-7}\|y\|^2$ and vanishing prime sum, refuting any $c^{-(2+\varepsilon)}$ global reserve on $(V_{\lfloor N^\theta \rfloor})^\perp$ for `tiltedUnitSpline`; invoking `logarithmicReserveMatrix.PosDef` at $c = (\log N)^\alpha$ is circular because its horizon exponentiates $c^{16}$.
- **Strongest positive survivor:** Asymmetric Prefix/Terminal Reserve on $(V_1)^\perp$ (`AsymmetricTwoRegionConductorReserve`) + Quadratic-Overlap Single-Conductor Residuals (`QuadraticOverlapConductorResiduals`) + All-Vector Positivity below $1/16$ (`CompleteWeilPositivityBelowOneSixteenth`).
- **New insight:** Localizing the $O(c^9)$ overlap penalty strictly onto the separated prefix mass $P$ where $+\frac{1}{2} D_M(x)$ is order-$1$ decouples $(V_{\lfloor N^\theta \rfloor})^\perp$ coercivity ($\alpha < 1/9$) from the prefix-to-tail non-ratio balance ($\alpha < 1/16$).
