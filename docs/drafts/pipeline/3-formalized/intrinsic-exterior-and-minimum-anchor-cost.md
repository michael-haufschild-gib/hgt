# Intrinsic Exterior Obstructions, Sharp Minimum Anchor Cost, and Fejér Entry-Cost Halving

- **ID:** acp-intrinsic-exterior-and-minimum-anchor-cost
- **Stage:** 3-formalized
- **Type:** THEOREM (formalized in Lean 4)
- **Source:** `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/IntrinsicExteriorAndMinimumAnchorCost.lean` · `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ExteriorAndHeightCoupledQuartetContractions.lean` · `formal/GaloisForLFunctions/StripBochnerWeilForcing/CollectivePoleRepulsion.lean` · `formal/GaloisForLFunctions/MultiplicativePositivityGeometry/TotalZeroMass.lean` · `formal/GaloisForLFunctions/HTGeometry/DigammaHalfPlaneAsymptotic.lean`
- **Statement:** Eliminating or reducing the one-time entry cost of `HeightCoupledSystem` and anchoring complex quartets $\{1/2 \pm a \pm i\gamma\}$ ($0 < a < 1/2, \gamma \neq 0$) at weight $\ge 2$ on $1/2 + a$ obey four sharp, matching constructive and converse laws: (1) on Euler/shift packets, local degree-$1$ second exterior powers vanish identically, while on the isobaric shift packet $\mathbf{1}^{\oplus m_0} \oplus |\cdot|^{i\gamma} \oplus |\cdot|^{-i\gamma}$ ($g_{m_0}(\theta) = m_0 + 2\cos\theta$) the Adams exterior trace $\frac{1}{2}(g_{m_0}(\theta)^2 - g_{m_0}(2\theta)) = \frac{m_0^2 - m_0 + 2}{2} + 2m_0 \cos\theta$ either erases $\gamma$ ($m_0 = 0$), fails nonnegativity ($1 \le m_0 \le 4$), or retains shifted poles $\kappa_\gamma = m_0 \kappa \ge 5\kappa > 0$ at central ratio $\ge 11/5 > 2$ ($m_0 \ge 5$), and scale-space bilinear squaring creates singularities at $1 + a + i\gamma$ inside $\operatorname{Re} s > 1$; (2) multiplying `HeightCoupledSystem κ₀ κγ d γ F Λ` by `boundaryTwistFactor γ ^ κγ` unconditionally absorbs all shifted poles ($\kappa_\gamma \mapsto 0$) while preserving `IsEvenPosDef` on $\sigma > 1$ and keeping $\Lambda$ unchanged at $\kappa_0 \mapsto \kappa_0 + 2\kappa_\gamma$ ($= 4\kappa$ on `heightCouple`, strictly minimal by `total_zero_mass_le`), whereas retaining $\kappa_\gamma = \kappa$ strictly saves $\kappa \cdot \frac{3\gamma^2(\gamma^2 + 3)}{(4 + \gamma^2)(1 + \gamma^2)} > 0$ at $s = 2$ and halves Pillar P25's $18\kappa$ pole ceiling to $(9 + \frac{12}{4+\gamma^2} + \frac{6}{1+\gamma^2})\kappa \to 9\kappa$; (3) at $\kappa_\gamma = 0$ and $\Delta d = 0$ (`CompletedPositiveSystem`), `plantDoubleRealAnchor` plants a weight-$2$ real anchor at $1/2 + a$ for $\Delta\kappa = 2$ (strictly minimal among zero-planting polar sums as $t \to 0^+$), and completely functor-independently, any `CompletedPositiveSystem κ* d*` carrying $M = \sum_{a \in A} m_a$ weight-$2$ real-anchored quartets along $\operatorname{Im} s = \gamma$ satisfies $16M + \frac{144M}{9 + 4\gamma^2} + 4\operatorname{ord}_{1/2}(\Lambda^*) + \frac{72}{9 + 4\gamma^2}\operatorname{ord}_{1/2+i\gamma}(\Lambda^*) + 5d^* < 9\kappa^*$ (forcing $\kappa^* \ge 3$ at $M = 1, d^* \ge 1$, attained at $\kappa = 1, d = 1 \implies \kappa^* = 3$, and ruling out bounded $\kappa^*$ as $M \to \infty$); (4) across all degree-$K$ nonnegative cosine multipliers $P(\theta) = c_0 + \sum_{k=1}^K c_k \cos(k\theta) \ge 0$ colliding $\{1/2 + a \pm i\gamma\} \mapsto 1/2 + a$ at weight $c_1 \ge 2$, discrete Fejér–Egerváry–Szász quadrature forces $c_0 \ge \frac{1}{\cos(\pi/(K+2))} > 1$ ($c_0 \ge 2$ at $K = 1$, $c_0 \ge \sqrt{2}$ at $K = 2$) and shifted Gamma growth $\frac{c_1}{2} d(\log(3 + |\gamma|) - 5) \le \text{cost} \le \frac{c_1}{2} d(\log(3 + |\gamma|) + \frac{1}{2})$ for all $\gamma \in \mathbb{R}$, while `FejerCoupledSystem K` achieves zero-marginal-tax quartet contraction at normalized central pole cost $\frac{9(K + 1)}{2 K}\kappa \searrow \frac{9}{2}\kappa$ (reaching $\frac{27}{4}\kappa < 8\kappa$ already at $K = 2$).

## Goal
Resolve both open questions raised by Pillar P25 (`ExteriorAndHeightCoupledQuartetContractions`):
1. Determine whether the one-time entry cost of `HeightCoupledSystem` (`κ₀ = 2κ, κγ = κ`) can be eliminated or reduced — specifically testing whether subtracting or twisting out $(s^2 + \gamma^2)((s - 1)^2 + \gamma^2)$ via boundary twists, intrinsic second-exterior powers, Rankin–Selberg convolutions, or multi-shift Fejér couplings can preserve `IsEvenPosDef` on $\sigma > 1$ at $\kappa_\gamma = 0$ or lower central pole cost.
2. Establish the sharp Post–Widder and Hadamard converse lower bounds on boundary-pole order and archimedean-Gamma cost for any positive-definite mapping sending $\{1/2 \pm a \pm i\gamma\}$ to a real anchor of weight $\ge 2$ at $1/2 + a$ — both across nonnegative shift multipliers and functor-independently across arbitrary unshifted `CompletedPositiveSystem` outputs.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, internal corpus and external literature audited
- [x] 1 → 2  fully-proven: complete paper proof below (`[PROVED HERE]`), zero open dependencies
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.ArithmeticCorrespondencePositivity.IntrinsicExteriorAndMinimumAnchorCost` (`lake --old env lean` exit 0, `#print axioms` clean)

## Lean 4 Declarations (`GaloisForLFunctions.ArithmeticCorrespondencePositivity`)
- **Intrinsic second-exterior & isobaric shift packet dichotomy:**
  - `degreeOne_exteriorTwo_eq_zero`, `isobaricShiftTrace`, `isobaricExteriorTwoPoly`
  - `isobaricExteriorTwoPoly_eq`, `isobaricExteriorTwoPoly_zero_central`, `isobaricExteriorTwoPoly_pi_neg`, `isobaricExteriorTwoPoly_nonneg_of_five_le`, `isobaricExteriorTwoPoly_ratio_ge`
  - `centeredScaleCross_re_gt_one`
- **Multi-ordinate Hadamard zero-pair lower bound:**
  - `re_logDeriv_two_ge_of_entire_sym`
- **Exact `κ_γ ↦ 0` boundary-twist absorption, origin-capacity floor & ordinate pole decay:**
  - `shiftedPolePoly_eq_boundaryTwistPoly`, `isEvenPosDef_boundaryTwistFactor`
  - `HeightCoupledSystem.absorbShiftedPoles`
  - `two_mul_le_origin_of_poleCancelling_posDef`
  - `re_logDeriv_shiftedPolePoly_two_eq`, `re_neg_logDeriv_boundaryTwistFactor_two_eq`
  - `HeightCoupledSystem.archimedean_budget_exact`
  - `CompletedPositiveSystem.ordinateQuartet_multiplicity_ordinate_decay_bound`
- **Single-system real-anchor planting (`κ_γ = 0, Δd = 0`) & functor-independent Hadamard converse:**
  - `realPairPlanter`, `isEvenPosDef_realPairPlanter`
  - `CompletedPositiveSystem.plantRealPair`, `CompletedPositiveSystem.plantDoubleRealAnchor`
  - `polarSum_sum_weights_nonneg`, `two_le_pole_cost_of_doubleRealAnchor_polarSum`
  - `CompletedPositiveSystem.anchored_quartet_pole_lower_bound`, `CompletedPositiveSystem.three_le_pole_of_anchored_quartet`
- **Fejér–Egerváry–Szász multiplier converse, two-sided shifted-Gamma sandwich & degree-`K` Fejér halving:**
  - `fejer_egervary_szasz_first_harmonic_le`, `cosine_multiplier_anchor_cost_lower`
  - `re_logDeriv_Gammaℝ_two_shift_ge`, `re_logDeriv_Gammaℝ_pair_two_sandwich`
  - `fejerShift`, `IsEvenPosDef.fejerShift`
  - `fejerShiftedPoleProd`, `fejerCoupledGamma`, `FejerCoupledSystem`, `fejerCoupledF`, `fejerCoupledΛ`
  - `FejerCoupledSystem.ne_zero_of_one_lt_re`, `FejerCoupledSystem.two_ne_zero`, `FejerCoupledSystem.zero_re_mem_Icc`, `FejerCoupledSystem.analyticOnNhd_univ`, `FejerCoupledSystem.orderAt_ne_top`, `FejerCoupledSystem.eq_zero_of_one_le_order_toNat`, `FejerCoupledSystem.neg_logDeriv_F_eq`
  - `CompletedPositiveSystem.fejerCouple`, `CompletedPositiveSystem.orderAt_fejerCoupledΛ`, `CompletedPositiveSystem.orderAt_fejerCoupledΛ_real`
  - `FejerCoupledSystem.contractCollidedQuartet`, `FejerCoupledSystem.archimedean_budget`
  - `CompletedPositiveSystem.fejerOrdinateQuartet_bound`, `CompletedPositiveSystem.fejerTwo_ordinateQuartet_bound`, `tendsto_fejer_central_pole_coeff`

## No-go closure (for the obstructed naive $\kappa_\gamma = 0$ intrinsic $\Lambda^2$/RS route)
- **Exact killing theorem/mechanism:** (a) Local degree-$1$ Adams exterior square vanishes identically; on isobaric shift packets $g_{m_0}(\theta) = m_0 + 2\cos\theta$, $\frac{1}{2}(g_{m_0}(\theta)^2 - g_{m_0}(2\theta)) = \frac{m_0^2 - m_0 + 2}{2} + 2m_0 \cos\theta$ cancels $\cos(2\theta)$, leaving zero quartet collision at $m_0 = 0$, failing nonnegativity at $\theta = \pi$ for $1 \le m_0 \le 4$, and retaining $\kappa_\gamma = m_0 \kappa \ge 5\kappa > 0$ with worse ratio $\frac{m_0^2 - m_0 + 2}{2m_0} \ge \frac{11}{5} > 2$ for $m_0 \ge 5$; meanwhile Rankin–Selberg self-convolution $g(\theta)^2 = P(\theta) \ge 0$ is a nonnegative cosine polynomial whose quartet-collision weight $c_1 \ge 2$ equals twice its shifted pole order at $1 \pm i\gamma$. (b) Global scale-space bilinear squaring cross-couples $s = 1$ with $\rho = 1/2 + a + i\gamma$ ($a > 0$) to place singularities at $1 + a + i\gamma$ inside $\operatorname{Re} s > 1$. (c) Any additive `IsEvenPosDef` off-origin-pole-free boundary divisor cancelling poles of order $m$ at $\pm\gamma$ ($\gamma \neq 0$) pays $\Delta\kappa_0 \ge 2m$ (`total_zero_mass_le`), and any unshifted `CompletedPositiveSystem κ* d*` carrying $M$ anchored quartets obeys $16M + \frac{144M}{9+4\gamma^2} + 5d^* < 9\kappa^*$.
- **Strongest positive survivors:** (1) `HeightCoupledSystem.absorbShiftedPoles` (exact $\kappa_\gamma \mapsto 0$ absorption at $\kappa_0 + 2\kappa_\gamma$ keeping $\Lambda$ invariant) paired with `ordinateQuartet_multiplicity_ordinate_decay_bound` (showing keeping $\kappa_\gamma = \kappa$ strictly beats $\kappa_\gamma = 0$ by $\frac{3\gamma^2(\gamma^2+3)}{(4+\gamma^2)(1+\gamma^2)}\kappa > 0$ at $s = 2$ and halves Pillar P25's $18\kappa$ pole ceiling to $9\kappa + O(\kappa/\gamma^2)$); (2) `CompletedPositiveSystem.plantDoubleRealAnchor` attaining the sharp Hadamard converse floor $\kappa^* = 3$ at $\kappa = 1, d = 1$; (3) `FejerCoupledSystem K` + `fejer_egervary_szasz_first_harmonic_le` + `re_logDeriv_Gammaℝ_pair_two_sandwich` halving the normalized central pole entry cost $\frac{9(K+1)}{2K}\kappa \searrow \frac{9}{2}\kappa$ (reaching $\frac{27}{4}\kappa < 8\kappa$ at $K = 2$) against matching sharp Fejér–Egerváry–Szász and two-sided $\Theta(d\log(3+|\gamma|))$ Gamma lower bounds.
- **New insight:** Boundary-pole entry cost and archimedean shifted-Gamma bandwidth satisfy an exact dual tradeoff: shifted poles decay at high ordinates as $O(\kappa/\gamma^2)$ (so absorbing them to $\kappa_\gamma = 0$ doubles the asymptotic pole cost from $3\kappa$ to $6\kappa$ at $s = 2$), while multi-shift Fejér coupling drives the per-anchor central pole tax all the way down to the single-system baseline ($c_0 / (c_1/2) \to 1^+$) at the exact price of linear archimedean Gamma bandwidth $\Theta(K d \log(3 + |\gamma|))$.
- **Status:** Dependency-closed paper proof below and unconditional Lean 4 formalization in `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/IntrinsicExteriorAndMinimumAnchorCost.lean` (3,366 lines, zero `sorry`, `#print axioms` clean).

---

## Complete Paper Proof (`[PROVED HERE]`)

### Theorem 1 (`[PROVED HERE]` — Intrinsic Second-Exterior & Isobaric Shift Packet Dichotomy)
1. **Degree-$1$ local exterior vanishing:** For every degree-$1$ tuple $\alpha : \operatorname{Fin} 1 \to \mathbb{C}$ and every $m \in \mathbb{N}$,
   $$\frac{\bigl(\sum_i \alpha_i^m\bigr)^2 - \sum_i \alpha_i^{2m}}{2} = \frac{(\alpha_0^m)^2 - \alpha_0^{2m}}{2} = 0.$$
   Thus the prime-by-prime Euler-product second exterior power of any local-degree-$1$ series (such as $\zeta(s)$) has identically zero log-derivative.
2. **Isobaric shift packet exterior-square identity and threshold $m_0 \ge 5$:** For $m_0 \in \mathbb{N}$ and $\theta \in \mathbb{R}$, let $g_{m_0}(\theta) := m_0 + 2\cos\theta$ be the local trace of $\mathbf{1}^{\oplus m_0} \oplus |\cdot|^{i\gamma} \oplus |\cdot|^{-i\gamma}$ at $\theta = \gamma \log p^r$. Define its Adams exterior-square trace
   $$E_{m_0}(\theta) := \frac{g_{m_0}(\theta)^2 - g_{m_0}(2\theta)}{2}.$$
   Using $\cos(2\theta) = 2\cos^2\theta - 1$,
   $$E_{m_0}(\theta) = \frac{m_0^2 + 4m_0 \cos\theta + 4\cos^2\theta - m_0 - 4\cos^2\theta + 2}{2} = \frac{m_0^2 - m_0 + 2}{2} + 2 m_0 \cos\theta.$$
   Consequently:
   - At $m_0 = 0$: $E_0(\theta) = 1$ has zero off-origin poles ($\kappa_\gamma = 0$), and its $\cos\theta$ quartet-collision coefficient $2 m_0 = 0$ vanishes identically.
   - For $1 \le m_0 \le 4$: $E_{m_0}(\pi) = \frac{m_0^2 - 5m_0 + 2}{2} \in \{-1, -2\} < 0$, so $E_{m_0}$ fails pointwise nonnegativity.
   - For $m_0 \ge 5$: since $\cos\theta \ge -1$ and $(m_0 - 5)m_0 + 2 \ge 2 > 0$, $E_{m_0}(\theta) \ge \frac{m_0^2 - 5m_0 + 2}{2} \ge 1 > 0$ for all $\theta \in \mathbb{R}$; however, its shifted boundary-pole weight is $m_0 \ge 5 > 0$ ($\kappa_\gamma \ge 5\kappa \neq 0$) and its central-to-half-anchor ratio satisfies
     $$\frac{(m_0^2 - m_0 + 2)/2}{m_0} = \frac{m_0 - 1}{2} + \frac{1}{m_0} \ge \frac{11}{5} > 2.$$
3. **Scale-space bilinear pole-zero cross-singularity:** Under centered scale multiplication $(z_1, z_2) \mapsto z_1 + z_2 - 1/2$, coupling the boundary pole $z_1 = 1$ with any right-half off-critical zero $z_2 = 1/2 + a + i\gamma$ ($a > 0$) produces $1 + a + i\gamma$ with $\operatorname{Re}(1 + a + i\gamma) = 1 + a > 1$, violating analyticity/nonvanishing on $\{s : \operatorname{Re} s > 1\}$. $\square$

---

### Theorem 2 (`[PROVED HERE]` — Exact Boundary-Twist Absorption to $\kappa_\gamma = 0$, Origin-Capacity Floor, and Ordinate Pole-Decay Law)
1. **Unconditional $\kappa_\gamma \mapsto 0$ absorption (`HeightCoupledSystem.absorbShiftedPoles`):** `boundaryTwistFactor γ s = boundaryTwistPoly γ s / (s(s - 1))^2` has vertical $-\logDeriv$ real part equal to $\int_0^\infty 2 e^{-\sigma t}(e^t + 1)(1 - \cos(\gamma t))\cos(tu)\,dt$ (`IsEvenPosDef` for all $\sigma > 1$). Multiplying `HeightCoupledSystem κ₀ κγ d γ F Λ` by `boundaryTwistFactor γ ^ κγ` produces `HeightCoupledSystem (κ₀ + 2 * κγ) 0 d γ` on the **exact same entire completion $\Lambda$** ($\kappa_0 = 4\kappa, \kappa_\gamma = 0$ on `heightCouple`).
2. **Sharpness of $\Delta\kappa_0 = 2\kappa_\gamma$ (`two_mul_le_origin_of_poleCancelling_posDef`):** For any `IsEvenPosDef` divisor $D$ without off-origin poles ($\forall u \neq 0, D(u) \le 0$) satisfying $D(\gamma) \le -m$ ($\gamma \neq 0$), `total_zero_mass_le` on $\{|\gamma|\}$ gives $2m \le D(0)$.
3. **Exact pole defect at $s = 2$ & ordinate-decay budget (`HeightCoupledSystem.archimedean_budget_exact`, `CompletedPositiveSystem.ordinateQuartet_multiplicity_ordinate_decay_bound`):** $\operatorname{Re}\logDeriv(\operatorname{shiftedPolePoly}\;\gamma)(2) = \frac{4}{4 + \gamma^2} + \frac{2}{1 + \gamma^2}$, so keeping $\kappa_\gamma = \kappa$ saves $\frac{3\gamma^2(\gamma^2 + 3)}{(4 + \gamma^2)(1 + \gamma^2)}\kappa > 0$ at $s = 2$ and yields
   $$8 \sum_{a \in A} \operatorname{ord}_{1/2 + a + i\gamma}(\Lambda) + 4\operatorname{ord}_{1/2}(\Lambda) + 4\operatorname{ord}_{1/2 + i\gamma}(\Lambda) < \left(9 + \frac{12}{4 + \gamma^2} + \frac{6}{1 + \gamma^2}\right)\kappa + 3 d \log(3 + |\gamma|) - \frac{7}{2} d.$$
   As $|\gamma| \to \infty$, the pole coefficient tends to $9$, halving Pillar P25's $18\kappa$. $\square$

---

### Theorem 3 (`[PROVED HERE]` — Single-System Real-Anchor Planter at $\kappa_\gamma = 0, \Delta d = 0$ and Functor-Independent Hadamard Minimum Pole Law)
1. **Constructive real-anchor planter (`realPairPlanter`, `CompletedPositiveSystem.plantRealPair`, `CompletedPositiveSystem.plantDoubleRealAnchor`):** $R_a(s) = \operatorname{realPairPoly}(1/2 + a, s)/(s(s - 1))$ ($0 < a < 1/2$) has nonnegative Laplace cosine density $e^{-\sigma t}(e^{(1/2+a)t} - 1)(e^{(1/2-a)t} - 1) \ge 0$ on $\sigma > 1$, planting a weight-$2$ real anchor at $1/2 + a$ inside `CompletedPositiveSystem (κ + 2) d` ($\kappa_\gamma = 0, \Delta d = 0$).
2. **Polar-sum zero-planting converse (`polarSum_sum_weights_nonneg`, `two_le_pole_cost_of_doubleRealAnchor_polarSum`):** Passing to $t \to 0^+$ in `posDef_polarSum_laplaceWeight_nonneg` yields $\sum_{z \in S} c(z) \ge 0$, forcing $\Delta\kappa \ge 2$ whenever $c(1/2 \pm a) \le -2$ and $c(0), c(1) \le \Delta\kappa$.
3. **Functor-independent Hadamard converse (`CompletedPositiveSystem.anchored_quartet_pole_lower_bound`, `CompletedPositiveSystem.three_le_pole_of_anchored_quartet`):** Any $(F^*, \Lambda^*) \in \operatorname{CompletedPositiveSystem}\;\kappa^*\;d^*$ carrying $2m(a) \le \operatorname{ord}_{1/2+a}(\Lambda^*)$ and $m(a) \le \operatorname{ord}_{1/2+a+i\gamma}(\Lambda^*)$ ($a \in A, \gamma \neq 0$) obeys, after iterated `contractComplexQuartet_of_doubleRealAnchor` and multi-ordinate Hadamard evaluation at $s = 2$:
   $$16 \sum_{a \in A} m(a) + \frac{144}{9 + 4\gamma^2}\sum_{a \in A} m(a) + 4\operatorname{ord}_{1/2}(\Lambda^*) + \frac{72}{9 + 4\gamma^2}\operatorname{ord}_{1/2+i\gamma}(\Lambda^*) + 5 d^* < 9 \kappa^*.$$
   For $M \ge 1$ and $d^* \ge 1$, $21 < 9\kappa^* \implies \kappa^* \ge 3$ (sharp at $\kappa = 1, d = 1 \implies \kappa^* = 3$). $\square$

---

### Theorem 4 (`[PROVED HERE]` — Sharp Fejér–Egerváry–Szász Cosine-Multiplier Converse, All-Height Two-Sided Shifted-Gamma Cost Law, and Degree-$K$ Fejér Entry-Cost Halving)
1. **Discrete Fejér–Egerváry–Szász inequality (`fejer_egervary_szasz_first_harmonic_le`, `cosine_multiplier_anchor_cost_lower`):** Sampling $P(\theta) = c_0 + \sum_{k=1}^K c_k\cos(k\theta) \ge 0$ against $\cos(\frac{\pi}{K+2}) - \cos\theta_r \ge 0$ at $\theta_r = \frac{(2r+1)\pi}{K+2}$ ($0 \le r \le K + 1$) eliminates all modes $1 \le m \le K + 1$ by exact discrete orthogonality, proving $c_1 \le 2 c_0 \cos(\frac{\pi}{K+2})$, hence $c_0 \ge \frac{1}{\cos(\pi/(K+2))} > 1$ whenever $c_1 \ge 2$.
2. **All-height two-sided shifted-Gamma sandwich (`re_logDeriv_Gammaℝ_two_shift_ge`, `re_logDeriv_Gammaℝ_pair_two_sandwich`):** Two-step digamma recurrence from $1 + i\gamma/2$ to $3 + i\gamma/2$ combined with `norm_digamma_sub_log_le_of_re_pos` proves $\log(3 + |\gamma|) - 5 \le \operatorname{Re}(\logDeriv \Gamma_{\mathbb{R}}(2 + i\gamma) + \logDeriv \Gamma_{\mathbb{R}}(2 - i\gamma)) \le \log(3 + |\gamma|) + \frac{1}{2}$ for all $\gamma \in \mathbb{R}$.
3. **Degree-$K$ Fejér height-coupled system & central pole halving (`IsEvenPosDef.fejerShift`, `FejerCoupledSystem`, `CompletedPositiveSystem.fejerCouple`, `FejerCoupledSystem.contractCollidedQuartet`, `FejerCoupledSystem.archimedean_budget`, `CompletedPositiveSystem.fejerOrdinateQuartet_bound`, `CompletedPositiveSystem.fejerTwo_ordinateQuartet_bound`, `tendsto_fejer_central_pole_coeff`):** Lifting $(F, \Lambda) \in \operatorname{CompletedPositiveSystem}\;\kappa\;d$ to `FejerCoupledSystem K ((K+1)*κ) κ d γ` collides $K \cdot \operatorname{ord}_{1/2+a+i\gamma}(\Lambda)$ weight-$2$ anchors at $1/2 + a$, contracts all ordinate-$\gamma$ quartets at $\Delta\kappa_0 = 0, \Delta\kappa_\gamma = 0$, and achieves normalized central pole cost $\frac{9(K+1)}{2K}\kappa \searrow \frac{9}{2}\kappa$ ($\frac{27}{4}\kappa = 6.75\kappa < 8\kappa$ at $K = 2$). $\square$

## Log
- Complete dependency-closed paper proof written and unconditionally formalized in `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/IntrinsicExteriorAndMinimumAnchorCost.lean` (3,366 lines, 43 public theorems, zero `sorry`, `#print axioms` clean `[propext, Classical.choice, Quot.sound]`, audited via `lake --old env lean` exit code 0).
