# Resolution of the finite-layer logarithmic wall-cusp question

- **Stage:** 2-fully-proven
- **Source:** [Obstacles summary §2.17](../../../reports/review-1911/obstacles-summary.md#217-the-one-smaller-question-with-the-largest-shared-payoff)

## 1. Exact cusp laws and first-moment asymptotics on $\zeta$

Let $F$ be a threshold ground state at $W_0 > 0$, $a = \operatorname{criticalAliasCoefficient}(W_0)$, $M = \int F(u)^2 e^{-8u}\,du$, and $m_F(q) = \|\mathcal{L}F(\operatorname{centredZero} q)\|^2$ on `onLineCopies`.

1. **Logarithmic Abel and vertical-line $L^2$ cusp laws** (unconditional for every confined minimizer and threshold ground state):
   $$
   \lim_{x\to+\infty} (x\log x)\int_0^\infty e^{-2xv} F(-v)^2\,dv = 4aM, \qquad
   \lim_{x\to+\infty} (x\log x)\int_{\mathbb{R}} \|\mathcal{L}F(x+iy)\|^2\,dy = 8\pi aM.
   $$
2. **Continuous boundary tail vanishing** (unconditional for every threshold ground state):
   $$
   \lim_{T\to+\infty} T \int_{|y|>T} \|\mathcal{L}F(-4+iy)\|^2\,dy = 0, \qquad
   \lim_{T\to+\infty} \frac{1}{\log T}\int_{-T}^T |y|\,\|\mathcal{L}F(-4+iy)\|^2\,dy = 0.
   $$
3. **Exact ordinate-tail and first-moment asymptotics under `FiniteOffLine`:**
   $$
   \lim_{T\to+\infty} T \sum_{\substack{q\in\mathrm{onLineCopies} \\ |\gamma_q|>T}} m_F(q) = \frac{8aM}{\pi}, \qquad
   \lim_{T\to+\infty} \frac{1}{\log T}\sum_{\substack{q\in\mathrm{onLineCopies} \\ |\gamma_q|\le T}} |\gamma_q|\,m_F(q) = \frac{8aM}{\pi}.
   $$

## 2. Saturation of crowding, sample, Poisson, and fixed-window axioms

For every $\ell \neq 0$, the profile $F_\ell(u) = \ell(1+8u)^2(\log(1/|u|))^{-1/2}\mathbf{1}_{(-1/8,0)}(u)$ lies in `CriticalHalfLineEnergyDomain` and satisfies unconditionally:
- $\frac{\log(1/h)}{h}\int_{-h}^0 F_\ell(u)^2\,du \to \ell^2 > 0$, $\frac{1}{h}\int_{-h}^0 F_\ell(u)^2\,du \to 0$, and $\frac{1}{h}\int (F_\ell(u)-F_\ell(u+h))^2 e^{-8u}\,du \to 0$;
- $\|(w+5)\mathcal{L}F_\ell(w)\| \le C|\ell|/\sqrt{\log(\|w\|+4)}$ uniformly on $\operatorname{Re} w \ge -4$, with $y\sqrt{\log|y|}\,\mathcal{L}F_\ell(iy) \to i\ell$ as $|y|\to\infty$ and bounded axis derivative $\|((iy_1+5)\mathcal{L}F_\ell(iy_1)) - ((iy_2+5)\mathcal{L}F_\ell(iy_2))\| \le K|\ell|\,|y_1-y_2|$;
- uniform rescaled sample and Poisson bounds on `onLineCopies`: $(1+y^2)\sum_{|\gamma_q-y|\le 1} m_{F_\ell}(q) \le C_1\ell^2$ and $(1+y^2)\sum_q m_{F_\ell}(q)\frac{4}{16+(y-\gamma_q)^2} \le C_2\ell^2$ for all $y\in\mathbb{R}$;
- window-width and multiplicity saturation: on any ordinate family with $c_h\log y \le \#\{q : |\gamma_q-y|\le h\}$ for $y\ge Y_h$ (in particular on `onLineCopies` under `FiniteOffLine`, and unconditionally on every Riemann–von Mangoldt ordinate grid), $y^2\sum_{|\gamma_q-y|\le h} m_{F_\ell}(q) \ge \frac{c_h}{2}\ell^2$ and $y^2\sum_q m_{F_\ell}(q)\frac{4}{16+(y-\gamma_q)^2} \ge \frac{2c_h\ell^2}{16+h^2}$ for large $y$.

Moreover, at every positive ratio $R>0$ the actual unit-$L^2$ minimizer $F_R$ of the shift-invariant half-line form `criticalHalfLineFullEnergy R` sustains $\frac{\log(1/h)}{h}\int_{-h}^0 F_R(u)^2\,du \to 8a(R)M_R > 0$ together with $\frac{1}{h}\int_{-h}^0 F_R(u)^2\,du \to 0$. Thus critical-line crowding, rescaled sample bounds, fixed-window mass capture, and the $\Gamma_{\mathbb{R}}$ jump operator alone admit rescaled transform amplitudes $\asymp |\ell|/\sqrt{\log y}$ and sustain the nonzero wall-cusp coefficient without any vanishing subsequence $h_j\downarrow 0$; any exclusion of finite layers must use the multiplicative structure of the arithmetic prime source beyond these axioms.

## 3. Exact equivalences, global payoff corollaries, and outer-tail boundary

1. **Six-way equivalence on $\zeta$:** `FiniteOffLine → RiemannHypothesis` is equivalent to each of: (i) existence under `¬RH ∧ FiniteOffLine` of $h_j\downarrow 0$ with $\frac{\log(1/h_j)}{h_j}\int_{-h_j}^0 F(u)^2\,du \to 0$ for the first ground state; (ii) existence of $x_j\to+\infty$ with $(x_j\log x_j)\int_{\mathbb{R}} \|\mathcal{L}F(x_j+iy)\|^2\,dy \to 0$; (iii) finiteness of $\sum_q |\gamma_q|\,m_F(q)$; (iv) existence of $T_j\to+\infty$ with $\frac{1}{\log T_j}\sum_{|\gamma_q|\le T_j} |\gamma_q|\,m_F(q) \to 0$; and (v) existence of $T_j\to+\infty$ with $T_j\sum_{|\gamma_q|>T_j} m_F(q) \to 0$.
2. **Unconditional payoff corollaries of any equivalent target:**
   - global elimination of every single off-line quartet: $\forall \rho_0,\ \neg\operatorname{HasSingleOffLineQuartet}(\rho_0)$ (without assuming `FiniteOffLine`, since `HasSingleOffLineQuartet` implies `FiniteOffLine`);
   - global QIC dichotomy `realPacketNegIndex = 0 ∨ realPacketNegIndex = ⊤` and unconditional `TwoIntervalRadialExclusionLaw`;
   - removal of the quartet alias in PDR: for every $\frac{1}{2}<\beta<1$ and $\gamma>0$, boundedness of the `(2,3,6)` ordinary-prime $\theta$-dilation residuals is equivalent to `RiemannHypothesis`;
   - removal of the two-wave proper-power characterization of off-line quartets in PPC;
   - collapse of `riemannHypothesis_iff_three_atoms` to `RiemannHypothesis ↔ ZerosApproachLine ∧ ZetaLandingLaw`.
3. **Sharp outer-tail non-implication:** For every $\sigma_0 \in (\frac{1}{2},1)$, an explicit configuration $Z_{\sigma_0}$ with an isolated finite nonempty outer layer at $\operatorname{Re}\rho = \sigma_0$ above an infinite off-line background approaching $\operatorname{Re}s = \frac{1}{2}$ satisfies `AbscissaLawAt Z 0` and `ApproachesLine Z`, yet has `zeroAbscissa Z = σ_0` and violates `LinearAbscissaLaw Z` and `AbscissaLaw Z`.

## Proofs

**§1.** Let $S(h)=\int_{-h}^0 F(u)^2\,du$. Tonelli's theorem gives $\int_0^\infty e^{-2xv}F(-v)^2\,dv = \int_0^\infty e^{-t} S(t/(2x))\,dt$, so $(x\log x)\int_0^\infty e^{-2xv}F(-v)^2\,dv = \frac{1}{2}\int_0^\infty g_x(t)\,dt$ with $g_x(t) = (2x\log x)e^{-t}S(t/(2x))$. Since $\frac{\log(1/h)}{h}S(h)\to 8aM$ and $S(h)\le \|F\|_2^2$, splitting at $t=\sqrt{x}$ bounds $g_x(t)$ uniformly for large $x$ by $C(t + t^4)e^{-t}\in L^1(0,\infty)$, while $g_x(t)\to 8aM\,t e^{-t}$ pointwise; dominated convergence gives $4aM$, and vertical Plancherel gives $8\pi aM$.

For $G_{-4}(u)=e^{-4u}F(u)$, `criticalState_tendsto_weighted_sq_increment_div` gives $\int (G_{-4}(u)-G_{-4}(u+h))^2\,du = o(h)$. At $h=1/(2U)$, $1-\cos(hy)\ge 1/16$ on $[U,2U]$, so increment Plancherel gives $\int_U^{2U}\|\mathcal{L}F(-4+iy)\|^2\,dy = o(1/U)$. Summing $U=2^k T$ yields $T\int_{|y|>T}\|\mathcal{L}F(-4+iy)\|^2\,dy \to 0$, and Cesàro summation over dyadic shells yields $\frac{1}{\log T}\int_{-T}^T |y|\,\|\mathcal{L}F(-4+iy)\|^2\,dy \to 0$.

Under `FiniteOffLine`, `localized_high_frequency_mass` gives $y^2\big(\frac{a}{2}\|\mathcal{L}F(-4+iy)\|^2 + \sum_{|y-\gamma_q|<\eta y} m_F(q)\frac{4}{16+(y-\gamma_q)^2}\big)\to 4aM$ for every $\eta\in(0,1/4)$. Subtracting the $o(1/T)$ continuous integral and integrating on $[T,\lambda T]$ ($\lambda>1$) or dividing by $y$ and integrating on $[1,T]$ exchanges with the nonnegative series by Tonelli. For $|\gamma_q|$ above a fixed threshold $T_0(\eta)$, the truncated Cauchy integral on $|y-\gamma_q|<\eta y$ lies between $(1-\eta)\pi$ and $\pi$, squeezing $T\sum_{|\gamma_q|>T} m_F(q)$ and $\frac{1}{\log T}\sum_{|\gamma_q|\le T}|\gamma_q|m_F(q)$ to $\frac{8aM}{\pi}$ as $\eta\downarrow 0$.

**§2.** `wallLogProfile (1/8)` lies in `CriticalHalfLineEnergyDomain`, and $\psi(u)=\min(\max(1+8u,0),1)^2$ is bounded and globally Lipschitz, so $F_\ell = \ell\psi\cdot\mathrm{wallLogProfile}(1/8)$ lies in `CriticalHalfLineEnergyDomain`. Since $\psi(u)\to 1$ at $0^-$, $F_\ell$ has wall-cusp limit $\ell^2$. On $v\in(0,1/8)$, $g(v)=F_1(-v)=(1-8v)^2(\log(1/v))^{-1/2}$ satisfies $g(0^+)=g(1/8^-)=0$ and $g'(v)=g_1(v)-g_2(v)$ with $g_1(v)=\frac{(1-8v)^2}{2v(\log(1/v))^{3/2}}$ positive and antitone on $(0,1/8)$ (since $\log(1/v)>\log 8>3/2$) and $g_2'\in L^1(0,1/8)$. Integration by parts gives $w\mathcal{L}F_1(w)=-\int_0^{1/8}g'(v)e^{-wv}\,dv$. Splitting $\int_0^{1/8}g_1(v)e^{-wv}\,dv$ at $\delta=\min(1/(\|w\|+8),1/16)$ bounds $(0,\delta]$ by $\int_0^\delta \frac{e^{1/2}\,dv}{2v(\log(1/v))^{3/2}} = \frac{e^{1/2}}{\sqrt{\log(1/\delta)}}$ and $[\delta,1/8)$ by integration by parts and antitonicity of $g_1$ as $\le \frac{2e^{1/2}g_1(\delta)}{\|w\|} \ll (\log(\|w\|+8))^{-3/2}$. On $w=iy$ ($|y|\to\infty$), splitting at $\delta=1/|y|$ gives $\int_0^{1/|y|}g_1(v)(e^{-iyv}-1)\,dv = O((\log|y|)^{-3/2})$ and $\int_0^{1/|y|}g_1(v)\,dv = (\log|y|)^{-1/2}+O(1/|y|)$, so $y\sqrt{\log|y|}\,\mathcal{L}F_\ell(iy)\to i\ell$. Combining with `lorentzMass_le_log` yields the global sample and Poisson upper bounds on `onLineCopies`, and combining with window crowding $\ge c_h\log y$ yields the lower bounds.

**§3.** Each of (i)–(v) contradicts §1 or `criticalState_tendsto_log_div_mul_terminal_sq` whenever `¬RH ∧ FiniteOffLine` supplies a threshold ground state via `not_rh_gives_ground_state`; conversely `FiniteOffLine → RH` discharges all five vacuously via `finiteLayer_ecs_b13_tfae`. Every corollary follows from `HasSingleOffLineQuartet.finiteOffLine`, `finiteLayer_ecs_b13_tfae`, `twoIntervalRadialExclusionLaw_iff_no_singleQuartet`, `ordinary_prime_recurrences_iff_rh_or_singleQuartet`, `hasSingleOffLineQuartet_iff_two_properPower_waves`, and `riemannHypothesis_iff_three_atoms`. Finally, `seqPairConfig` with $\delta(0)=\sigma_0-\frac{1}{2}$ and $\delta(n+1)=\frac{\sigma_0-1/2}{n+3}$ furnishes $Z_{\sigma_0}$.
