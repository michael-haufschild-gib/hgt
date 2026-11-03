# Intrinsic Control of the Right Half-Port via Shifted and Critical-Line Flux Identities

- **ID:** wd-right-half-port-critical-line-flux-control
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-0211/obstacles-summary.md · WindowPortFlux
- **Statement:** Integration-by-parts $O(1/(|t|+1))$ upgrade and 6-way zero-free window rigidity equivalence for `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree`, shifted-abscissa intrinsic decomposition `rightHalfPort = vertFlux σ₁ + horizCapFlux (1/2) σ₁` giving $O(e^{(\sigma_1 - 1/2)t}/(t+1))$ decay and boundary Laplace integrability from $[1/2, 3/2]$ alone, 5-way uniform boundedness equivalence `‖𝒫_+(t)‖ ≤ M ↔ local RH`, and unconditional Burnol, double-log typical, and micro-Planck right-port decay laws for $\zeta$.

## Goal
Analyze and maximally extend `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree` to control `rightHalfPort` ($\mathcal{P}_+(t)$) alone:
1. Upgrade `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree` from $O(1)$ to $O(1/(|t|+1)) \in L^2(0, \infty)$ and determine the exact necessary-and-sufficient scope of $\sigma_1 = 1/2$ control on boundary-regular centered windows.
2. Control `rightHalfPort` alone when critical-line or corridor zeros of $A_N$ ARE present (where $\sigma_1 = 1/2$ is obstructed), both intrinsically on $[1/2, 3/2] \times [y_1, y_2]$ via shifted vertical-line + short-cap integration by parts and via desingularized critical-line oscillatory modes.
3. Establish unconditional quantitative bounds on `rightHalfPort` for $\zeta$'s theta prefixes across all Burnol unit windows, almost all unit windows (double-log rate), and $(1 - O(B))V$ micro-Planck windows (where $\sigma_1 = 1/2$ applies verbatim).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `RightHalfPortCriticalLineControl.lean`, `lake --old env lean` green, `#print axioms` PASS

## Approach & Complete Paper Proofs

### §1. Oscillatory Integration by Parts & Shifted-Abscissa Intrinsic Right-Port Control (`[PROVED HERE]`)

**Theorem 1.1 (Oscillatory Vertical-Flux Decay & Short-Cap Decay).**
1. Let $y_1 \le y_2$, $\sigma \in \mathbb{R}$, $N \in \mathbb{N}$, and assume $A_N(\sigma + i y) \ne 0$ for all $y \in [y_1, y_2]$. Then there exists $C_V > 0$ such that for all $t \in \mathbb{R}$,
   $$\|\mathrm{vertFlux}(\sigma, y_1, y_2, N, t)\| \le \frac{C_V e^{(\sigma - 1/2) t}}{|t| + 1}.$$
2. Let $\frac{1}{2} \le \sigma_1$, $y_1, y_2 \in \mathbb{R}$, $N \in \mathbb{N}$, and assume $A_N(x + i y_j) \ne 0$ for all $x \in [1/2, \sigma_1]$ and $j \in \{1, 2\}$. Then there exists $C_H > 0$ such that for all $t \ge 0$,
   $$\|\mathrm{horizCapFlux}(1/2, \sigma_1, y_1, y_2, N, t)\| \le \frac{C_H e^{(\sigma_1 - 1/2) t}}{t + 1}.$$

*Proof.*
(1) Write $\mathrm{vertFlux}(\sigma, y_1, y_2, N, t) = \frac{1}{2\pi} e^{(\sigma - 1/2) t} \int_{y_1}^{y_2} e^{i t y} g(y)\,dy$, where $g(y) := L_N(\sigma + i y)$ has continuous derivative $g'(y) = i L_N'(\sigma + i y)$ on $[y_1, y_2]$ by `analyticAt_thetaLogDeriv`. Let $M_0 := \sup_{[y_1, y_2]} \|g\|$ and $M_1 := \sup_{[y_1, y_2]} \|g'\|$. For $|t| \le 1$, $\|\int_{y_1}^{y_2} e^{i t y} g(y)\,dy\| \le M_0 (y_2 - y_1) \le \frac{2 M_0 (y_2 - y_1)}{|t| + 1}$. For $|t| > 1$, $i t \ne 0$ and $\frac{d}{dy}\big((i t)^{-1} e^{i t y} g(y)\big) = e^{i t y} g(y) + (i t)^{-1} e^{i t y} g'(y)$ on $[y_1, y_2]$; by the fundamental theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`),
$$\left\|\int_{y_1}^{y_2} e^{i t y} g(y)\,dy\right\| \le \frac{2 M_0 + M_1 (y_2 - y_1)}{|t|} \le \frac{2(2 M_0 + M_1(y_2 - y_1) + 1)}{|t| + 1}.$$
Multiplying by $(2\pi)^{-1} e^{(\sigma - 1/2) t}$ gives (1).

(2) On each horizontal segment $x \in [1/2, \sigma_1]$ at height $y \in \{y_1, y_2\}$, set $h_y(x) := L_N(x + i y)$, $h'_y(x) = L_N'(x + i y)$, bounded by $K_0, K_1$ on $[1/2, \sigma_1]$. For $t \ge 0$ and $x \in [1/2, \sigma_1]$, $\|e^{t(x - 1/2 + i y)}\| = e^{t(x - 1/2)} \le e^{(\sigma_1 - 1/2) t}$. For $0 \le t \le 1$, $\|\int_{1/2}^{\sigma_1} e^{t(x - 1/2 + i y)} h_y(x)\,dx\| \le K_0 (\sigma_1 - 1/2) e^{(\sigma_1 - 1/2) t} \le \frac{2 K_0 (\sigma_1 - 1/2) e^{(\sigma_1 - 1/2) t}}{t + 1}$. For $t > 1$, $\frac{d}{dx}\big(t^{-1} e^{t(x - 1/2 + i y)} h_y(x)\big) = e^{t(x - 1/2 + i y)} h_y(x) + t^{-1} e^{t(x - 1/2 + i y)} h'_y(x)$, giving norm $\le \frac{(2 K_0 + K_1 (\sigma_1 - 1/2)) e^{(\sigma_1 - 1/2) t}}{t} \le \frac{2(2 K_0 + K_1(\sigma_1 - 1/2) + 1) e^{(\sigma_1 - 1/2) t}}{t + 1}$. Subtracting top from bottom and dividing by $2\pi i$ yields (2). $\square$

**Theorem 1.2 (Intrinsic Shifted-Abscissa Control of `rightHalfPort` Alone & Critical-Line Specialization).**
Let $\frac{1}{2} \le \sigma_1 \le \frac{3}{2}$, $y_1 \le y_2$, $N \in \mathbb{N}$, and assume $A_N(z) \ne 0$ for all $z \in [\sigma_1, 3/2] \times [y_1, y_2]$ and $A_N(x + i y_j) \ne 0$ for all $x \in [1/2, 3/2]$, $j \in \{1, 2\}$. Then:
1. For all $t \in \mathbb{R}$, $\mathrm{rightHalfPort}(y_1, y_2, N, t) = \mathrm{vertFlux}(\sigma_1, y_1, y_2, N, t) + \mathrm{horizCapFlux}(1/2, \sigma_1, y_1, y_2, N, t)$.
2. There exists $C > 0$ such that $\|\mathrm{rightHalfPort}(y_1, y_2, N, t)\| \le C \frac{e^{(\sigma_1 - 1/2) t}}{t + 1}$ for all $t \ge 0$.
3. *(Boundary Laplace integrability)* $\int_0^\infty e^{-2(\sigma_1 - 1/2) t} \|\mathrm{rightHalfPort}(y_1, y_2, N, t)\|^2\,dt < \infty$.
4. *(Critical-line upgrade at $\sigma_1 = 1/2$)* When $A_N \ne 0$ on $[1/2, 3/2] \times [y_1, y_2]$, $\mathrm{rightHalfPort} = \mathrm{vertFlux}(1/2)$, $\|\mathrm{rightHalfPort}(y_1, y_2, N, t)\| \le \frac{C}{|t| + 1}$ for **all** $t \in \mathbb{R}$, and $\mathrm{rightHalfPort} \in L^2(0, \infty)$.

*Proof.*
(1) By `horizCapFlux_add_adjacent` on $1/2 \le \sigma_1 \le 3/2$, $\mathrm{horizCapFlux}(1/2, 3/2) = \mathrm{horizCapFlux}(1/2, \sigma_1) + \mathrm{horizCapFlux}(\sigma_1, 3/2)$; adding `rightEdgeFlux` and applying `rightEdgeFlux_add_horizCapFlux_eq_vertFlux` gives (1).
(2) Combine (1) with Theorem 1.1(1)–(2).
(3) For $t > 0$, $e^{-2(\sigma_1 - 1/2) t} \|\mathrm{rightHalfPort}(t)\|^2 \le e^{-2(\sigma_1 - 1/2) t} \frac{C^2 e^{2(\sigma_1 - 1/2) t}}{(t + 1)^2} = C^2 (t + 1)^{-2}$, which is integrable on $(0, \infty)$ by `integrableOn_add_rpow_Ioi_of_lt` (continuity of `rightHalfPort` follows from `continuous_vertFlux_of_ne_zero` and `continuous_horizCapFlux_of_ne_zero`).
(4) At $\sigma_1 = 1/2$, $\mathrm{horizCapFlux}(1/2, 1/2) = 0$, so Theorem 1.1(1) gives $\le C_V / (|t| + 1)$ for all $t \in \mathbb{R}$, and (3) at $2(1/2 - 1/2) = 0$ gives `IntegrableOn` on $(0, \infty)$. $\square$

---

### §2. 6-Way Zero-Free Rigidity & 5-Way Critical-Line Uniform-Boundedness Equivalence (`[PROVED HERE]`)

**Theorem 2.1 (6-Way Zero-Free Window Rigidity `TFAE`).**
On any boundary-regular centered window $[-1/2, 3/2] \times [y_1, y_2]$ ($y_1 \le y_2$), the following are equivalent:
1. $\forall z \in [1/2, 3/2] \times [y_1, y_2],\; A_N(z) \ne 0$ (the exact hypothesis of `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree`);
2. $(\forall t \in \mathbb{R},\; \mathrm{rightHalfPort}(t) = \mathrm{vertFlux}(1/2, t)) \wedge (\exists C > 0,\; \forall t \in \mathbb{R},\; \|\mathrm{rightHalfPort}(t)\| \le C / (|t| + 1))$;
3. $\mathrm{IntegrableOn}\,(t \mapsto \|\mathrm{rightHalfPort}(y_1, y_2, N, t)\|^2)\,(0, \infty)$;
4. $\forall z \in (-1/2, 3/2) \times (y_1, y_2),\; A_N(z) \ne 0$;
5. $\forall t \in \mathbb{R},\; \mathrm{centeredThetaExpSum}(y_1, y_2, N, t) = 0$;
6. $\forall t \in \mathbb{R},\; \mathrm{rightHalfPort}(y_1, y_2, N, t) = -\overline{\mathrm{rightHalfPort}(y_1, y_2, N, -t)}$.

*Proof.*
- $1 \Rightarrow 2 \Rightarrow 3$: Theorem 1.2(4).
- $3 \Rightarrow 4$: By `integrableOn_windowEnergy_iff_rightHalfPort` at $x = 0$, $\int_0^\infty \|\mathcal{Z}_N(t)\|^2\,dt < \infty$. Let $W = \mathrm{centeredThetaWindow}$. If $z \in (-1/2, 3/2) \times (y_1, y_2)$ satisfies $A_N(z) = 0$, then $z \in W.Z$. Setting $z_1 := z$ if $\operatorname{Re} z \ge 1/2$ and $1 - \bar z \in W.Z$ otherwise gives $z_1 \in W.Z$ with $\operatorname{Re} z_1 - 1/2 \ge 0$. Choosing $z_0 \in W.Z$ maximizing $w \mapsto \operatorname{Re} w - 1/2 =: \delta \ge 0$ and applying `W.lt_of_integrableOn_energy` at $x = 0$ yields $2\delta < 0$, contradicting $\delta \ge 0$.
- $4 \Rightarrow 5$: $W.Z = \emptyset$, so $\mathcal{Z}_N(t) = W.\mathrm{expSum}(t) = 0$.
- $5 \Rightarrow 6$: `centeredThetaExpSum_eq_rightHalfPort_add_conj_neg` gives $0 = \mathcal{P}_+(t) + \overline{\mathcal{P}_+(-t)}$.
- $6 \Rightarrow 3$: By `leftHalfPort_eq_conj_rightHalfPort_neg`, $\mathcal{P}_+(t) = -\mathcal{P}_-(t)$, so $\|\mathcal{P}_+(t)\|^2 = \|\mathcal{P}_-(t)\|^2 \in L^1(0, \infty)$ by `integrableOn_leftHalfPort_sq`.
- $4 \Rightarrow 1$: Any $z \in [1/2, 3/2] \times [y_1, y_2]$ either lies on $\{3/2\} \times [y_1, y_2] \cup [1/2, 3/2] \times \{y_1, y_2\}$ (where $A_N(z) \ne 0$ by `edge_ne_zero_of_bdry_regular`) or in $(-1/2, 3/2) \times (y_1, y_2)$ (where $A_N(z) \ne 0$ by (4)). $\square$

**Theorem 2.2 (5-Way Critical-Line Uniform-Boundedness & Mode-Decomposition `TFAE`).**
On any boundary-regular centered window $[-1/2, 3/2] \times [y_1, y_2]$ ($y_1 \le y_2$) with $W := \mathrm{centeredThetaWindow}$, the following are equivalent:
1. $\exists M > 0,\; \forall t \ge 0,\; \|\mathrm{rightHalfPort}(y_1, y_2, N, t)\| \le M$;
2. $\exists M > 0,\; \forall t \ge 0,\; \|\mathrm{centeredThetaExpSum}(y_1, y_2, N, t)\| \le M$;
3. $\forall \varepsilon > 0,\; \exists C > 0,\; \forall t \ge 0,\; \|\mathrm{rightHalfPort}(y_1, y_2, N, t)\|^2 \le C e^{\varepsilon t}$;
4. $\forall z \in (-1/2, 3/2) \times (y_1, y_2),\; A_N(z) = 0 \implies \operatorname{Re} z = 1/2$;
5. $(\forall z \in W.Z,\; \operatorname{Re} z = 1/2) \wedge \exists C_L > 0,\; \forall t \ge 0,\; \left\|\mathrm{rightHalfPort}(y_1, y_2, N, t) - \sum_{z \in W.Z} W.\mathrm{mult}(z) e^{i (\operatorname{Im} z) t}\right\| \le \frac{C_L}{t + 1}$.

*Proof.*
- $1 \Rightarrow 3$: Take $C = M^2 \le M^2 e^{\varepsilon t}$ for $t \ge 0$.
- $3 \Leftrightarrow 4$: Directly from `subexp_windowEnergy_tfae` (items 3 and 4).
- $4 \Rightarrow 5$: Every $z \in W.Z$ satisfies $\operatorname{Re} z = 1/2$, so $z - 1/2 = i \operatorname{Im} z$ and $(t : \mathbb{C}) (z - 1/2) = i (\operatorname{Im} z) t$. Hence $W.\mathrm{expSum}(t) = \sum_{z \in W.Z} W.\mathrm{mult}(z) e^{i (\operatorname{Im} z) t}$. By `centeredThetaWindow_expSum` and `centeredThetaExpSum_eq_rightHalfPort_add_leftHalfPort`, $\mathrm{rightHalfPort}(t) - \sum_{z \in W.Z} W.\mathrm{mult}(z) e^{i (\operatorname{Im} z) t} = -\mathrm{leftHalfPort}(t)$, which is bounded by $C_L / (t + 1)$ for $t \ge 0$ by `exists_leftEdge_and_leftHalfPort_decay`.
- $5 \Rightarrow 1$: Triangle inequality gives $\|\mathrm{rightHalfPort}(t)\| \le W.\mathrm{degree} + C_L + 1$ for $t \ge 0$.
- $2 \Rightarrow 3$: $\mathrm{rightHalfPort}(t) = \mathcal{Z}_N(t) - \mathrm{leftHalfPort}(t)$ is bounded on $[0, \infty)$ by $M + C_L$, hence $O_\varepsilon(e^{\varepsilon t})$ in square norm.
- $4 \Rightarrow 2$: By `W.norm_expSum_le` with $\delta = 0$, $\|\mathcal{Z}_N(t)\| \le W.\mathrm{degree} + 1$ for $t \ge 0$. $\square$

---

### §3. Unconditional Right-Half-Port Control Laws for $\zeta$ (`[PROVED HERE]`)

**Theorem 3.1 (Unconditional Sub-$e^{t/2}/(t+1)$ Right-Half-Port Control on Every Burnol Unit Window).**
For every $m \in \mathbb{N}$ and every $N \ge \mathrm{capCancelSqrtPrefix}\,m$, $\sigma_m := \mathrm{burnolCapAbscissa}\,m = 1 - \frac{1}{116\log(m + 5)} \in (\frac{3}{4}, 1)$ satisfies $\sigma_m - \frac{1}{2} < \frac{1}{2}$, there exists $C > 0$ such that for all $t \ge 0$,
$$\|\mathrm{rightHalfPort}(\mathrm{burnolUnitLower}\,m, \mathrm{burnolUnitUpper}\,m, N, t)\| \le C \frac{e^{(\sigma_m - 1/2) t}}{t + 1},$$
and $\mathrm{IntegrableOn}\,(t \mapsto e^{-2(\sigma_m - 1/2) t} \|\mathrm{rightHalfPort}(\mathrm{burnolUnitLower}\,m, \mathrm{burnolUnitUpper}\,m, N, t)\|^2)\,(0, \infty)$.

*Proof.* Combine `exists_burnol_subHalfExp_cap_cancellation` (giving $A_N \ne 0$ on $[\sigma_m, 3/2] \times [\mathrm{burnolUnitLower}\,m, \mathrm{burnolUnitUpper}\,m]$), `burnolUnit_bdry_regular` (giving $A_N \ne 0$ on $[1/2, 3/2] \times \{y_1(m), y_2(m)\}$ via `edge_ne_zero_of_bdry_regular`), and Theorem 1.2(2)–(3). $\square$

**Theorem 3.2 (Unconditional Double-Logarithmic Right-Half-Port Decay on Almost All Burnol Unit Windows).**
There exists $C_0 > 0$ such that eventually in $V$: for all except at most $C_0 V / \log\log V$ Burnol unit windows $m \in [\lceil V \rceil, \lfloor 2V \rfloor]$, for every $N \ge \max(\mathrm{capCancelSqrtPrefix}\,m, \mathrm{doorSqrtPrefix}\,m)$, there exists $C_{m,N} > 0$ such that for all $t \ge 0$,
$$\|\mathrm{rightHalfPort}(\mathrm{burnolUnitLower}\,m, \mathrm{burnolUnitUpper}\,m, N, t)\| \le C_{m,N} \frac{\exp\!\left(\frac{3\log\log V}{\log V} t\right)}{t + 1}.$$

*Proof.* By `deepExtendedShell_orderSum_le` at $r = 3/4$ and $A_V = 2\log\log V$ (as in `almostAll_doubleLogStage_besselSzegoCertificate`), at most $3 C_d V / \log\log V$ windows $m \in [\lceil V \rceil, \lfloor 2V \rfloor]$ contain a $\xi$-zero in `burnolUnitXiZeros m` with $|\operatorname{Re}\rho - 1/2| \ge \frac{2\log\log V}{\log V}$. On every remaining window $m$, applying `exists_logStage_tail_lt` at $c = 1$ (`N ≥ doorSqrtPrefix m`) gives zero transfer within radius $r_m = \frac{1}{16 \, \mathrm{logDoorStage}\,1\,m} \le \frac{1}{16\log V} \le \frac{\log\log V}{\log V}$, so every interior zero of $A_N$ has $\operatorname{Re} z < \frac{1}{2} + \frac{2\log\log V}{\log V} + \frac{1}{16\log V} < \frac{1}{2} + \frac{3\log\log V}{\log V} =: \sigma_V \in (1/2, 3/2)$ (for $\frac{3\log\log V}{\log V} < 1$). Together with boundary regularity (`N ≥ capCancelSqrtPrefix m`), $A_N \ne 0$ on $[\sigma_V, 3/2] \times [y_1(m), y_2(m)]$, and Theorem 1.2(2) yields the bound. $\square$

**Theorem 3.3 (Unconditional Direct Critical-Line Flux Control on $(1 - O(B))V$ Micro-Planck Windows).**
There exists $C_0 > 0$ such that for every $B > 0$, eventually in $V$: outside a set of $t_0 \in [V, 2V]$ of Lebesgue measure at most $C_0 B V$, the Planck window $[-1/2, 3/2] \times [t_0, t_0 + B / \log V]$ at $N = \mathrm{doorSqrtPrefix}\,\lfloor t_0 \rfloor$ is boundary-regular and satisfies $A_N(z) \ne 0$ on $[1/2, 3/2] \times [t_0, t_0 + B / \log V]$, hence
$$\forall t \in \mathbb{R},\quad \mathrm{rightHalfPort}(t_0, t_0 + B / \log V, N, t) = \mathrm{vertFlux}(1/2, t_0, t_0 + B / \log V, N, t)$$
and $\exists C > 0,\; \forall t \in \mathbb{R},\; \|\mathrm{rightHalfPort}(t_0, t_0 + B / \log V, N, t)\| \le \frac{C}{|t| + 1}$.

*Proof.* Let $C_{\mathrm{tot}} > 0$ be the constant of `stripFinsetPos_orderSum_le_mul_log`; take $C_0 := 8 C_{\mathrm{tot}}$. Fix $B > 0$. If $8 C_{\mathrm{tot}} B \ge 1$, $\operatorname{vol}([V, 2V]) = V \le C_0 B V$. Otherwise $B < \frac{1}{8 C_{\mathrm{tot}}}$. Set $c := 1 / B > 0$ and obtain $m_1$ from `exists_logStage_tail_lt`$(c)$. For large $V$ ($V \ge \max(32, m_1 + 2)$, $\log V \ge \max(16, B)$), every $t_0 \in [V, 2V]$ has $m = \lfloor t_0 \rfloor \ge m_1$, $B / \log V \le 1$, $[t_0, t_0 + B/\log V] \subset (\mathrm{burnolUnitLower}\,m, \mathrm{burnolUnitUpper}\,m)$, and transfer radius $r_m = \frac{1}{16\,\mathrm{logDoorStage}\,c\,m} \le \frac{1}{16 c \log V} = \frac{B}{16\log V}$. If $A_N$ vanishes anywhere on $[-1/2, 3/2] \times [t_0, t_0 + B/\log V]$, `burnolUnit_bdry_regular` excludes $\operatorname{Re} z \in \{-1/2, 3/2\}$, so $z \in (-1/2, 3/2) \times (\mathrm{burnolUnitLower}\,m, \mathrm{burnolUnitUpper}\,m)$ and `exists_xiZero_near_thetaZero` produces $w \in \mathrm{burnolUnitXiZeros}\,m \subseteq S_V := \mathrm{stripFinsetPos}(2V + 4)$ with $|w.\mathrm{im} - z.\mathrm{im}| \le \frac{B}{16\log V}$, whence $t_0 \in [w.\mathrm{im} - \frac{17 B}{16\log V}, w.\mathrm{im} + \frac{B}{16\log V}]$ (length $\frac{9 B}{8\log V}$). Since $\#S_V \le C_{\mathrm{tot}}(2V + 4)\log(2V + 4) \le 6 C_{\mathrm{tot}} V \log V$ eventually, the bad set has measure $\le 6 C_{\mathrm{tot}} V \log V \cdot \frac{9 B}{8\log V} < 8 C_{\mathrm{tot}} B V = C_0 B V$. Outside this set, $[-1/2, 3/2] \times [t_0, t_0 + B/\log V]$ has zero zeros of $A_N$ up to the boundary, so `hbdry` and Theorem 1.2(4) hold directly on $\sigma_1 = 1/2$. $\square$

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** `rightHalfPort_criticalLineFlux_zeroFree_tfae` proves that `∀ z ∈ [1/2, 3/2] × [y₁, y₂], A_N z ≠ 0` (the hypothesis of `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree`) AND unweighted $L^2(0, \infty)$ integrability of `rightHalfPort` are both unconditionally equivalent to complete absence of zeros of $A_N$ in $(-1/2, 3/2) \times (y_1, y_2)$, so any critical-line zero forces $\int_0^\infty \|\mathcal{P}_+(t)\|^2\,dt = +\infty$.
- **Strongest positive survivor:**
  1. Integration-by-parts $O(1/(|t|+1))$ upgrade on zero-free windows + micro-Planck direct applicability on $(1 - O(B))V$ of $[V, 2V]$ for $\zeta$.
  2. Shifted-abscissa decomposition `rightHalfPort = vertFlux σ₁ + horizCapFlux (1/2) σ₁` giving $O(e^{(\sigma_1 - 1/2) t}/(t + 1))$ decay and boundary Laplace integrability from $[1/2, 3/2]$ alone (yielding $O(e^{(\sigma_m - 1/2)t}/(t+1))$ on **every** Burnol unit window and $O(e^{(3\log\log V/\log V)t}/(t+1))$ on $1 - O(1/\log\log V)$ Burnol unit windows).
  3. 5-way equivalence `∃ M, ∀ t ≥ 0, ‖rightHalfPort(t)‖ ≤ M ↔ local critical-line purity` with explicit $O(1/(t+1))$-accurate critical-line mode decomposition.
- **New insight:** Distinguishes $L^2(0, \infty)$ decay of `rightHalfPort` (which forbids critical-line zeros) from $L^\infty(0, \infty)$ boundedness of `rightHalfPort` (which is exact local `RH`) and shifted boundary-Laplace integrability $e^{-2(\sigma_1 - 1/2)t}\|\mathcal{P}_+(t)\|^2 \in L^1(0, \infty)$ (which holds purely from right-half zero-freeness on $[\sigma_1, 3/2]$).
- **Status:** Dependency-closed on paper; ready for immediate Lean 4 formalization in `RightHalfPortCriticalLineControl.lean`.

## Log
- 2026-11-03 — created with complete dependency-closed paper proofs in 2-fully-proven
