# Intrinsic Control of the Right Half-Port via Shifted and Critical-Line Flux Identities

- **ID:** wd-right-half-port-critical-line-flux-control
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0211/obstacles-summary.md · WindowPortFlux
- **Statement:** Integration-by-parts $O(1/(|t|+1))$ upgrade and 6-way zero-free window rigidity equivalence for `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree`, shifted-abscissa intrinsic decomposition `rightHalfPort = vertFlux σ₁ + horizCapFlux (1/2) σ₁` giving $O(e^{(\sigma_1 - 1/2)t}/(t+1))$ decay and boundary Laplace integrability from $[1/2, 3/2]$ alone, 5-way uniform boundedness equivalence `‖𝒫_+(t)‖ ≤ M ↔ local RH`, and unconditional Burnol, double-log typical, and micro-Planck right-port decay laws for $\zeta$.

## Goal
Analyze and maximally extend `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree` to control `rightHalfPort` ($\mathcal{P}_+(t)$) alone:
1. Upgrade `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree` from $O(1)$ to $O(1/(|t|+1)) \in L^2(0, \infty)$ and determine the exact necessary-and-sufficient scope of $\sigma_1 = 1/2$ control on boundary-regular centered windows.
2. Control `rightHalfPort` alone when critical-line or corridor zeros of $A_N$ are present (where $\sigma_1 = 1/2$ is obstructed), both intrinsically on $[1/2, 3/2] \times [y_1, y_2]$ via shifted vertical-line + short-cap integration by parts and via desingularized critical-line oscillatory modes.
3. Establish unconditional quantitative bounds on `rightHalfPort` for $\zeta$'s theta prefixes across all Burnol unit windows, almost all unit windows (double-log rate), and $(1 - O(B))V$ micro-Planck windows (where $\sigma_1 = 1/2$ applies verbatim).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux.RightHalfPortCriticalLineControl`, `lake --old env lean` green, `#print axioms` PASS (`[propext, Classical.choice, Quot.sound]`)

## Lean Declarations
Module: `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/WindowPortFlux/RightHalfPortCriticalLineControl.lean`
- `exists_vertFlux_inv_decay`, `exists_shortCap_inv_decay`
- `rightHalfPort_eq_vertFlux_add_shortCap`, `exists_rightHalfPort_shifted_inv_decay`, `exists_criticalLineFlux_inv_decay_of_rightHalfZeroFree`
- `rightHalfPort_criticalLineFlux_zeroFree_tfae`, `rightHalfPort_uniformBounded_tfae`
- `exists_burnol_rightHalfPort_subHalfExp_inv_decay`, `almostAll_unitWindow_rightHalfPort_doubleLog_decay`, `microPlanckWindow_criticalLineFlux_volume_le`

## Approach & Complete Paper Proofs

### §1. Oscillatory Integration by Parts & Shifted-Abscissa Intrinsic Right-Port Control (`[PROVED HERE]`)

**Theorem 1.1 (`exists_vertFlux_inv_decay`, `exists_shortCap_inv_decay`).**
1. Let $y_1 \le y_2$, $\sigma \in \mathbb{R}$, $N \in \mathbb{N}$, and assume $A_N(\sigma + i y) \ne 0$ for all $y \in [y_1, y_2]$. Then there exists $C_V > 0$ such that for all $t \in \mathbb{R}$,
   $$\|\mathrm{vertFlux}(\sigma, y_1, y_2, N, t)\| \le \frac{C_V e^{(\sigma - 1/2) t}}{|t| + 1}.$$
2. Let $\frac{1}{2} \le \sigma_1$, $y_1, y_2 \in \mathbb{R}$, $N \in \mathbb{N}$, and assume $A_N(x + i y_j) \ne 0$ for all $x \in [1/2, \sigma_1]$ and $j \in \{1, 2\}$. Then there exists $C_H > 0$ such that for all $t \ge 0$,
   $$\|\mathrm{horizCapFlux}(1/2, \sigma_1, y_1, y_2, N, t)\| \le \frac{C_H e^{(\sigma_1 - 1/2) t}}{t + 1}.$$

*Proof.*
(1) Factor $\mathrm{vertFlux}(\sigma, y_1, y_2, N, t) = \frac{1}{2\pi} e^{(\sigma - 1/2) t} \int_{y_1}^{y_2} e^{i t y} g(y)\,dy$ with $g(y) := L_N(\sigma + i y)$ and $g'(y) = i L_N'(\sigma + i y)$ continuous on $[y_1, y_2]$ by `analyticAt_thetaLogDeriv`. Bound directly for $|t| \le 1$, and integrate by parts via $\frac{d}{dy}\big((i t)^{-1} e^{i t y} g(y)\big) = e^{i t y} g(y) + (i t)^{-1} e^{i t y} g'(y)$ for $|t| > 1$.

(2) Bound directly for $0 \le t \le 1$, and integrate by parts via $\frac{d}{dx}\big(t^{-1} e^{t(x - 1/2 + i y)} h_y(x)\big) = e^{t(x - 1/2 + i y)} h_y(x) + t^{-1} e^{t(x - 1/2 + i y)} h'_y(x)$ on $[1/2, \sigma_1]$ for $t > 1$. $\square$

**Theorem 1.2 (`rightHalfPort_eq_vertFlux_add_shortCap`, `exists_rightHalfPort_shifted_inv_decay`, `exists_criticalLineFlux_inv_decay_of_rightHalfZeroFree`).**
Let $\frac{1}{2} \le \sigma_1 \le \frac{3}{2}$, $y_1 \le y_2$, $N \in \mathbb{N}$, and assume $A_N(z) \ne 0$ for all $z \in [\sigma_1, 3/2] \times [y_1, y_2]$ and $A_N(x + i y_j) \ne 0$ for all $x \in [1/2, 3/2]$, $j \in \{1, 2\}$. Then:
1. For all $t \in \mathbb{R}$, $\mathrm{rightHalfPort}(y_1, y_2, N, t) = \mathrm{vertFlux}(\sigma_1, y_1, y_2, N, t) + \mathrm{horizCapFlux}(1/2, \sigma_1, y_1, y_2, N, t)$.
2. There exists $C > 0$ such that $\|\mathrm{rightHalfPort}(y_1, y_2, N, t)\| \le C \frac{e^{(\sigma_1 - 1/2) t}}{t + 1}$ for all $t \ge 0$, and $\int_0^\infty e^{-2(\sigma_1 - 1/2) t} \|\mathrm{rightHalfPort}(y_1, y_2, N, t)\|^2\,dt < \infty$.
3. When $A_N \ne 0$ on $[1/2, 3/2] \times [y_1, y_2]$, $\mathrm{rightHalfPort} = \mathrm{vertFlux}(1/2)$, $\|\mathrm{rightHalfPort}(y_1, y_2, N, t)\| \le \frac{C}{|t| + 1}$ for all $t \in \mathbb{R}$, and $\mathrm{rightHalfPort} \in L^2(0, \infty)$.

---

### §2. 6-Way Zero-Free Rigidity & 5-Way Critical-Line Uniform-Boundedness Equivalence (`[PROVED HERE]`)

**Theorem 2.1 (`rightHalfPort_criticalLineFlux_zeroFree_tfae`).**
On any boundary-regular centered window $[-1/2, 3/2] \times [y_1, y_2]$ ($y_1 \le y_2$), the following are equivalent:
1. $\forall z \in [1/2, 3/2] \times [y_1, y_2],\; A_N(z) \ne 0$;
2. $(\forall t \in \mathbb{R},\; \mathrm{rightHalfPort}(t) = \mathrm{vertFlux}(1/2, t)) \wedge (\exists C > 0,\; \forall t \in \mathbb{R},\; \|\mathrm{rightHalfPort}(t)\| \le C / (|t| + 1))$;
3. $\mathrm{IntegrableOn}\,(t \mapsto \|\mathrm{rightHalfPort}(y_1, y_2, N, t)\|^2)\,(0, \infty)$;
4. $\forall z \in (-1/2, 3/2) \times (y_1, y_2),\; A_N(z) \ne 0$;
5. $\forall t \in \mathbb{R},\; \mathrm{centeredThetaExpSum}(y_1, y_2, N, t) = 0$;
6. $\forall t \in \mathbb{R},\; \mathrm{rightHalfPort}(y_1, y_2, N, t) = -\overline{\mathrm{rightHalfPort}(y_1, y_2, N, -t)}$.

**Theorem 2.2 (`rightHalfPort_uniformBounded_tfae`).**
On any boundary-regular centered window $[-1/2, 3/2] \times [y_1, y_2]$ ($y_1 \le y_2$) with $W := \mathrm{centeredThetaWindow}$, the following are equivalent:
1. $\exists M > 0,\; \forall t \ge 0,\; \|\mathrm{rightHalfPort}(y_1, y_2, N, t)\| \le M$;
2. $\exists M > 0,\; \forall t \ge 0,\; \|\mathrm{centeredThetaExpSum}(y_1, y_2, N, t)\| \le M$;
3. $\forall \varepsilon > 0,\; \exists C > 0,\; \forall t \ge 0,\; \|\mathrm{rightHalfPort}(y_1, y_2, N, t)\|^2 \le C e^{\varepsilon t}$;
4. $\forall z \in (-1/2, 3/2) \times (y_1, y_2),\; A_N(z) = 0 \implies \operatorname{Re} z = 1/2$;
5. $(\forall z \in W.Z,\; \operatorname{Re} z = 1/2) \wedge \exists C_L > 0,\; \forall t \ge 0,\; \left\|\mathrm{rightHalfPort}(y_1, y_2, N, t) - \sum_{z \in W.Z} W.\mathrm{mult}(z) e^{i (\operatorname{Im} z) t}\right\| \le \frac{C_L}{t + 1}$.

---

### §3. Unconditional Right-Half-Port Control Laws for $\zeta$ (`[PROVED HERE]`)

**Theorem 3.1 (`exists_burnol_rightHalfPort_subHalfExp_inv_decay`).**
For every $m \in \mathbb{N}$ and every $N \ge \mathrm{capCancelSqrtPrefix}\,m$, $\sigma_m := \mathrm{burnolCapAbscissa}\,m \in (\frac{3}{4}, 1)$ satisfies $\sigma_m - \frac{1}{2} < \frac{1}{2}$, $\|\mathrm{rightHalfPort}(\mathrm{burnolUnitLower}\,m, \mathrm{burnolUnitUpper}\,m, N, t)\| \le C \frac{e^{(\sigma_m - 1/2) t}}{t + 1}$ for $t \ge 0$, and $e^{-2(\sigma_m - 1/2) t} \|\mathrm{rightHalfPort}(t)\|^2 \in L^1(0, \infty)$.

**Theorem 3.2 (`almostAll_unitWindow_rightHalfPort_doubleLog_decay`).**
There exists $C_0 > 0$ such that eventually in $V$: for all except at most $C_0 V / \log\log V$ Burnol unit windows $m \in [\lceil V \rceil, \lfloor 2V \rfloor]$, for every $N \ge \mathrm{doorSqrtPrefix}\,m$, there exists $C_{m,N} > 0$ such that for all $t \ge 0$,
$$\|\mathrm{rightHalfPort}(\mathrm{burnolUnitLower}\,m, \mathrm{burnolUnitUpper}\,m, N, t)\| \le C_{m,N} \frac{\exp\!\left(\frac{3\log\log V}{\log V} t\right)}{t + 1}.$$
*(Note: `burnolPrefix_le_doorSqrtPrefix m` already supplies boundary regularity for all $N \ge \mathrm{doorSqrtPrefix}\,m$.)*

**Theorem 3.3 (`microPlanckWindow_criticalLineFlux_volume_le`).**
There exists $C_0 > 0$ such that for every $B > 0$, eventually in $V$: outside a set of $t_0 \in [V, 2V]$ of Lebesgue measure at most $C_0 B V$, at $N = \mathrm{doorSqrtPrefix}\,\lfloor t_0 \rfloor$, $[1/2, 3/2] \times [t_0, t_0 + B / \log V]$ is completely zero-free for $A_N$, so `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree` applies verbatim and gives $O(1 / (|t| + 1))$ decay and $L^2(0, \infty)$ integrability.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** `rightHalfPort_criticalLineFlux_zeroFree_tfae` proves that `∀ z ∈ [1/2, 3/2] × [y₁, y₂], A_N z ≠ 0` (the hypothesis of `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree`) and unweighted $L^2(0, \infty)$ integrability of `rightHalfPort` are both unconditionally equivalent to complete absence of zeros of $A_N$ in $(-1/2, 3/2) \times (y_1, y_2)$, so any critical-line zero forces $\int_0^\infty \|\mathcal{P}_+(t)\|^2\,dt = +\infty$.
- **Strongest positive survivor:**
  1. Integration-by-parts $O(1/(|t|+1))$ upgrade on zero-free windows + micro-Planck direct applicability on $(1 - O(B))V$ of $[V, 2V]$ for $\zeta$.
  2. Shifted-abscissa decomposition `rightHalfPort = vertFlux σ₁ + horizCapFlux (1/2) σ₁` giving $O(e^{(\sigma_1 - 1/2) t}/(t + 1))$ decay and boundary Laplace integrability from $[1/2, 3/2]$ alone (yielding $O(e^{(\sigma_m - 1/2)t}/(t+1))$ on **every** Burnol unit window and $O(e^{(3\log\log V/\log V)t}/(t+1))$ on $1 - O(1/\log\log V)$ Burnol unit windows).
  3. 5-way equivalence `∃ M, ∀ t ≥ 0, ‖rightHalfPort(t)‖ ≤ M ↔ local critical-line purity` with explicit $O(1/(t+1))$-accurate critical-line mode decomposition.
- **New insight:** Distinguishes $L^2(0, \infty)$ decay of `rightHalfPort` (which forbids critical-line zeros) from $L^\infty(0, \infty)$ boundedness of `rightHalfPort` (which is exact local `RH`) and shifted boundary-Laplace integrability $e^{-2(\sigma_1 - 1/2)t}\|\mathcal{P}_+(t)\|^2 \in L^1(0, \infty)$ (which holds purely from right-half zero-freeness on $[\sigma_1, 3/2]$).
- **Status:** Unconditionally formalized in `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/WindowPortFlux/RightHalfPortCriticalLineControl.lean`; `lake --old env lean` green (`0` `sorry`s, standard axioms only).

## Log
- 2026-11-03 — created with complete dependency-closed paper proofs in 2-fully-proven
- 2026-11-03 — unconditionally formalized in `RightHalfPortCriticalLineControl.lean` and promoted to 3-formalized
