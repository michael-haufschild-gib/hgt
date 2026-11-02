# Window energy, port flux decomposition, Cauchy cap cancellation, and polynomial-stage $\Theta(\sqrt m)$ laws

- **ID:** wd-window-energy-port-flux-and-polynomial-stage
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0211/obstacles-summary.md` §2.6.3 (Obstacles B15, A10)
- **Statement:** The $e^t$ right-edge flux never cancels against its functional-equation image: on every Burnol window at $N\ge\Theta(\sqrt m)$ both $\mathcal F_{\mathrm{right}}+\mathcal F_{\mathrm{left}}$ and $\mathcal F_{\mathrm{right}}+\mathcal P_-$ are $\Omega(e^t/t)$. The flux is cancelled by the right horizontal caps (Cauchy), and subexponential growth of $|\mathcal Z_N|^2$ on all polynomial-stage windows at $\Theta_k(\sqrt m)$ prefix is unconditionally equivalent to RH; at fixed degree $k$ it is equivalent to $|\operatorname{Re}\rho-\frac12|\le C/|\operatorname{Im}\rho|^k$.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: modules below, `lake --old env lean` exit 0, axioms `propext`, `Classical.choice`, `Quot.sound` only

## Lean modules
- `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/WindowPortFlux/PortFluxDecompositionAndBlowup.lean`
- `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/WindowPortFlux/CauchyCapCancellationAndPolynomialStage.lean`

## Notation
$L_N=A_N'/A_N$ (`thetaLogDeriv`). `vertFlux σ` $=\frac1{2\pi}\int_{y_1}^{y_2}e^{t(\sigma-\frac12+iy)}L_N(\sigma+iy)\,dy$; $\mathcal F_{\mathrm{right}}$ = `rightEdgeFlux` ($\sigma=\frac32$); $\mathcal F_{\mathrm{left}}$ = `leftEdgeFlux` ($-$`vertFlux` at $-\frac12$); `horizCapFlux a b`; $\mathcal P_+$ = `rightHalfPort` $=\mathcal F_{\mathrm{right}}+$`horizCapFlux` $\frac12\,\frac32$; $\mathcal P_-$ = `leftHalfPort` $=\mathcal F_{\mathrm{left}}+$`horizCapFlux` $-\frac12\,\frac12$; $\mathcal Z_N$ = `centeredThetaExpSum`.

## Theorems

**P1 (functional-equation port decomposition).**
- `thetaLogDeriv_one_sub_conj`: $L_N(1-\bar z)=-\overline{L_N(z)}$ (from $A_N(1-z)=A_N(z)$ and $\overline{A_N(\bar z)}=A_N(z)$).
- `centeredThetaExpSum_eq_edges`: $\mathcal Z_N=\mathcal F_{\mathrm{right}}+\mathcal F_{\mathrm{left}}+$`horizCapFlux` $-\frac12\,\frac32$.
- `leftEdgeFlux_eq_conj_rightEdgeFlux_neg`: $\mathcal F_{\mathrm{left}}(t)=\overline{\mathcal F_{\mathrm{right}}(-t)}$; `leftHalfPort_eq_conj_rightHalfPort_neg`: $\mathcal P_-(t)=\overline{\mathcal P_+(-t)}$.
- `centeredThetaExpSum_eq_rightHalfPort_add_conj_neg`: $\mathcal Z_N(t)=\mathcal P_+(t)+\overline{\mathcal P_+(-t)}$ when $A_N\ne0$ on the boundary.

**P2 (left port is $L^2$).** `exists_leftEdge_and_leftHalfPort_decay`: $\|\mathcal F_{\mathrm{left}}(t)\|\le Ce^{-t}$, $\|\mathcal P_-(t)\|\le C/(t+1)$ for $t\ge0$ (integration by parts in $x$; $|e^{t(x-\frac12)}|\le1$ on $[-\frac12,\frac12]$). `integrableOn_leftHalfPort_sq`: $\mathcal P_-\in L^2(0,\infty)$. `integrableOn_windowEnergy_iff_rightHalfPort`: for every $x\ge0$, $e^{-xt}|\mathcal Z_N|^2\in L^1(0,\infty)\Leftrightarrow e^{-xt}|\mathcal P_+|^2\in L^1(0,\infty)$.

**P3 (no functional-equation cancellation).** `re_logDeriv_xi_three_halves_ge`: $\operatorname{Re}(\xi'/\xi)(\frac32+iy)\ge\frac1{9+4(y-\operatorname{Im}\rho_0)^2}$ (one term of the nonnegative partial-fraction sum). `re_thetaLogDeriv_burnol_pos`: $\operatorname{Re}L_N(\frac32+iy_j(m))>0$ for $N\ge$ `fluxSqrtPrefix m` $=\Theta(\sqrt m)$. `exists_burnol_rightAddLeftFlux_exp_blowup`: for every $m$ and $N\ge$ `fluxSqrtPrefix m` there are $c,T_0>0$ such that every period $[T,T+2\pi/(y_2-y_1)]$, $T\ge T_0$, contains $t$ with
$$\|\mathcal F_{\mathrm{right}}(t)+\mathcal F_{\mathrm{left}}(t)\|\ge\tfrac{ce^t}{t},\qquad\|\mathcal F_{\mathrm{right}}(t)+\mathcal P_-(t)\|\ge\tfrac{ce^t}{t}.$$
*Proof.* Periodic mean-square identity for the endpoint oscillation (`periodic_endpoint_mean_sq`) and twice integration by parts (`exists_oscillatory_integral_ge_div_t`) give $\|\mathcal F_{\mathrm{right}}(t)\|\ge\mu e^t/t$; P2 bounds the partners. $\square$

**P4 (Cauchy cap cancellation).** `rightEdgeFlux_add_horizCapFlux_eq_vertFlux`: if $A_N\ne0$ on $[\sigma_1,\frac32]\times[y_1,y_2]$ then $\mathcal F_{\mathrm{right}}+$`horizCapFlux` $\sigma_1\,\frac32=$`vertFlux` $\sigma_1$, hence $O(e^{(\sigma_1-\frac12)t})$ (`exists_norm_rightEdgeFlux_add_horizCapFlux_le`). `exists_burnol_subHalfExp_cap_cancellation`: on every Burnol window at $N\ge$ `capCancelSqrtPrefix m`, cancellation holds at `burnolCapAbscissa m` $<1$, i.e. strictly below $e^{t/2}$. `rightHalfPort_eq_criticalLineFlux_of_rightHalfZeroFree`: with no zeros right of the line, $\mathcal P_+$ equals the critical-line flux.

**P5 (single window).** `subexp_windowEnergy_tfae`: with $A_N\ne0$ on the boundary, equivalent: $\forall\varepsilon>0$ $|\mathcal Z_N(t)|^2\le Ce^{\varepsilon t}$; $\forall x>0$ $e^{-xt}|\mathcal Z_N|^2\in L^1$; $\forall x>0$ $e^{-xt}|\mathcal P_+|^2\in L^1$; every enclosed zero of $A_N$ has $\operatorname{Re}z=\frac12$. `centeredThetaExpSum_eq_zero_above_quadratic_horizon`: at fixed $N$, $\mathcal Z_N\equiv0$ on windows above $C_{\mathrm{hor}}(N+2)^2$.

**P6 (polynomial stage ⇔ RH).** `besselUnitPrefix_le_polySqrtPrefix_of_le`: for $S\le(m+6)^k$, `besselUnitPrefix m S` $\le$ `polySqrtPrefix k m` $=\Theta_k(\sqrt m)$. `riemannHypothesis_polynomialStage_tfae`: with $n_{k,m}=$ `doorUnitStage m ((m+6)^k)`, equivalent: RH; $\forall k,m,\ N\ge$ `polySqrtPrefix k m`: $|\mathcal Z_N(t)|^2\le Ce^{t/(4n_{k,m})}$; $e^{-t/(2n_{k,m})}|\mathcal Z_N|^2\in L^1(0,\infty)$; $e^{-t/(2n_{k,m})}|\mathcal P_+|^2\in L^1(0,\infty)$; explicit Bessel–Szegő certificate positivity; circle nonvanishing and Fredholm index $0$.

**P7 (fixed degree).** `invPoly_corridor_iff_fixedDegree_polynomialStage` ($k\ge1$): $\exists T_1,C$, $|\operatorname{Re}\rho-\frac12|\le C/|\operatorname{Im}\rho|^k$ for $|\operatorname{Im}\rho|\ge T_1$ $\Leftrightarrow$ the energy, half-port, certificate and index statements at stage `fixedPolyDoorStage k c m` ($0<c\le1$, $m\ge m_0$, $N\ge$ `polySqrtPrefix k m`).

## No-go closure
- **Killing mechanism:** $\mathcal F_{\mathrm{left}}=O(e^{-t})$ and $\mathcal P_-\in L^2(0,\infty)$, while $\operatorname{Re}(\xi'/\xi)>0$ on $\operatorname{Re}s=\frac32$ forces $\mathcal F_{\mathrm{right}}=\Omega(e^t/t)$ on every window (P3). The functional-equation image cannot cancel the right-edge flux.
- **Strongest positive survivors:** P1–P2 (the left half-plane is invisible to window energy at every Laplace rate $x\ge0$), P4 (the true cancelling partner is the right horizontal cap pair), P5 (single-window classification), P6–P7 (polynomial-stage subexponential growth at $\Theta_k(\sqrt m)$ is exactly RH; fixed degree is exactly the inverse-polynomial corridor).
- **New insight:** subexponential growth of $|\mathcal Z_N|^2$ is not a source identity on the right edge but zero location of $A_N$ inside the right half-window; the source must control $\mathcal P_+$ alone.

## Log
- 2026-11-02 — formalized; promoted from 2-fully-proven.
