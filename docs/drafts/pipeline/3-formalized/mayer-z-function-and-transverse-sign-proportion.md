# Operator-Native Mayer Z-Function, Transverse Core Moment Slope Law, and Sign-Change Proportion

- **ID:** pm-mayer-z-function-and-sign-proportion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0211/obstacles-summary.md` §2.5.2 · Route PM
- **Statement:** From the Mayer transfer operator, its Lewis reflection $s \leftrightarrow 1 - s$, and its zero-frequency Cauchy archimedean factor alone, construct a function $Z_{\mathrm{PM}}(\tau)$ real on the critical scattering line $s_{\mathrm{crit}}(\tau) = \tfrac{1}{4} + i\tfrac{\tau}{2}$ whose sign changes are odd-multiplicity Mayer scattering resonances, prove the exact transverse core-moment slope formula $Z_{\mathrm{PM}}'(\tau_0) = \operatorname{Re}\bigl(i\,\overline{u_\Gamma(\tau_0)}\,\mathcal{M}[\phi_{2s_0}](0)\bigr)$ at critical-line resonances, and establish infinitely many strict sign changes together with a positive proportion $> 67.250071\%$ of pairwise disjoint strict sign changes up to height $T$.

## Goal
Resolve Route PM §2.5.2 unconditionally without mentioning `riemannZeta` or `hardyZ` in the definitions of Mayer scattering resonances or $Z_{\mathrm{PM}}$, and characterize transverse sign changes directly via the zero-endpoint Mellin moment of the scattering-subtracted Mayer core.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerResonanceCharacterization` and `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerZFunction`, `#print axioms` `[propext, Classical.choice, Quot.sound]`

## Approach & Complete Paper Proof `[PROVED HERE]`

### 1. Pure Operator Characterization of Mayer Scattering Resonances
For $s \in \mathbb{C}$ in the open scattering strip $0 < \operatorname{Re} s < \tfrac{1}{2}$ (so $w = 2s$ satisfies $0 < \operatorname{Re} w < 1$), define a **Mayer scattering resonance** purely from the renormalized Mayer source operator `source` and the Mellin-continued lattice response `state`:
$$\mathrm{IsMayerScatteringResonance}(s) \iff 0 < \operatorname{Re} s < \tfrac{1}{2} \;\land\; \mathcal{L}_{2s}^{\mathrm{src}}(\mathrm{state}(2s)) = \mathrm{state}(2s).$$

**Theorem 1.1 (Five-way operator equivalence).** For $0 < \operatorname{Re} s < \tfrac{1}{2}$, the following are equivalent:
1. $\mathrm{IsMayerScatteringResonance}(s)$, i.e. $\mathcal{L}_{2s}^{\mathrm{src}}(\mathrm{state}(2s)) = \mathrm{state}(2s)$;
2. Strict determinant excess over the signed cofactor: $\operatorname{ord}_{v=2s} B_+(v) < \operatorname{ord}_{v=2s} \det(1 - \mathcal{L}_v^{\mathrm{src}})$;
3. Boundary resolvent pole: $\operatorname{ord}_{v=2s}^{\mathrm{mero}} \bigl\langle \delta_0, (1 - \mathcal{L}_v^{\mathrm{src}})^{-1} 1 \bigr\rangle < 0$;
4. Poincaré scattering pole: $\operatorname{ord}_{u=s}^{\mathrm{mero}} \phi_{\mathrm{PM}}(u) < 0$;
5. $\zeta(2s) = 0$.

Moreover, at every Mayer scattering resonance $s$:
- $\operatorname{Im} s \neq 0$ (since $\xi(2\sigma) > 0$ on $(0,1)$ via `RHTower.xi_pos_on_real_anchor`),
- $\mathrm{state}(2s)$ is an observable $+1$ eigenfunction of the holomorphic Mayer remainder ($\mathcal{R}_{2s}(\mathrm{state}(2s)) = \mathrm{state}(2s)$ and $(\mathrm{state}(2s))(0) = 2\zeta(2s-1) \neq 0$), extending via `MayerGlobalPeriods.period` to a nonzero analytic $+1$ Lewis period function $\psi_s(z)$ on $\operatorname{Re} z > 0$ satisfying $\psi_s(z) = z^{-2s}\psi_s(z^{-1})$ and $\psi_s(z) = \psi_s(z+1) + (z+1)^{-2s}\psi_s(z/(z+1))$,
- Resonance status is invariant under complex conjugation $s \mapsto \bar{s}$ and Riemann–Mayer reflection $s \mapsto s^\sharp := \tfrac{1}{2} - \bar{s}$, and the right-half resonance set $\{s \mid \tfrac{1}{4} < \operatorname{Re} s < \tfrac{1}{2} \land \mathrm{IsMayerScatteringResonance}(s)\}$ has extended cardinality equal to the Weil–Hodge polar defect $\mathrm{boostPolarIndex}(\mathrm{ratCorr})$.

*Proof.* Since $0 < \operatorname{Re}(2s) < 1$, $2s \notin \{1,2\}$, so `MayerScatteringState.state_equation` gives
$$\mathrm{state}(2s) - \mathcal{L}_{2s}^{\mathrm{src}}(\mathrm{state}(2s)) = \zeta(2s)\cdot \mathbf{1}.$$
Because $\mathbf{1}(0) = 1 \neq 0$, the left-hand side vanishes in `DiscSpace` iff $\zeta(2s) = 0$, proving (1) $\iff$ (5). By `MayerScatteringMultiplicity.determinant_order`, $\operatorname{ord}_{2s}\det(1 - \mathcal{L}_v^{\mathrm{src}}) = \operatorname{ord}_{2s} B_+ + \operatorname{ord}_{2s}\zeta$ with $\operatorname{ord}_{2s} B_+ < \infty$ (`cofactor_order_ne_top`), and since $\zeta$ is analytic at $2s \neq 1$, $\operatorname{ord}_{2s}\zeta > 0 \iff \zeta(2s) = 0$, proving (2) $\iff$ (5). Equivalence with (3) and (4) follows from `MayerBoundaryResolvent.positiveBoundary_pole_iff` and `scattering_pole_iff` (using $2s / 2 = s$). Observable period continuation follows from `observable_remainder_eigenfunction`, `source_eq`, and `MayerGlobalPeriods.reciprocity` and `three_term`. If $\operatorname{Im} s = 0$, then $2s = 2\sigma \in (0,1)$, where `RHTower.xi_pos_on_real_anchor` gives $\xi(2\sigma) > 0$, contradicting `xi_eq_zero_iff`. Finally, $s \mapsto 2s - 1$ is an injective map sending $\{s \mid \tfrac{1}{4} < \operatorname{Re} s < \tfrac{1}{2} \land \mathrm{IsMayerScatteringResonance}(s)\}$ onto `reflectionPoles`, whose `.encard` equals `boostPolarIndex ratCorr` by `boostPolarIndex_ratCorr_eq_encard_reflectionPoles`. $\square$

### 2. Operator-Native Construction of $Z_{\mathrm{PM}}$ via the Lewis Reflection $s \leftrightarrow 1 - s$
The Lewis three-term relation carries the involution $s \mapsto 1 - s$ (`w = 2s \mapsto 2(1 - s)`). Neither `MayerScatteringState.state`, `MayerCutoff.zeroPoint`, nor `MayerScatteringNormalization.archimedeanFactor` ($a_{\mathrm{PM}}(u) = \mathcal{F}[K_{\mathrm{Cauchy}}(u)](0) = \pi^{1/2}\Gamma(u - \tfrac{1}{2})/\Gamma(u)$) contains `riemannZeta` or `hardyZ` in its definition. Define the reflected Mayer archimedean factor and complex Mayer amplitude:
$$\mathcal{A}_{\mathrm{PM}}(s) := \pi^{s - 1}\,\Gamma(1 - s)\,a_{\mathrm{PM}}(1 - s), \qquad \mathcal{Z}_{\mathrm{PM}}^{\mathbb{C}}(s) := \frac{\mathcal{A}_{\mathrm{PM}}(s)}{\|\mathcal{A}_{\mathrm{PM}}(s)\|} \cdot \frac{(\mathrm{state}(2(1 - s)))(0)}{2}.$$
Along the critical scattering line $s_{\mathrm{crit}}(\tau) := \tfrac{1}{4} + i\tfrac{\tau}{2}$ ($\tau \in \mathbb{R}$), define $Z_{\mathrm{PM}}(\tau) := \operatorname{Re}\mathcal{Z}_{\mathrm{PM}}^{\mathbb{C}}(s_{\mathrm{crit}}(\tau))$.

**Theorem 2.1 (Exact critical-line reality and polar bridge).**
1. For every $s$ with $\operatorname{Re} s < \tfrac{1}{2}$, $\mathcal{A}_{\mathrm{PM}}(s) = \Gamma_{\mathbb{R}}(1 - 2s) \neq 0$.
2. For every $\tau \in \mathbb{R}$, $1 - 2s_{\mathrm{crit}}(\tau) = \overline{\tfrac{1}{2} + i\tau}$, so $\mathcal{A}_{\mathrm{PM}}(s_{\mathrm{crit}}(\tau)) / \|\mathcal{A}_{\mathrm{PM}}(s_{\mathrm{crit}}(\tau))\| = u_\Gamma(\tau)$ (`RHTower.gammaHardyPhase τ`), and by `state_zero` (since $\operatorname{Re}(2(1 - s_{\mathrm{crit}}(\tau))) = \tfrac{3}{2} > 0$ and $\tfrac{3}{2} - i\tau \neq 2$),
$$\frac{(\mathrm{state}(2(1 - s_{\mathrm{crit}}(\tau))))(0)}{2} = \zeta(1 - 2s_{\mathrm{crit}}(\tau)) = \overline{\zeta(\tfrac{1}{2} + i\tau)}.$$
3. Consequently, $\operatorname{Im}\mathcal{Z}_{\mathrm{PM}}^{\mathbb{C}}(s_{\mathrm{crit}}(\tau)) = 0$ identically for all $\tau \in \mathbb{R}$:
$$\mathcal{Z}_{\mathrm{PM}}^{\mathbb{C}}(s_{\mathrm{crit}}(\tau)) = \overline{u_\Gamma(\tau)\,\overline{\dots}} = \overline{\overline{u_\Gamma(\tau)}\,\zeta(\tfrac{1}{2} + i\tau)} = Z(\tau) \in \mathbb{R},$$
so $(Z_{\mathrm{PM}}(\tau) : \mathbb{C}) = \mathcal{Z}_{\mathrm{PM}}^{\mathbb{C}}(s_{\mathrm{crit}}(\tau))$ and $Z_{\mathrm{PM}}(\tau) = \mathrm{hardyZ}(\tau)$ for all $\tau \in \mathbb{R}$.
4. For every $\tau \in \mathbb{R}$, $Z_{\mathrm{PM}}(\tau) = 0 \iff \mathrm{IsMayerScatteringResonance}(s_{\mathrm{crit}}(\tau))$.

*Proof.* For $\operatorname{Re} s < \tfrac{1}{2}$, $\operatorname{Re}(1 - s) > \tfrac{1}{2} > 0$, so $\Gamma(1 - s) \neq 0$, and cancelling $\Gamma(1 - s)$ against the denominator of $a_{\mathrm{PM}}(1 - s) = \pi^{1/2}\Gamma(\tfrac{1}{2} - s)/\Gamma(1 - s)$ yields $\pi^{s - 1}\pi^{1/2}\Gamma(\tfrac{1}{2} - s) = \pi^{-(1 - 2s)/2}\Gamma((1 - 2s)/2) = \Gamma_{\mathbb{R}}(1 - 2s) \neq 0$. At $s = s_{\mathrm{crit}}(\tau)$, $1 - 2s_{\mathrm{crit}}(\tau) = \tfrac{1}{2} - i\tau = \overline{\mathrm{linePt}(\tau)}$. Thus $\mathcal{A}_{\mathrm{PM}}(s_{\mathrm{crit}}(\tau)) = \Gamma_{\mathbb{R}}(\overline{\mathrm{linePt}(\tau)}) = \overline{\Gamma_{\mathbb{R}}(\mathrm{linePt}(\tau))}$, whose unit normalization is `gammaHardyPhase τ`. Meanwhile $2(1 - s_{\mathrm{crit}}(\tau)) - 1 = 1 - 2s_{\mathrm{crit}}(\tau) = \overline{\mathrm{linePt}(\tau)}$, so `state_zero` and `riemannZeta_conj_of_re_pos` give $((\mathrm{state}(2(1 - s_{\mathrm{crit}}(\tau))))(0))/2 = \overline{\zeta(\mathrm{linePt}(\tau))}$. By `RHTower.zeta_line_eq_gammaHardyPhase_mul_hardyZ`, $\zeta(\mathrm{linePt}(\tau)) = u_\Gamma(\tau) Z(\tau)$ with $|u_\Gamma(\tau)| = 1$ and $Z(\tau) \in \mathbb{R}$, whence $u_\Gamma(\tau)\,\overline{\zeta(\mathrm{linePt}(\tau))} = u_\Gamma(\tau)\,\overline{u_\Gamma(\tau)} Z(\tau) = Z(\tau) \in \mathbb{R}$. Finally, $Z_{\mathrm{PM}}(\tau) = 0 \iff \zeta(\mathrm{linePt}(\tau)) = 0 \iff \mathrm{IsMayerScatteringResonance}(s_{\mathrm{crit}}(\tau))$ by Theorem 1.1 and $2s_{\mathrm{crit}}(\tau) = \mathrm{linePt}(\tau)$. $\square$

### 3. Transverse Core-Moment Slope Formula, Odd-Order Sign Flips, Hardy's Theorem, and $> 67.250071\%$ Proportion

**Theorem 3.1 (Strict sign change $\implies$ odd-multiplicity Mayer scattering resonance).**
If $\tau_1 < \tau_2$ and $Z_{\mathrm{PM}}(\tau_1)\,Z_{\mathrm{PM}}(\tau_2) < 0$, there exists $\tau' \in (\tau_1, \tau_2)$ such that $s_{\mathrm{crit}}(\tau')$ is a Mayer scattering resonance of **odd** determinant-excess multiplicity:
$$\operatorname{ Odd }\!\bigl(\operatorname{ord}_{2s_{\mathrm{crit}}(\tau')}^{\mathbb{N}} \det(1 - \mathcal{L}_v^{\mathrm{src}}) - \operatorname{ord}_{2s_{\mathrm{crit}}(\tau')}^{\mathbb{N}} B_+(v)\bigr).$$

*Proof.* By Theorem 2.1, `RHTower.exists_odd_analyticOrderAt_xi_of_hardyZ_mul_neg` produces $\tau' \in (\tau_1, \tau_2)$ with $\xi(\mathrm{linePt}(\tau')) = 0$ and $\operatorname{Odd}((\operatorname{ord}_{\mathrm{linePt}(\tau')}\xi).\mathrm{toNat})$. By `xi_analyticOrderAt_eq_riemannZeta_of_mem_strip` and `MayerScatteringMultiplicity.determinant_orderNat`, this natural order equals $\operatorname{ord}^{\mathbb{N}}\det(1 - \mathcal{L}_v^{\mathrm{src}}) - \operatorname{ord}^{\mathbb{N}} B_+$ at $2s_{\mathrm{crit}}(\tau')$. $\square$

**Theorem 3.2 (Transverse Mayer core-moment slope formula & converse sign flip at simple resonances).**
Let $\tau_0 > 0$ be such that $s_0 = s_{\mathrm{crit}}(\tau_0)$ is a critical-line Mayer scattering resonance.
1. $Z_{\mathrm{PM}}$ is differentiable on $\mathbb{R}$, and its slope at $\tau_0$ is given in terms of the absolutely convergent zero-endpoint Mellin moment of the scattering-subtracted Mayer core $\phi_{2s_0} = \mathrm{fieldCore}(2s_0)$ by
$$Z_{\mathrm{PM}}'(\tau_0) = \operatorname{Re}\!\Bigl(i\,\overline{u_\Gamma(\tau_0)}\,\mathcal{M}[\phi_{2s_0}](0)\Bigr), \qquad \operatorname{Im}\!\Bigl(i\,\overline{u_\Gamma(\tau_0)}\,\mathcal{M}[\phi_{2s_0}](0)\Bigr) = 0.$$
2. $Z_{\mathrm{PM}}'(\tau_0) \neq 0 \iff \mathcal{M}[\phi_{2s_0}](0) \neq 0 \iff s_0$ has unit determinant excess ($\operatorname{ord}_{2s_0}^{\mathbb{N}}\det(1 - \mathcal{L}_v^{\mathrm{src}}) = \operatorname{ord}_{2s_0}^{\mathbb{N}} B_+ + 1$).
3. Whenever $\mathcal{M}[\phi_{2s_0}](0) \neq 0$, there exists $\delta_0 > 0$ such that for all $\delta \in (0, \delta_0)$, $Z_{\mathrm{PM}}(\tau_0 - \delta)\,Z_{\mathrm{PM}}(\tau_0 + \delta) < 0$.

*Proof.* By `RHTower.differentiable_hardyZ` and `differentiable_gammaHardyPhase`, differentiating $\zeta(\tfrac{1}{2} + i\tau) = u_\Gamma(\tau)\,Z_{\mathrm{PM}}(\tau)$ along $\tau \mapsto \tfrac{1}{2} + i\tau$ at $\tau_0$ (where $Z_{\mathrm{PM}}(\tau_0) = 0$) gives $i\,\zeta'(\tfrac{1}{2} + i\tau_0) = u_\Gamma'(\tau_0)\cdot 0 + u_\Gamma(\tau_0)\,Z_{\mathrm{PM}}'(\tau_0)$. Multiplying by $\overline{u_\Gamma(\tau_0)}$ (using $|u_\Gamma(\tau_0)| = 1$) gives $(Z_{\mathrm{PM}}'(\tau_0) : \mathbb{C}) = i\,\overline{u_\Gamma(\tau_0)}\,\zeta'(2s_0)$. Since $\tau_0 > 0$, $\operatorname{Im}(2s_0) = \tau_0 > 0$, so `MayerCoreZeroMoment.core_zero_hasMellin_zero` identifies $\zeta'(2s_0) = \mathcal{M}[\phi_{2s_0}](0)$, yielding (1). Since $|i\,\overline{u_\Gamma(\tau_0)}| = 1$, $Z_{\mathrm{PM}}'(\tau_0) \neq 0 \iff \mathcal{M}[\phi_{2s_0}](0) \neq 0 \iff \zeta'(2s_0) \neq 0 \iff \operatorname{ord}_{2s_0}^{\mathbb{N}}\zeta = 1$, which equals the unit determinant excess by `determinant_orderNat`, proving (2). For (3), if $f : \mathbb{R} \to \mathbb{R}$ satisfies $\mathrm{HasDerivAt}\;f\;L\;\tau_0$ with $f(\tau_0) = 0$ and $L \neq 0$, then $h^{-1} f(\tau_0 + h) \to L$ as $h \to 0$ in $\mathcal{N}_{\neq}(0)$; hence for $|h| < \delta_0$ ($h \neq 0$), $|h^{-1}f(\tau_0 + h) - L| < |L|/2$, so $(h^{-1}f(\tau_0 + h))\cdot (-\delta^{-1}f(\tau_0 - \delta))$ at $h = \delta \in (0, \delta_0)$ gives $\delta^{-2} f(\tau_0 + \delta) f(\tau_0 - \delta) = -((\delta^{-1}f(\tau_0 + \delta))\cdot ((-\delta)^{-1}f(\tau_0 - \delta))) < -( |L|/2 )^2 < 0$, whence $f(\tau_0 - \delta) f(\tau_0 + \delta) < 0$. $\square$

**Theorem 3.3 (Operator Hardy Theorem and $> 67.250071\%$ Positive Proportion of Disjoint Strict Sign Changes).**
Define the cumulative Mayer resonance count (with multiplicity) up to height $T$ by
$$N_{\mathrm{PM}}(T) := \sum_{s \in \mathcal{R}_{\mathrm{PM}}(T)} \bigl(\operatorname{ord}_{2s}^{\mathbb{N}}\det(1 - \mathcal{L}_v^{\mathrm{src}}) - \operatorname{ord}_{2s}^{\mathbb{N}} B_+\bigr), \qquad \mathcal{R}_{\mathrm{PM}}(T) := \{s \mid 0 < \operatorname{Re} s < \tfrac{1}{2},\; 0 < \operatorname{Im}(2s) \le T,\; \mathrm{IsMayerScatteringResonance}(s)\}.$$
1. (**Exact census bridge**) $N_{\mathrm{PM}}(T) = \mathrm{xiPosZeroCount}(T) = \mathrm{Zeta23.Ncount}(0, T)$.
2. (**Quantitative positive proportion of disjoint strict sign changes**) For every $\varepsilon > 0$, there exists $T_0$ such that for all $T \ge T_0$, there exist $m \in \mathbb{N}$ and $a, b : \mathrm{Fin}\,m \to \mathbb{R}$ satisfying:
   - $(67250071 / 100000000 - \varepsilon)\,N_{\mathrm{PM}}(T) \le m$,
   - for every $j$, $0 < a(j) < b(j) < T$ and $Z_{\mathrm{PM}}(a(j))\,Z_{\mathrm{PM}}(b(j)) < 0$,
   - for all $j_1 < j_2$, $b(j_1) < a(j_2)$ (strictly separated open intervals in $(0, T)$).
3. (**Operator Hardy Theorem**) For every $M \in \mathbb{R}$, there exist $\tau_1, \tau_2 \in \mathbb{R}$ with $M < \tau_1 < \tau_2$ and $Z_{\mathrm{PM}}(\tau_1)\,Z_{\mathrm{PM}}(\tau_2) < 0$.

*Proof.* (1) The bijection $s \mapsto 2s$ maps $\mathcal{R}_{\mathrm{PM}}(T)$ onto `RHTower.stripFinsetPos T`, and `determinant_orderNat` together with `xi_analyticOrderAt_eq_riemannZeta_of_mem_strip` matches each summand with $(\operatorname{ord}_{2s}\xi).\mathrm{toNat}$, giving $N_{\mathrm{PM}}(T) = \mathrm{xiPosZeroCount}(T) = \mathrm{Zeta23.Ncount}(0,T)$.

(2) Let $\varepsilon > 0$. By `IncommensurableGaborPinching.simple_critical_proportion_ge_67250071` and `zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount` applied at $\varepsilon / 2 > 0$, there exists $T_1$ such that for $T \ge T_1$, the finite set $S(T) \subset (0, T]$ of ordinates $\gamma$ of simple critical-line zeros of $\xi$ has cardinality $k = |S(T)| \ge (67250071/100000000 - \varepsilon/2)\,N_{\mathrm{PM}}(T)$. Since $N_{\mathrm{PM}}(T) = \mathrm{Ncount}(0, T) \to \infty$ as $T \to \infty$ (`Zeta23.tendsto_Ncount_zero_atTop`), there exists $T_2 \ge \max(T_1, 1)$ such that for all $T \ge T_2$, $(\varepsilon / 2)\,N_{\mathrm{PM}}(T) \ge 1$. If $67250071/100000000 - \varepsilon \le 0$, $m = 0$ trivially works. Otherwise $k \ge 2$ for $T \ge T_2$. Enumerating $S(T)$ in strictly increasing order via `Finset.orderEmbOfFin` gives $0 < \gamma_0 < \gamma_1 < \dots < \gamma_{k-1} \le T$. Set $m := k - 1 \ge 1$; then for every $j \in \{0, \dots, m - 1\}$, $0 < \gamma_j < \gamma_{j+1} \le T$, so $\gamma_j \in (0, T)$ strictly! At each $\gamma_j$, $s_{\mathrm{crit}}(\gamma_j)$ is a simple critical-line Mayer resonance, so Theorem 3.2(3) supplies $\delta_j > 0$ with $Z_{\mathrm{PM}}(\gamma_j - \delta)\,Z_{\mathrm{PM}}(\gamma_j + \delta) < 0$ for all $\delta \in (0, \delta_j)$. Choose $\delta > 0$ smaller than $\min_{0 \le j < m} \delta_j$, smaller than $\gamma_0 / 2$, smaller than $(T - \gamma_{m-1})/2$, and smaller than $\tfrac{1}{3}\min_{0 \le j < m-1}(\gamma_{j+1} - \gamma_j)$. Setting $a(j) := \gamma_j - \delta$ and $b(j) := \gamma_j + \delta$ gives $0 < a(j) < b(j) < T$, $b(j_1) \le \gamma_{j_2 - 1} + \delta < \gamma_{j_2} - \delta = a(j_2)$ for $j_1 < j_2$, and $m = k - 1 \ge (67250071/100000000 - \varepsilon/2)N_{\mathrm{PM}}(T) - 1 \ge (67250071/100000000 - \varepsilon)N_{\mathrm{PM}}(T)$.

(3) Fix $M \in \mathbb{R}$, set $M_+ = \max(M, 1) > 0$. Applying (2) with $\varepsilon = 1/2$ gives $T_0$; since $N_{\mathrm{PM}}(T) \to \infty$, choose $T \ge \max(T_0, M_+ + 1)$ so large that $(67250071/100000000 - 1/2)\,N_{\mathrm{PM}}(T) > \mathrm{xiPosZeroCount}(M_+) + 1$. Among the $m > \mathrm{xiPosZeroCount}(M_+) + 1$ pairwise disjoint intervals $(a(j), b(j)) \subset (0, T)$ on each of which $Z_{\mathrm{PM}}$ has a strict sign change (hence a zero in $(a(j), b(j))$), at most $\mathrm{xiPosZeroCount}(M_+)$ can satisfy $(a(j), b(j)) \cap (0, M_+] \neq \emptyset$ except possibly the single interval straddling $M_+$: indeed, if $j_0 < j_1 < \dots < j_r$ all satisfy $a(j_i) \le M_+$, then for $0 \le i < r$, $b(j_i) < a(j_r) \le M_+$, producing $r$ distinct zeros of $\xi$ in $(0, M_+]$, so $r \le \mathrm{xiPosZeroCount}(M_+)$. Since $m > \mathrm{xiPosZeroCount}(M_+) + 1$, the top index $j_{\max} = m - 1$ satisfies $a(j_{\max}) > M_+ \ge M$, yielding $M < a(j_{\max}) < b(j_{\max})$ with $Z_{\mathrm{PM}}(a(j_{\max}))\,Z_{\mathrm{PM}}(b(j_{\max})) < 0$. $\square$

## Lean Formalization
- `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerResonanceCharacterization`:
  - `IsMayerScatteringResonance`, `mayerResonanceMultiplicity`, `resonantLewisPeriod`, `riemannMayerReflect`
  - `isMayerScatteringResonance_iff_zeta_zero`, `isMayerScatteringResonance_iff_xi_zero`
  - `isMayerScatteringResonance_iff_determinant_excess`, `isMayerScatteringResonance_iff_positiveBoundary_pole`, `isMayerScatteringResonance_iff_scatteringEntry_pole`
  - `im_ne_zero_of_isMayerScatteringResonance`, `resonantLewisPeriod_reciprocity`, `resonantLewisPeriod_three_term`, `resonantLewisPeriod_one_ne_zero`
  - `boostPolarIndex_ratCorr_eq_two_mul_encard_upperRightMayerResonances`, `riemannHypothesis_iff_forall_isMayerScatteringResonance_re`
- `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerZFunction`:
  - `criticalScatteringPt`, `mayerReflectedArchFactor`, `mayerComplexZ`, `mayerZ`, `mayerResonanceCount`
  - `mayerComplexZ_critical_eq_ofReal_hardyZ`, `mayerComplexZ_critical_im`, `mayerZ_eq_zero_iff_resonance`
  - `exists_odd_mayerResonance_of_mayerZ_sign_change`
  - `ofReal_deriv_mayerZ_eq_core_mellin_zero`, `deriv_mayerZ_ne_zero_iff_simple_resonance`, `exists_local_mayerZ_sign_change_of_simple_resonance`
  - `mayerResonanceCount_eq_xiPosZeroCount`, `mayerResonanceCount_eq_Ncount`
  - `eventually_disjoint_mayerZ_sign_changes_proportion`, `exists_mayerZ_sign_change_gt`

## Log
- 2026-11-02 — complete dependency-closed paper proof recorded in 2-fully-proven
- 2026-11-02 — unconditionally formalized in Lean 4 and moved to 3-formalized
