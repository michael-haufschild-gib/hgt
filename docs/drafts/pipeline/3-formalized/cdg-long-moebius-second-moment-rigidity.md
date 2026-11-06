# Exact slope rigidity, quantifier collapse, and pure-Möbius equivalence for long critical-line moments

- **ID:** CDG-LONG-MOEBIUS-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0511/route-wd.md` §1 · `ConjugateDiagonalGeometry/NearLineLogMean/TwoSidedThetaMollifierTrap.lean`
- **Statement:** For $M_X(s) = \sum_{1 \le n \le X} \mu(n) n^{-s}$ and $w = \mathrm{zetaZeroWidth}$, the coupled $[1, T]$ second moments at $X = \lfloor T^\theta \rfloor$ obey the unconditional slope law $\int_1^T |\zeta M_{\lfloor T^\theta \rfloor}(\frac{1}{2}+it)|^2\,dt \le C_\theta T^{6 + 2w\theta}$ (and $\int_1^T |M_{\lfloor T^\theta \rfloor}(\frac{1}{2}+it)|^2\,dt \le C_\theta T^{4 + 2w\theta}$) for all $\theta > 0, T \ge 1$ without zero-simplicity assumptions, while any cofinal-$\theta$, sparse-$T$ bound of growth $C_\theta T^{K + 2\beta\theta}$ (for either $|\zeta M_{\lfloor T^\theta \rfloor}|^2$ or $|M_{\lfloor T^\theta \rfloor}|^2$) forces $w \le \beta$, collapsing all quantifiers and fixed exponents $K \ge 0$ to universal $K = 6$ (resp. $K = 4$) and forbidding $\theta$-uniform constants $C$.

## Goal
Resolve the exact $\theta$-slope, quantifier structure, pure-Möbius reduction, and $\theta$-constant growth of `route-wd.md` §1 unconditionally in terms of `zetaZeroWidth`.

## Gates
- [x] 0 → 1  in-progress: exact $2w\theta$ upper/lower slope, quantifier collapse, pure-Möbius equivalence, and $\theta$-uniformity no-go stated
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, complete unconditional paper proofs with zero unproved premises
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean` (`riemannZeta_ne_zero_of_mem_Ioo_zero_one`, `exists_pure_moebius_moment_le_zetaZeroWidth`, `exists_moebius_mollifier_moment_le_zetaZeroWidth`, `zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope`, `zetaZeroWidth_le_of_cofinal_pure_moebius_slope`, `zetaZeroWidth_le_iff_cofinal_moebius_mollifier_slope`, `cofinal_moebius_mollifier_slope_iff_forall`, `riemannHypothesis_iff_cofinal_moebius_mollifier`, `cofinal_moebius_mollifier_self_improves_to_all`, `riemannHypothesis_of_width_slope_saving`, `riemannHypothesis_iff_cofinal_pure_moebius_moment`, `cofinal_pure_moebius_moment_iff_cofinal_moebius_mollifier`, `eventually_exists_theta_pure_moebius_moment_gt`, `not_exists_theta_uniform_pure_moebius_moment`)

## Theorems and complete paper proofs `[PROVED HERE]`

### Theorem 1 (Unconditional upper slope law without simplicity hypotheses) `[PROVED HERE]`
Let $w = \mathrm{zetaZeroWidth} \in [0, \frac{1}{2}]$. For every $\theta > 0$, there exist $C_\theta^{(0)}, C_\theta \ge 0$ such that for every $T \ge 1$:
$$\int_1^T \left|M_{\lfloor T^\theta \rfloor}\!\left(\tfrac{1}{2}+it\right)\right|^2 dt \le C_\theta^{(0)}\, T^{4 + 2w\theta}, \qquad \int_1^T \left|\zeta\!\left(\tfrac{1}{2}+it\right) M_{\lfloor T^\theta \rfloor}\!\left(\tfrac{1}{2}+it\right)\right|^2 dt \le C_\theta\, T^{6 + 2w\theta}.$$
Consequently, for any $\beta \ge 0$ satisfying `XiZeroHalfPlaneBound β` (equivalently $w \le \beta$), the same bounds hold with $\beta$ in place of $w$.

*Proof.* Apply `exists_norm_moebiusPoly_line_le` with $\varepsilon = \frac{1}{2\theta} > 0$: there exists $K \ge 0$ such that for all $X \ge 1$ and $t \in \mathbb{R}$, $\|M_X(\frac{1}{2}+it)\| \le 2 K (1 + |t|) X^{w + 1/(2\theta)}$. For $T \ge 1$ and $\theta > 0$, $T^\theta \ge 1$, so $X = \lfloor T^\theta \rfloor_+ \ge 1$ and $(X : \mathbb{R}) \le T^\theta$. On $t \in [1, T]$, $1 + |t| = 1 + t \le 2T$ and $(X : \mathbb{R})^{w + 1/(2\theta)} \le (T^\theta)^{w + 1/(2\theta)} = T^{w\theta + 1/2}$. Thus $\|M_X(\frac{1}{2}+it)\|^2 \le 16 K^2 T^{3 + 2w\theta}$ across $[1, T]$, and integrating over $[1, T]$ of length $T - 1 \le T$ yields $\int_1^T \|M_X(\frac{1}{2}+it)\|^2 dt \le 16 K^2 T^{4 + 2w\theta}$. Multiplying pointwise by `norm_zeta_linePoint_le` ($\|\zeta(\frac{1}{2}+it)\| \le 18(1 + |t|) \le 36 T$ on $[1, T]$) yields $\int_1^T \|\zeta M_X(\frac{1}{2}+it)\|^2 dt \le 36^2 \cdot 16 K^2 T^{6 + 2w\theta}$. Neither zero simplicity nor discrete residue bounds $J_{-1}(T)$ are used. $\square$

### Theorem 2 (Sharp $2\beta\theta$ converse for both mollified and pure Möbius moments) `[PROVED HERE]`
Let $\beta \ge 0$ and $K \ge 0$. Suppose that for arbitrarily large $\theta > 0$, there exists $C_\theta \ge 0$ and an unbounded sequence of heights $T$ (`∃ᶠ T in atTop`) satisfying **either**:
1. $\int_1^T |\zeta(\frac{1}{2}+it) M_{\lfloor T^\theta \rfloor}(\frac{1}{2}+it)|^2\,dt \le C_\theta T^{K + 2\beta\theta}$, **or**
2. $\int_1^T |M_{\lfloor T^\theta \rfloor}(\frac{1}{2}+it)|^2\,dt \le C_\theta T^{K + 2\beta\theta}$.

Then $\mathrm{zetaZeroWidth} \le \beta$ (equivalently `XiZeroHalfPlaneBound β`).

*Proof.* Suppose for contradiction that $\beta < w := \mathrm{zetaZeroWidth}$, and set $g := w - \beta > 0$. Let $p_0 := \frac{w/2}{\pi(5/4)} > 0$ and $t_0 := \min(\frac{w}{2}, \frac{p_0 g}{8}) > 0$. By `exists_zetaZero_mem_openStrip_lt_re`, choose a zero $\rho_0$ of $\zeta$ with $\frac{1}{2} + w - t_0 < \operatorname{Re}\rho_0 < 1$. Since $\operatorname{Re}\rho_0 > \frac{1}{2}$ and $\rho_0 \ne 1$, `riemannZeta_ne_zero_of_xi_ne_zero` implies $\xi(\rho_0) = 0$, whence `xi_ne_zero_of_abs_im_le_nine_halves` gives $|\operatorname{Im}\rho_0| > \frac{9}{2}$. Replacing $\rho_0$ by $\overline{\rho_0}$ if $\operatorname{Im}\rho_0 < 0$ (using $\zeta(\overline{\rho_0}) = \overline{\zeta(\rho_0)} = 0$) produces a zero $\rho$ with $\operatorname{Re}\rho = \operatorname{Re}\rho_0 \in (\frac{1}{2}, 1)$, $w - (\operatorname{Re}\rho - \frac{1}{2}) \le t_0$, and $\gamma := \operatorname{Im}\rho > \frac{9}{2} > 2$.

Consequently $[\gamma - 1, \gamma + 1] \subseteq [1, T]$ whenever $T \ge \gamma + 1$. On $u \in [\gamma - 1, \gamma + 1]$, $\|E_X(u)\|^2 = \|\zeta(\frac{1}{2}+iu) M_X(\frac{1}{2}+iu) - 1\|^2 \le 2\|\zeta(\frac{1}{2}+iu) M_X(\frac{1}{2}+iu)\|^2 + 2$, and under case (2) $\|\zeta(\frac{1}{2}+iu)\| \le 18(1 + |u|) \le 18(2 + \gamma)$ gives $\|E_X(u)\|^2 \le 648(2 + \gamma)^2 \|M_X(\frac{1}{2}+iu)\|^2 + 2$. Thus in both cases, for $T \ge \gamma + 1$ along the assumed sequence at a single chosen $\theta \ge \max(1, \frac{4(K + 1)}{g})$, setting $X = \lfloor T^\theta \rfloor_+$, we have $T^\theta \le 2 X$ (for $T^\theta \ge 2$) and
$$\int_{\gamma - 1}^{\gamma + 1} \|E_X(u)\|^2\,du \le A_\theta T^{K + 2\beta\theta} + 4 \le X^{2(\beta + g/3)}$$
for arbitrarily large $T$ (hence arbitrarily large $X$). By Markov's inequality on $[\gamma - 1, \gamma + 1]$ of measure $2$, the complement of $\mathrm{lowSet}(X, \beta + \frac{g}{2})$ in $[\gamma - 1, \gamma + 1]$ has measure at most $X^{-g/3} \le 1$, so $|\mathrm{lowSet}(X, \beta + \frac{g}{2}) \cap [\gamma - 1, \gamma + 1]| \ge 1$. Since $P_\rho(u) \ge p_0$ on $[\gamma - 1, \gamma + 1]$, the $P_\rho$-mass of $\mathrm{lowSet}(X, \beta + \frac{g}{2})$ is at least $p_0$ for arbitrarily large $X$, contradicting `eventually_poissonMass_lowSet_le` (which bounds this mass eventually by $\frac{w - (\operatorname{Re}\rho - 1/2)}{g/2} + \frac{p_0}{4} \le \frac{t_0}{g/2} + \frac{p_0}{4} \le \frac{p_0}{2}$). $\square$

### Theorem 3 (Corollaries: RH equivalences, quantifier/exponent collapse, width bootstrap, and $\theta$-nonuniformity) `[PROVED HERE]`
1. **Two-sided equivalence for `route-wd.md` §1 (`riemannHypothesis_iff_cofinal_moebius_mollifier`):** `RiemannHypothesis` holds if and only if there exists $K \ge 0$ such that for arbitrarily large $\theta > 0$, some $C_\theta \ge 0$ satisfies $\exists^\infty T,\ \int_1^T |\zeta M_{\lfloor T^\theta \rfloor}(\frac{1}{2}+it)|^2\,dt \le C_\theta T^K$.
2. **Total quantifier and exponent collapse (`cofinal_moebius_mollifier_slope_iff_forall`):** For every $\beta \ge 0$, the sparse/cofinal condition with existential $K \ge 0$ is unconditionally equivalent to the universal bound with $K = 6$, all $\theta > 0$, and all $T \ge 1$.
3. **Self-improving width bootstrap (`riemannHypothesis_of_width_slope_saving`):** Any strict slope saving $2w - \Delta$ ($\Delta > 0$) below $2w$ forces $w = 0$, hence `RiemannHypothesis` and universal $K = 6$.
4. **Pure-Möbius equivalence (`riemannHypothesis_iff_cofinal_pure_moebius_moment`, `cofinal_pure_moebius_moment_iff_cofinal_moebius_mollifier`):** `RiemannHypothesis` (and `route-wd.md` §1) is unconditionally equivalent to cofinal-$\theta$, sparse-$T$ polynomial boundedness $\int_1^T |M_{\lfloor T^\theta \rfloor}(\frac{1}{2}+it)|^2\,dt \le C_\theta T^{K_0}$ (collapsing to $K_0 = 4$ for all $\theta > 0, T \ge 1$).
5. **Unconditional $\theta$-nonuniformity (`eventually_exists_theta_pure_moebius_moment_gt`, `not_exists_theta_uniform_pure_moebius_moment`):** For every height-only bound $f : \mathbb{R} \to \mathbb{R}$, all sufficiently large $T \ge 2$ admit $m \ge 1$ with $\int_{T/2}^T \|M_m(\frac{1}{2}+it)\|^2 dt > f(T)$ by `eventually_not_uniform_moebius`; setting $\theta = \frac{\log(m + 1/2)}{\log T} > 0$ gives $\lfloor T^\theta \rfloor_+ = m$ and $\int_1^T \|M_{\lfloor T^\theta \rfloor}(\frac{1}{2}+it)\|^2 dt > f(T)$. In particular no $\theta$-independent constant $C$ can bound the pure Möbius moment across all $\theta > 0$ and $T \ge 1$. $\square$

## Log
- 2026-11-06 — formalized in `ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean` and wired into `ConjugateDiagonalGeometry.lean`.
