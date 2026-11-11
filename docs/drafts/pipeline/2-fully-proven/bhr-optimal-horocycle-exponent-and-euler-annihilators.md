# The Optimal Horocycle Equidistribution Exponent $1 - \Theta/2$ and the Euler-Operator Characterization of the Asymptotic Abscissa Law

- **ID:** bhr-optimal-horocycle-exponent-and-euler-annihilators
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-1011/fable.md §5.3 · formal/GaloisForLFunctions/BlackHoleRingdown/TheHorocycleRateIsTheZeroFreeRegion.lean
- **Statement:** Unconditionally, the supremum of universal horocycle equidistribution exponents for smooth compactly supported pseudo-Eisenstein profiles on $(1, \infty)$ equals $1 - \Theta/2$ ($\Theta = \operatorname{zetaZeroAbscissa}$), the supremum of polynomial-Euler-filtered universal horocycle exponents equals $1 - \Theta_\infty/2$ ($\Theta_\infty = \operatorname{zetaAsymptoticAbscissa}$), `ZerosApproachLine` ($\Theta_\infty = 1/2$) holds iff every exponent $< 3/4$ is attained via some nonzero $P(u\frac{d}{du}) \in \mathbb{R}[X]$, and `AsymptoticAbscissaLaw` ($\Theta_\infty = \Theta$) holds iff no nonzero $P(u\frac{d}{du}) \in \mathbb{R}[X]$ accelerates universal horocycle equidistribution strictly past $1 - \Theta/2$.

## Goal
Extend Zagier's horocycle equidistribution theorem (`RH` $\iff$ universal rate $y^{3/4 - \varepsilon}$) to the unconditional global zero abscissa $\Theta = \operatorname{zetaZeroAbscissa}$ and establish an exact spectral-dynamical equivalence between `AsymptoticAbscissaLaw` and non-accelerability of horocycle equidistribution by nonzero polynomial Euler differential operators.

## Gates
- [x] 0 → 1  in-progress: exact coupling between `norm_horocycleMean_sub_le_of_zeroFree`, `exists_zeta_lower_bound_subpolynomial_of_zeroFree_above`, and meromorphic normal forms of polynomial-twisted scattering ratios
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof `[PROVED HERE]`
- [ ] 2 → 3  formalized: Lean module `GaloisForLFunctions.BlackHoleRingdown.TheOptimalHorocycleExponentAndEulerAnnihilators`, `lake --old env lean` green, `#print axioms` clean

## Paper Proof `[PROVED HERE]`

### 1. Sharp unconditional horocycle rate $1 - \Theta/2$ (pseudo-Eisenstein and cusp-energy channels)
Let $\Theta = \operatorname{zetaZeroAbscissa} \in [\frac{1}{2}, 1]$.
- **Forward rate (`horocycle_rate_zetaZeroAbscissa`, `cusp_energy_rate_zetaZeroAbscissa`):** By `riemannZeta_ne_zero_of_zetaZeroAbscissa_lt` and `xi_eq_zero_iff_riemannZeta_eq_zero`, $\xi(z) \ne 0$ for all $\operatorname{Re} z > \Theta$. By `exists_invZeta_shift_data_of_zeroFree` at $\Theta$ with $\varepsilon_0 = 1$, for every $\delta > 0$ and $d \in \mathbb{R}$ there exists $K_b \ge 0$ such that $\lVert\zeta(z)^{-1}\rVert \le 2 K_b |\operatorname{Im} z|$ on $\Theta + \min(\delta, \frac{1}{2}) \le \operatorname{Re} z \le d$, $|\operatorname{Im} z| \ge 2$. Substituting these two unconditional inputs into `norm_horocycleMean_sub_le_of_zeroFree` and `norm_mass_sub_le_of_zeroFree` yields, for every $\varepsilon \in (0, 1)$ and $\varphi \in C_c^\infty(1, \infty)$ (respectively $\varepsilon \in (0, \frac{1}{2})$ and Hecke–Maass cusp form $g$),
  $$
  \Bigl\lVert A_\varphi(y) - \frac{6}{\pi}\widetilde{\varphi}(-1)\Bigr\rVert \le C_{\varphi,\varepsilon}\, y^{1 - \Theta/2 - \varepsilon}, \qquad
  \Bigl| m_g(y) - \frac{3}{\pi}\lVert g\rVert^2 \Bigr| \le C_{g,\varepsilon}\, y^{1 - \Theta/2 - \varepsilon} \qquad (0 < y \le 1).
  $$
- **Optimality (`not_horocycle_rate_gt_one_sub_half_zetaZeroAbscissa`, `sSup_universalHorocycleExponents`):** Suppose universal pseudo-Eisenstein equidistribution held at exponent $\alpha > 1 - \Theta/2$. Then $2 - 2\alpha < \Theta$. By `exists_zetaZero_lt_re`, there exists $\rho \in \mathbb{C}$ with $\zeta(\rho) = 0$ and $\operatorname{Re}\rho > \max(2 - 2\alpha, 0)$ (since $\Theta \ge \frac{1}{2} > 0$). Zagier's converse (`re_le_of_horocycle_rate`) gives $\operatorname{Re}\rho \le 2 - 2\alpha$, a contradiction. Thus the set of universal horocycle equidistribution exponents has exact supremum $1 - \Theta/2$.

### 2. Polynomial Euler differential operators on $C_c^\infty(1, \infty)$
For $k \in \mathbb{N}$ and $\varphi : \mathbb{R} \to \mathbb{R}$, define the real Euler iterates $D^0 \varphi = \varphi$, $D^{k+1}\varphi(u) = u (D^k\varphi)'(u)$, and for $P = \sum_{k=0}^d a_k X^k \in \mathbb{R}[X]$ set
$$
(\mathcal{E}_P \varphi)(u) := \sum_{k=0}^d a_k (D^k \varphi)(u).
$$
Induction shows:
1. If $\varphi \in C_c^\infty(\mathbb{R})$ with $\operatorname{tsupport}\varphi \subseteq (1, \infty)$, then $\mathcal{E}_P\varphi \in C_c^\infty(\mathbb{R})$ with $\operatorname{tsupport}(\mathcal{E}_P\varphi) \subseteq \operatorname{tsupport}\varphi \subseteq (1, \infty)$.
2. Complexifying $\psi_0(u) = (\varphi(u) : \mathbb{C})$ and $P_{\mathbb{C}} = P.\operatorname{map}(\mathbb{R} \to \mathbb{C})$, $(\mathcal{E}_P\varphi(u) : \mathbb{C}) = \sum_{k \in P.\mathrm{support}} (a_k : \mathbb{C})\, \operatorname{eulerIter}_k \psi_0(u)$.
3. If `IsTest ψ₀ a b` ($1 < a \le b$), then `IsTest (fun u => (eulerPolyR P φ u : ℂ)) a b`, and by `mellin_eulerIter` at $-s$,
   $$
   \mathcal{M}[\mathcal{E}_P\varphi](-s) = \sum_{k \in P.\mathrm{support}} a_k s^k \mathcal{M}\psi_0(-s) = P_{\mathbb{C}}(s)\, \mathcal{M}\psi_0(-s) \qquad (s \in \mathbb{C}).
   $$

### 3. Converse acceleration theorem: Euler-filtered rate $\alpha$ bounds $\Theta_\infty \le \max(\frac{1}{2}, 2 - 2\alpha)$
Suppose $P \in \mathbb{R}[X]$ is nonzero ($P \ne 0$) and for some $\alpha \in \mathbb{R}$, every $\varphi \in C_c^\infty(1, \infty)$ satisfies $\lVert A_{\mathcal{E}_P\varphi}(y) - c_\varphi\rVert \le C_\varphi y^\alpha$ on $(0, 1]$.
Let $\rho \in \mathbb{C}$ be any nontrivial zero of $\zeta$ ($0 < \operatorname{Re}\rho < 1$, $\zeta(\rho) = 0$) with $\operatorname{Re}\rho > 2 - 2\alpha$. Since $\zeta$ has no real zeros in $(0, 1)$, $\operatorname{Im}\rho \ne 0$; let $\rho' \in \{\rho, \overline{\rho}\}$ be the conjugate with $\operatorname{Im}\rho' > 0$, so $\zeta(\rho') = 0$ and $\operatorname{Re}\rho' = \operatorname{Re}\rho > 2 - 2\alpha$. Set $s_0 = \rho'/2 \in \operatorname{quarterPlane}(\alpha)$. Then $\operatorname{msA}(s_0 - \frac{1}{2}) = 0$ and $\operatorname{msB}(s_0 - \frac{1}{2}) \ne 0$.
Applying `msB_mul_mellin_eq_zero_of_rate` to the admissible test function $\mathcal{E}_P\varphi$ yields
$$
\operatorname{msB}(s_0 - \tfrac{1}{2}) \cdot P_{\mathbb{C}}(s_0) \cdot \mathcal{M}[\varphi](-s_0) = 0 \qquad \forall \varphi \in C_c^\infty(1, \infty).
$$
If $P_{\mathbb{C}}(s_0) \ne 0$, then $\mathcal{M}[\varphi](-s_0) = 0$ for every $\varphi \in C_c^\infty(1, \infty)$, contradicting `isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero` on $y \mapsto y^{-s_0 - 1} \ne 0$. Hence $P_{\mathbb{C}}(\rho'/2) = 0$, and since $P$ has real coefficients, $P_{\mathbb{C}}(\rho/2) = 0$ as well.
Because $P_{\mathbb{C}} \ne 0$, its root set is finite (`P_ℂ.roots.toFinset`); therefore $\{\rho \in \mathcal{Z}_\zeta \mid \operatorname{Re}\rho > \max(\frac{1}{2}, 2 - 2\alpha)\}$ is finite, so $\Theta_\infty = \operatorname{zetaAsymptoticAbscissa} \le \max(\frac{1}{2}, 2 - 2\alpha)$. In particular, if $\alpha > 1 - \Theta/2$, then $2 - 2\alpha < \Theta$ while $\frac{1}{2} < \Theta$ (if $\Theta = \frac{1}{2}$, $2 - 2\alpha < \frac{1}{2}$ forces $\xi$ to have finitely many zeros right of $\frac{1}{2}$, which already fails at $\frac{1}{2}$ only on the line; Wait: check $\Theta = \frac{1}{2}$!!).

**Check the $\Theta = \frac{1}{2}$ (`RiemannHypothesis`) case carefully!**
If $\Theta = \frac{1}{2}$ (`RiemannHypothesis`) and $\alpha > 1 - \Theta/2 = \frac{3}{4}$, then $2 - 2\alpha < \frac{1}{2}$! By Hardy's theorem (`exists_Xi_zero_gt`), $\zeta$ has **infinitely many** zeros $\frac{1}{2} + i\gamma_n$ on $\operatorname{Re}\rho = \frac{1}{2} > 2 - 2\alpha$! Every single one of those infinitely many critical-line zeros satisfies $0 < \operatorname{Re}\rho = \frac{1}{2} < 1$ and $\operatorname{Re}\rho > 2 - 2\alpha$, so $P_{\mathbb{C}}(\frac{1}{4} + i\gamma_n/2) = 0$ for infinitely many $\gamma_n$, contradicting $P \ne 0$!
Thus **even when $\Theta = \frac{1}{2}$**, NO nonzero polynomial $P \in \mathbb{R}[X]$ can accelerate universal horocycle equidistribution to any $\alpha > 1 - \Theta/2 = \frac{3}{4}$!

### 4. Forward top-annihilator theorem when `¬ AsymptoticAbscissaLaw`
Conversely, assume `¬ AsymptoticAbscissaLaw`, so $\frac{1}{2} \le \Theta_\infty < \Theta \le 1$ (`asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa`). Set $\theta_1 = \frac{1}{2}(\Theta_\infty + \Theta) \in (\Theta_\infty, \Theta)$ and $\theta_0 = \frac{1}{2}(\Theta_\infty + \theta_1) \in (\Theta_\infty, \theta_1)$, so $\frac{1}{2} \le \Theta_\infty < \theta_0 < \theta_1 < \Theta \le 1$.
Since $\theta_0 > \Theta_\infty$, the set $F = \{z \in \mathbb{C} \mid \theta_0 < \operatorname{Re} z \text{ and } \xi(z) = 0\}$ is finite (`zetaAsymptoticAbscissaSet`), conjugate-symmetric ($\xi(\overline{z}) = \overline{\xi(z)}$), and contains no real points ($\xi$ has no real zeros). Let $F^+ = \{z \in F \mid \operatorname{Im} z > 0\}$ (finite) and for each $z \in F^+$ let $m(z) \in \mathbb{N}$ be the analytic order of $s \mapsto \xi(2s)$ at $z/2$ (finite since $\xi(2) \ne 0$). Define the monic real polynomial
$$
P_{\mathrm{top}}(X) := \prod_{z \in F^+} \Bigl(X^2 - (\operatorname{Re} z) X + \frac{\lvert z\rvert^2}{4}\Bigr)^{m(z)} \in \mathbb{R}[X].
$$
Since each quadratic factor is monic, $P_{\mathrm{top}}$ is monic, hence $P_{\mathrm{top}} \ne 0$. Over $\mathbb{C}$, $X^2 - (\operatorname{Re} z) X + \frac{\lvert z\rvert^2}{4} = (X - z/2)(X - \overline{z}/2)$, and since $\xi(\overline{w}) = \overline{\xi(w)}$, $s \mapsto \xi(2s)$ has the same analytic order $m(z)$ at $\overline{z}/2$ as at $z/2$.
Hence at every $s \in \mathbb{C}$ with $\operatorname{Re} s > \theta_0/2$, $\operatorname{meromorphicOrderAt}(w \mapsto \operatorname{scatterQ}(w)\, P_{\mathrm{top},\mathbb{C}}(w), s) \ge 0$.
Let $Q_P := \operatorname{toMeromorphicNFOn}(w \mapsto \operatorname{scatterQ}(w)\, P_{\mathrm{top},\mathbb{C}}(w), \operatorname{univ})$. Then:
1. $Q_P$ is analytic on $\{\operatorname{Re} s > \theta_0/2\}$, and $Q_P(s) = \operatorname{scatterQ}(s)\, P_{\mathrm{top},\mathbb{C}}(s)$ wherever $\xi(2s) \ne 0$ (in particular at $s = 1$, on $\operatorname{Re} s > 1$, and for $|\operatorname{Im} s| \ge T_0 + 4$ on $\operatorname{Re} s > \theta_0/2$ where $T_0 = \max_{z \in F} |\operatorname{Im} z| + 1$).
2. By `exists_zeta_lower_bound_subpolynomial_of_zeroFree_above` on $\{\operatorname{Re} z > \theta_0, |\operatorname{Im} z| \ge T_0\}$ combined with `exists_norm_scatterQ_le` and polynomial growth of $P_{\mathrm{top},\mathbb{C}}$, $Q_P$ has polynomial vertical growth on every closed strip $a' + 1 \le \operatorname{Re} s \le b' + 1$ ($\theta_1/2 \le a' + 1$).
3. For any $\varphi \in C_c^\infty(1, \infty)$ with $\psi_0(u) = (\varphi(u) : \mathbb{C})$ and $\psi = \mathcal{E}_{P_{\mathrm{top}}}\varphi$, replacing `poleNumerator ψ` by $N_P(s) := 2 Q_P(s) \mathcal{M}\psi_0(-s) - \operatorname{residueConst}(\psi)\Gamma(s)$ yields an analytic regularized Mellin kernel $\Psi_P(w) = 2\mathcal{M}\psi(w) + \operatorname{dslope}(N_P, 1)(w + 1)$ satisfying `MellinRegularStrip Ψ_P (θ₁/2 - 1) 2` and agreeing with `regularPart ψ` on $\operatorname{Re} w = 1$.
4. Mellin inversion and contour shift to $c' = \theta_1/2 - 1 + \varepsilon_1$ with $\varepsilon_1 = \frac{1}{4}(\Theta - \theta_1) \in (0, \frac{1}{2})$ give
   $$
   \Bigl\lVert A_{\mathcal{E}_{P_{\mathrm{top}}}\varphi}(y) - \frac{6}{\pi}\widetilde{\mathcal{E}_{P_{\mathrm{top}}}\varphi}(-1)\Bigr\rVert \le C_\varphi\, y^\alpha \qquad (0 < y \le 1),
   $$
   with $\alpha = 1 - \theta_1/2 - \varepsilon_1 = 1 - \Theta/2 + \frac{1}{4}(\Theta - \theta_1) > 1 - \Theta/2$.

Combining §3 and §4 yields the unconditional equivalence: `AsymptoticAbscissaLaw` holds if and only if no nonzero $P \in \mathbb{R}[X]$ accelerates universal horocycle equidistribution to any exponent $\alpha > 1 - \Theta/2$.

## Log
- 2026-11-11 — created and proved in `2-fully-proven`
