# The Optimal Horocycle Equidistribution Exponent $1 - \Theta/2$ and the Euler-Operator Characterization of the Asymptotic Abscissa Law

- **ID:** bhr-optimal-horocycle-exponent-and-euler-annihilators
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1011/fable.md §5.3 · formal/GaloisForLFunctions/BlackHoleRingdown/TheHorocycleRateIsTheZeroFreeRegion.lean
- **Lean Module:** `GaloisForLFunctions.BlackHoleRingdown.TheOptimalHorocycleExponentAndEulerAnnihilators`
- **Lean Declarations:**
  - `GaloisForLFunctions.BlackHoleRingdown.horocycle_rate_zetaZeroAbscissa`
  - `GaloisForLFunctions.BlackHoleRingdown.cusp_energy_rate_zetaZeroAbscissa`
  - `GaloisForLFunctions.BlackHoleRingdown.sSup_universalHorocycleExponents`
  - `GaloisForLFunctions.BlackHoleRingdown.eulerPolyR`
  - `GaloisForLFunctions.BlackHoleRingdown.re_le_or_eval_eq_zero_of_eulerPoly_horocycle_rate`
  - `GaloisForLFunctions.BlackHoleRingdown.not_eulerPoly_horocycle_rate_gt_three_quarters`
  - `GaloisForLFunctions.BlackHoleRingdown.exists_eulerPoly_horocycle_rate_of_lt_one_sub_half_zetaAsymptoticAbscissa`
  - `GaloisForLFunctions.BlackHoleRingdown.sSup_eulerFilteredHorocycleExponents`
  - `GaloisForLFunctions.BlackHoleRingdown.zerosApproachLine_iff_eulerPoly_horocycle_rate`
  - `GaloisForLFunctions.BlackHoleRingdown.asymptoticAbscissaLaw_iff_no_eulerPoly_horocycle_acceleration`
- **Statement:** Unconditionally, the supremum of universal horocycle equidistribution exponents for smooth compactly supported pseudo-Eisenstein profiles on $(1, \infty)$ equals $1 - \Theta/2$ ($\Theta = \operatorname{zetaZeroAbscissa}$), the supremum of polynomial-Euler-filtered universal horocycle exponents equals $1 - \Theta_\infty/2$ ($\Theta_\infty = \operatorname{zetaAsymptoticAbscissa}$), `ZerosApproachLine` ($\Theta_\infty = 1/2$) holds iff every exponent $< 3/4$ is attained via some nonzero $P(y\frac{d}{dy}) \in \mathbb{R}[X]$, and `AsymptoticAbscissaLaw` ($\Theta_\infty = \Theta$) holds iff no nonzero $P(y\frac{d}{dy}) \in \mathbb{R}[X]$ accelerates universal horocycle equidistribution strictly past $1 - \Theta/2$.

## Goal
Extend Zagier's horocycle equidistribution theorem (`RH` $\iff$ universal rate $y^{3/4 - \varepsilon}$) to the unconditional global zero abscissa $\Theta = \operatorname{zetaZeroAbscissa}$ and establish an exact spectral-dynamical equivalence between `AsymptoticAbscissaLaw` and non-accelerability of horocycle equidistribution by nonzero polynomial Euler differential operators.

## Gates
- [x] 0 → 1  in-progress: exact coupling between `norm_horocycleMean_sub_le_of_zeroFree`, `exists_zeta_lower_bound_subpolynomial_of_zeroFree_above`, and meromorphic normal forms of polynomial-twisted scattering ratios
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof `[PROVED HERE]`
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.BlackHoleRingdown.TheOptimalHorocycleExponentAndEulerAnnihilators`, `lake --old env lean` green, `#print axioms` `[propext, Classical.choice, Quot.sound]`

## Paper Proof `[PROVED HERE]`

### 1. Sharp unconditional horocycle rate $1 - \Theta/2$ (pseudo-Eisenstein and cusp-energy channels)
Let $\Theta = \operatorname{zetaZeroAbscissa} \in [\frac{1}{2}, 1]$.
- **Forward rate (`horocycle_rate_zetaZeroAbscissa`, `cusp_energy_rate_zetaZeroAbscissa`):** By `riemannZeta_ne_zero_of_zetaZeroAbscissa_lt` and `xi_eq_zero_iff_riemannZeta_eq_zero`, $\xi(z) \ne 0$ for all $\operatorname{Re} z > \Theta$. By `exists_invZeta_shift_data_of_zeroFree` at $\Theta$ with $\varepsilon_0 = 1$, for every $\delta > 0$ and $d \in \mathbb{R}$ there exists $K_b \ge 0$ such that $\lVert\zeta(z)^{-1}\rVert \le 2 K_b |\operatorname{Im} z|$ on $\Theta + \min(\delta, \frac{1}{2}) \le \operatorname{Re} z \le d$, $|\operatorname{Im} z| \ge 2$. Substituting these two unconditional inputs into `norm_horocycleMean_sub_le_of_zeroFree` and `norm_mass_sub_le_of_zeroFree` yields, for every $\varepsilon \in (0, 1)$ and $\varphi \in C_c^\infty(1, \infty)$ (respectively $\varepsilon \in (0, \frac{1}{2})$ and Hecke–Maass cusp form $g$),
  $$
  \Bigl\lVert A_\varphi(y) - \frac{6}{\pi}\widetilde{\varphi}(-1)\Bigr\rVert \le C_{\varphi,\varepsilon}\, y^{1 - \Theta/2 - \varepsilon}, \qquad
  \Bigl| m_g(y) - \frac{3}{\pi}\lVert g\rVert^2 \Bigr| \le C_{g,\varepsilon}\, y^{1 - \Theta/2 - \varepsilon} \qquad (0 < y \le 1).
  $$
- **Optimality (`not_horocycle_rate_gt_one_sub_half_zetaZeroAbscissa`, `sSup_universalHorocycleExponents`):** If universal pseudo-Eisenstein equidistribution held at exponent $\alpha > 1 - \Theta/2$, then $2 - 2\alpha < \Theta$. By `exists_zetaZero_lt_re`, there exists $\rho \in \mathbb{C}$ with $\zeta(\rho) = 0$ and $\operatorname{Re}\rho > \max(2 - 2\alpha, 0)$. Zagier's converse (`re_le_of_horocycle_rate`) gives $\operatorname{Re}\rho \le 2 - 2\alpha$, a contradiction. Thus `universalHorocycleExponents` has exact supremum $1 - \Theta/2$.

### 2. Polynomial Euler differential operators on $C_c^\infty(1, \infty)$
For $k \in \mathbb{N}$ and $\varphi : \mathbb{R} \to \mathbb{R}$, define the real Euler iterates $D^0 \varphi = \varphi$, $D^{k+1}\varphi(u) = u (D^k\varphi)'(u)$, and for $P = \sum_{k=0}^d a_k X^k \in \mathbb{R}[X]$ set $(\mathcal{E}_P \varphi)(u) := \sum_{k=0}^d a_k (D^k \varphi)(u)$.
1. If $\varphi \in C_c^\infty(\mathbb{R})$ with $\operatorname{tsupport}\varphi \subseteq (1, \infty)$, then $\mathcal{E}_P\varphi \in C_c^\infty(\mathbb{R})$ with $\operatorname{tsupport}(\mathcal{E}_P\varphi) \subseteq \operatorname{tsupport}\varphi \subseteq (1, \infty)$.
2. Complexifying $\psi_0(u) = (\varphi(u) : \mathbb{C})$ and $P_{\mathbb{C}} = P.\operatorname{map}(\mathbb{R} \to \mathbb{C})$, $(\mathcal{E}_P\varphi(u) : \mathbb{C}) = \sum_{k \in P.\mathrm{support}} (a_k : \mathbb{C})\, \operatorname{eulerIter}_k \psi_0(u)$.
3. If `IsTest ψ₀ a b` ($1 < a \le b$), then `IsTest (fun u => (eulerPolyR P φ u : ℂ)) a b`, and by `mellin_eulerIter` at $-s$,
   $$
   \mathcal{M}[\mathcal{E}_P\varphi](-s) = \sum_{k \in P.\mathrm{support}} a_k s^k \mathcal{M}\psi_0(-s) = P_{\mathbb{C}}(s)\, \mathcal{M}\psi_0(-s) \qquad (s \in \mathbb{C}).
   $$

### 3. Converse acceleration theorem (`re_le_or_eval_eq_zero_of_eulerPoly_horocycle_rate`, `not_eulerPoly_horocycle_rate_gt_three_quarters`)
Suppose $P \in \mathbb{R}[X]$ is nonzero ($P \ne 0$) and for some $\alpha \in \mathbb{R}$, every $\varphi \in C_c^\infty(1, \infty)$ satisfies $\lVert A_{\mathcal{E}_P\varphi}(y) - c_\varphi\rVert \le C_\varphi y^\alpha$ on $(0, 1]$.
Let $\rho \in \mathbb{C}$ satisfy $0 < \operatorname{Re}\rho < 1$, $\zeta(\rho) = 0$, and $\operatorname{Re}\rho > 2 - 2\alpha$. Since $\zeta$ has no real zeros in $(0, 1)$, $\operatorname{Im}\rho \ne 0$; let $\rho' \in \{\rho, \overline{\rho}\}$ be the conjugate with $\operatorname{Im}\rho' > 0$, and set $s_0 = \rho'/2 \in \operatorname{quarterPlane}(\alpha)$. Then $\operatorname{msA}(s_0 - \frac{1}{2}) = 0$ and $\operatorname{msB}(s_0 - \frac{1}{2}) \ne 0$.
Applying `msB_mul_mellin_eq_zero_of_rate` to $\mathcal{E}_P\varphi$ yields
$$
\operatorname{msB}(s_0 - \tfrac{1}{2}) \cdot P_{\mathbb{C}}(s_0) \cdot \mathcal{M}[\varphi](-s_0) = 0 \qquad \forall \varphi \in C_c^\infty(1, \infty).
$$
If $P_{\mathbb{C}}(s_0) \ne 0$, then $\mathcal{M}[\varphi](-s_0) = 0$ for every $\varphi \in C_c^\infty(1, \infty)$, contradicting `isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero` on $y \mapsto y^{-s_0 - 1} \ne 0$. Hence $P_{\mathbb{C}}(\rho'/2) = 0$, and since $P$ has real coefficients, $P_{\mathbb{C}}(\rho/2) = 0$.
1. **Universal $3/4$ ceiling:** If $\alpha > 3/4$, then $2 - 2\alpha < 1/2$. By Hardy's theorem (`exists_Xi_zero_gt`), $\zeta$ has infinitely many critical-line zeros $\rho_n = \frac{1}{2} + i\gamma_n$, each satisfying $\operatorname{Re}\rho_n = \frac{1}{2} > 2 - 2\alpha$, forcing $P_{\mathbb{C}}(\rho_n/2) = 0$ on an infinite set and contradicting $P \ne 0$.
2. **Asymptotic abscissa bound:** Since $P_{\mathbb{C}} \ne 0$ has finitely many roots, $\{\rho \mid \xi(\rho) = 0 \text{ and } \operatorname{Re}\rho > \max(1/2, 2 - 2\alpha)\}$ is finite, so $\Theta_\infty = \operatorname{zetaAsymptoticAbscissa} \le \max(1/2, 2 - 2\alpha)$, hence $\alpha \le 1 - \Theta_\infty/2$.

### 4. Forward top-annihilator theorem (`exists_eulerPoly_horocycle_rate_of_lt_one_sub_half_zetaAsymptoticAbscissa`)
Let $\alpha < 1 - \Theta_\infty/2$ and choose $\theta_0 \in (\Theta_\infty, \min(1, 2 - 2\alpha))$ with $\frac{1}{2} \le \theta_0 < 1$ (if $\Theta_\infty = 1$, no $\alpha < 1/2$ exceeds the unconditional rate `horocycle_rate_zetaZeroAbscissa` evaluated at $P = 1$). Since $\theta_0 > \Theta_\infty$, $F_\xi = \{z \in \mathbb{C} \mid \theta_0 < \operatorname{Re} z \text{ and } \xi(z) = 0\}$ is finite (`zetaAsymptoticAbscissaSet`), so $F = F_\xi / 2$ is finite, conjugate-symmetric, and contains no real points. For each $s \in F^+ = \{s \in F \mid \operatorname{Im} s > 0\}$, let $m(s) \in \mathbb{N}$ be the analytic order of $z \mapsto \xi(2z)$ at $s$, and set
$$
P_{\mathrm{top}}(X) := \prod_{s \in F^+} \bigl(X^2 - 2(\operatorname{Re} s) X + \lvert s\rvert^2\bigr)^{m(s)} \in \mathbb{R}[X].
$$
$P_{\mathrm{top}}$ is monic ($P_{\mathrm{top}} \ne 0$), and over $\mathbb{C}$ its root multiplicity at every $s \in F$ is at least $m(s)$. Hence $Q_P := \operatorname{toMeromorphicNFOn}(z \mapsto \operatorname{scatterQ}(z)\, P_{\mathrm{top},\mathbb{C}}(z), \operatorname{univ})$ is analytic on $\{\operatorname{Re} s > \theta_0/2\}$ and agrees pointwise with $\operatorname{scatterQ}(s)\, P_{\mathrm{top},\mathbb{C}}(s)$ wherever $\xi(2s) \ne 0$.
Outside the bounded ordinate box $|\operatorname{Im} z| \le T_0$ ($T_0 = \max_{s \in F} 2|\operatorname{Im} s| + 1$), $\zeta(z) \ne 0$ on $\operatorname{Re} z > \theta_0$, so `exists_zeta_lower_bound_subpolynomial_of_zeroFree_above` and `exists_norm_scatterQ_le` give polynomial vertical growth of $Q_P$ on every closed strip in $\operatorname{Re} s > \theta_0/2$. Consequently, the regularized Mellin kernel $\Psi_P(w) = 2\mathcal{M}[\mathcal{E}_{P_{\mathrm{top}}}\varphi](w) + \operatorname{dslope}(N_P, 1)(w + 1)$ ($N_P(s) = 2 Q_P(s)\mathcal{M}\varphi(-s) - \operatorname{residueConst}(\mathcal{E}_{P_{\mathrm{top}}}\varphi)\Gamma(s)$) satisfies `MellinRegularStrip Ψ_P (θ₀/2 - 1) 2` and agrees with `regularPart (eulerPolyR P_top φ)` on $\operatorname{Re} w = 1$. Contour shifting to $c' = -\alpha$ yields universal equidistribution at exponent $\alpha$.

Combining §3 and §4 gives `sSup eulerFilteredHorocycleExponents = 1 - Θ_∞/2`, `ZerosApproachLine` $\iff$ every $\alpha < 3/4$ lies in `eulerFilteredHorocycleExponents`, and `AsymptoticAbscissaLaw` $\iff$ no nonzero $P \in \mathbb{R}[X]$ achieves rate $\alpha > 1 - \Theta/2$.

## Log
- 2026-11-11 — created, proved, and formalized in `GaloisForLFunctions.BlackHoleRingdown.TheOptimalHorocycleExponentAndEulerAnnihilators`
