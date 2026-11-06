# Universal Bilateral Cauchy–Szegő Gram Law and Kronecker Multiplicity Defect of Truncated Resonant Eisenstein States

- **Status:** `2-fully-proven`
- **Target subfolder:** `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ResonantEisensteinCrossZeroGramLaw.lean`

## Theorem Statements

1. **Universal Upper-Half-Strip Cauchy–Szegő Gram Law (`hermitianPairing_resonantState_upper`, `crossZero_angle_law_upper`, `crossZero_cauchySchwarz_residual_upper`):**
   For *any* two upper-strip zeros $\rho_1, \rho_2$ of $\Lambda = \text{reflectedCompletedLambda}$ ($0 < \operatorname{Re}\rho_j < 1$, $0 < \operatorname{Im}\rho_j$) and every truncation height $Y \ge 1$, with $u(\rho) = (\rho - 1)/2$:
   $$\left\langle \Lambda^Y E_{u(\rho_1)},\, \Lambda^Y E_{u(\rho_2)} \right\rangle_{L^2(\mathcal{D})} = \frac{2\,\Lambda(\rho_1 - 1)\,\overline{\Lambda(\rho_2 - 1)}}{2 - \rho_1 - \bar{\rho}_2} \, Y^{1 - \frac{\rho_1 + \bar{\rho}_2}{2}},$$
   and the normalized squared Hermitian inner product satisfies the height- and $\Lambda$-independent identity
   $$\frac{\left|\left\langle \Lambda^Y E_{u(\rho_1)},\, \Lambda^Y E_{u(\rho_2)} \right\rangle_{L^2(\mathcal{D})}\right|^2}{\|\Lambda^Y E_{u(\rho_1)}\|_{L^2(\mathcal{D})}^2 \, \|\Lambda^Y E_{u(\rho_2)}\|_{L^2(\mathcal{D})}^2} = \frac{4(1 - \operatorname{Re}\rho_1)(1 - \operatorname{Re}\rho_2)}{\left|2 - \rho_1 - \bar{\rho}_2\right|^2} = 1 - \left|\frac{\rho_1 - \rho_2}{2 - \rho_1 - \bar{\rho}_2}\right|^2.$$
   In particular, Cauchy–Schwarz is saturated if and only if $\rho_1 = \rho_2$; specializing to $\rho_2 = 1 - \bar{\rho}_1$ recovers the partner angle law $4\operatorname{Re}\rho_1(1 - \operatorname{Re}\rho_1) = 1 - (2\operatorname{Re}\rho_1 - 1)^2$.

2. **Full Bilateral Strip Gram Matrix & Conjugate-Pair Kronecker Multiplicity Defect (`truncatedPairing_diag_resonantState`, `hermitianPairing_resonantState_all`):**
   For *every* pair of strip zeros $\rho_1, \rho_2$ of $\Lambda$ ($0 < \operatorname{Re}\rho_j < 1$, arbitrary signs of $\operatorname{Im}\rho_1, \operatorname{Im}\rho_2 \ne 0$) and every $Y \ge 1$:
   $$\left\langle \Lambda^Y E_{u(\rho_1)},\, \Lambda^Y E_{u(\rho_2)} \right\rangle_{L^2(\mathcal{D})} = \frac{2\,\Lambda(\rho_1 - 1)\,\overline{\Lambda(\rho_2 - 1)}}{2 - \rho_1 - \bar{\rho}_2} \, Y^{1 - \frac{\rho_1 + \bar{\rho}_2}{2}} + \begin{cases} 2\,\Lambda(\rho_1 - 1)\,\Lambda'(\rho_1) & \text{if } \rho_2 = \bar{\rho}_1, \\ 0 & \text{if } \rho_2 \ne \bar{\rho}_1. \end{cases}$$
   Equivalently, at a single strip zero $\rho$, the bilinear self-pairing equals
   $$\int_{\mathcal{D}} \left(\Lambda^Y E_{u(\rho)}\right)^2 d\mu = \left\langle \Lambda^Y E_{u(\rho)},\, \Lambda^Y E_{u(\bar{\rho})} \right\rangle_{L^2(\mathcal{D})} = \frac{\Lambda(\rho - 1)^2}{1 - \rho} \, Y^{1 - \rho} + 2\,\Lambda(\rho - 1)\,\Lambda'(\rho),$$
   whose $Y$-independent constant term $2\,\Lambda(\rho - 1)\,\Lambda'(\rho)$ vanishes if and only if $\Lambda'(\rho) = 0$ (i.e. $\rho$ is a multiple zero of $\zeta$).

3. **Laplace Gram Isometric Representation (`hermitianPairing_resonantState_upper_eq_laplace_integral`, `resonantGramQuadraticForm_upper_eq_laplace_normSq`):**
   For any finite family $S$ of upper-strip zeros of $\Lambda$, complex weights $c : \mathbb{C} \to \mathbb{C}$, and $Y \ge 1$,
   $$\sum_{\rho_1 \in S} \sum_{\rho_2 \in S} \overline{c(\rho_1)}\,c(\rho_2)\,\left\langle \Lambda^Y E_{u(\rho_2)},\, \Lambda^Y E_{u(\rho_1)} \right\rangle_{L^2(\mathcal{D})} = \int_0^\infty \left|\sum_{\rho \in S} c(\rho)\,\Lambda(\rho - 1)\,Y^{\frac{1-\rho}{2}}\,e^{-t\frac{1-\rho}{2}}\right|^2 dt.$$

## Proof Outline

1. For $\operatorname{Im}\rho_1 > 0$ and $\operatorname{Im}\rho_2 > 0$, $u_1 = (\rho_1 - 1)/2 \in \Omega$ and $w_2 = -\bar{u}_2 = (1 - \bar{\rho}_2)/2 \in \Omega$, with $\overline{\Lambda^Y E_{u_2}} = \Lambda^Y E_{w_2}$, $A(u_1) = \Lambda(\rho_1) = 0$, and $B(w_2) = \overline{A(u_2)} = 0$. In `maassSelberg_lineModel` at $(u_1, w_2)$, three of the four terms in `msRight` vanish; since $\operatorname{Im}(u_1 + w_2) = (\operatorname{Im}\rho_1 + \operatorname{Im}\rho_2)/2 > 0$ and $\operatorname{Re}(u_1 - w_2) = (\operatorname{Re}\rho_1 + \operatorname{Re}\rho_2 - 2)/2 < 0$, both $(u_1 + w_2)$ and $(u_1 - w_2)$ are nonzero even when $\rho_1 = \rho_2$. Algebraic identity $|2 - \rho_1 - \bar{\rho}_2|^2 - 4(1 - \operatorname{Re}\rho_1)(1 - \operatorname{Re}\rho_2) = |\rho_1 - \rho_2|^2$ gives the angle and Cauchy–Schwarz residual laws.
2. For $\operatorname{Im}\rho_1 > 0$ and $\operatorname{Im}\rho_2 < 0$, $v_2 = \bar{u}_2 = u(\bar{\rho}_2) \in \Omega$ satisfies $\overline{\Lambda^Y E_{u_2}} = \Lambda^Y E_{v_2}$ and $A(v_2) = \overline{\Lambda(\rho_2)} = 0$. When $\rho_2 \ne \bar{\rho}_1$, $u_1 \ne v_2$ and $(u_1 - v_2)$ cancels from `maassSelberg_lineModel` at $(u_1, v_2)$. When $\rho_2 = \bar{\rho}_1$, $v_2 = u_1$, and `truncatedPairing_diag` evaluates $-msDiag(u_1, Y)/(2u_1) = \frac{\Lambda(\rho_1 - 1)^2}{1 - \rho_1} Y^{1 - \rho_1} + 2\Lambda(\rho_1 - 1)\Lambda'(\rho_1)$. The remaining two quadrants follow by complex conjugation and Schwarz reflection `deriv_reflectedCompletedLambda_conj`.
3. Since $\operatorname{Re}(1 - (\rho_1 + \bar{\rho}_2)/2) > 0$, $\int_0^\infty e^{-t(1 - (\rho_1 + \bar{\rho}_2)/2)}\,dt = \frac{2}{2 - \rho_1 - \bar{\rho}_2}$, and linearity swaps the finite double sum with the integral on $(0, \infty)$.
