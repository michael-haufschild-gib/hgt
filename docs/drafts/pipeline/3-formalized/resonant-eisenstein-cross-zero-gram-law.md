# Universal bilateral Cauchy–Szegő Gram law and Kronecker multiplicity defect of truncated resonant Eisenstein states

- **ID:** resonant-eisenstein-cross-zero-gram-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For any two strip zeros $\rho_1, \rho_2$ of $\Lambda = \mathrm{reflectedCompletedLambda}$ ($0 < \operatorname{Re}\rho_j < 1$) and every truncation height $Y \ge 1$, the $L^2(\mathcal{D})$ Hermitian inner product of the truncated resonant states $\Lambda^Y E_{u(\rho_j)}$ ($u(\rho) = (\rho - 1)/2$) equals $\frac{2\Lambda(\rho_1 - 1)\overline{\Lambda(\rho_2 - 1)}}{2 - \rho_1 - \bar{\rho}_2} Y^{1 - (\rho_1 + \bar{\rho}_2)/2} + 2\Lambda(\rho_1 - 1)\Lambda'(\rho_1)\delta_{\rho_2, \bar{\rho}_1}$; in the upper strip, the normalized squared cosine is $\frac{4(1 - \operatorname{Re}\rho_1)(1 - \operatorname{Re}\rho_2)}{|2 - \rho_1 - \bar{\rho}_2|^2} = 1 - \big|\frac{\rho_1 - \rho_2}{2 - \rho_1 - \bar{\rho}_2}\big|^2$ (saturating Cauchy–Schwarz iff $\rho_1 = \rho_2$), and finite upper-strip Gram quadratic forms are isometric to $L^2((0, \infty), dt)$ Laplace exponential wavepackets.

## Paper proof

1. **Upper-strip Cauchy–Szegő Gram law.** Every zero $\rho$ of $\Lambda$ in $0 < \operatorname{Re}\rho < 1$ satisfies $\operatorname{Im}\rho \ne 0$ (`riemannZeta_real_strip_ne_zero`). For $\operatorname{Im}\rho_1, \operatorname{Im}\rho_2 > 0$, $u_1 = (\rho_1 - 1)/2$ and $w_2 = -\bar{u}_2 = (1 - \bar{\rho}_2)/2$ lie in `eisensteinLineDomain` with $\overline{\Lambda^Y E_{u_2}} = \Lambda^Y E_{w_2}$, $A(u_1) = \Lambda(\rho_1) = 0$, and $B(w_2) = \overline{A(u_2)} = 0$. In `maassSelberg_lineModel` at $(u_1, w_2)$, three of the four terms in `msRight` vanish and $u_1 + w_2 \ne 0$, $u_1 - w_2 \ne 0$, yielding the rational Cauchy–Szegő kernel. The identity $|2 - \rho_1 - \bar{\rho}_2|^2 - 4(1 - \operatorname{Re}\rho_1)(1 - \operatorname{Re}\rho_2) = |\rho_1 - \rho_2|^2$ gives the $Y$-independent angle law, strict Cauchy–Schwarz non-collinearity for $\rho_1 \ne \rho_2$, and recovery of $4\operatorname{Re}\rho_1(1 - \operatorname{Re}\rho_1)$ at $\rho_2 = 1 - \bar{\rho}_1$.

2. **Bilateral strip Gram matrix and Kronecker multiplicity defect.** For $\operatorname{Im}\rho_1 > 0$ and $\operatorname{Im}\rho_2 < 0$, $v_2 = \bar{u}_2 = u(\bar{\rho}_2)$ satisfies $\overline{\Lambda^Y E_{u_2}} = \Lambda^Y E_{v_2}$. When $\rho_2 \ne \bar{\rho}_1$, $u_1 \ne v_2$ cancels in `maassSelberg_lineModel`; when $\rho_2 = \bar{\rho}_1$, `truncatedPairing_diag` adds the L'Hôpital derivative residue $2\Lambda(\rho_1 - 1)\Lambda'(\rho_1)$, which vanishes iff $\Lambda'(\rho_1) = 0$ since $\Lambda(\rho_1 - 1) \ne 0$. Simultaneous conjugation extends the identity to $\operatorname{Im}\rho_1 < 0$.

3. **Laplace Gram isometry.** Since $\operatorname{Re}(1 - (\rho_2 + \bar{\rho}_1)/2) > 0$, $\int_0^\infty e^{-t(1 - (\rho_2 + \bar{\rho}_1)/2)}\,dt = \frac{2}{2 - \rho_2 - \bar{\rho}_1}$, identifying the $S \times S$ Gram form with $\int_0^\infty \|\mathrm{resonantLaplacePacket}\,Y\,S\,c\,t\|^2\,dt$.

## Lean

Module `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ResonantEisensteinCrossZeroGramLaw.lean` (wired in `ArithmeticCorrespondencePositivity.lean`):
- `im_ne_zero_of_reflectedCompletedLambda_strip_zero`
- `hermitianPairing_resonantState_upper`
- `norm_sq_two_sub_add_conj`
- `crossZero_angle_law_upper`
- `crossZero_cauchySchwarz_residual_upper`
- `crossZero_saturation_upper_iff`
- `crossZero_angle_coeff_partner`
- `truncatedPairing_diag_resonantState`
- `bilinearDiagConstant_eq_zero_iff_deriv_eq_zero`
- `hermitianPairing_resonantState_all`
- `resonantLaplacePacket`
- `hermitianPairing_resonantState_upper_eq_laplace_integral`
- `resonantGramQuadraticForm_upper_eq_laplace_normSq`

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  compiles with `lake --old env lean`
