# Archimedean Tate Domination

Unconditional resolution of the positive-dimension archimedean Tate domination problem on the window tower $\{W_A\}_{A \ge 0}$ ($H \in C_c^2(\mathbb{R})$, $\operatorname{supp} H \subseteq [-A, 0]$).

## Mathematical Summary

For $H \in W_A$ and real dimension $k \ge 0$, write
- $\mathrm{archGammaForm}(H) = \Omega(0)\|H\|_2^2 + J_\infty(H)$,
- $\mathrm{windowPoleForm}(H) = 2\bigl(\int_{\mathbb{R}} H(u)e^{u/2}\,du\bigr)\bigl(\int_{\mathbb{R}} H(u)e^{-u/2}\,du\bigr)$,
- $\mathrm{archWindowForm}(H) = \mathrm{archGammaForm}(H) + \mathrm{windowPoleForm}(H)$,
- $\mathrm{shiftedPoleForm}_k(H) = 2\bigl(\int_{\mathbb{R}} H(u)e^{(1/2+k)u}\,du\bigr)\bigl(\int_{\mathbb{R}} H(u)e^{-(1/2+k)u}\,du\bigr)$,
- $\mathrm{tatePointCount}(A,H,k) = 2(\tau_H(k) - \|H\|_2^2) = 2\sum_{2 \le n \le \lfloor e^A \rfloor} \frac{J_k(n)}{\sqrt{n}}\int_{\mathbb{R}} H(u)H(u+\log n)\,du$,
- $\mathrm{backwardTateGammaForm}_k(H) = k\,\mathrm{archGammaForm}(H) - 2\int_0^\infty \omega(x)\bigl(\frac{e^{kx}-1}{x}-k\bigr)c_H(x)\,dx$,
- $\mathrm{symTateGammaForm}_k(H) = k\,\mathrm{archGammaForm}(H) - 2\int_0^\infty \omega(x)\bigl(\frac{\sinh(kx)}{x}-k\bigr)c_H(x)\,dx$,

where $c_H(x) = \int_{\mathbb{R}} H(u)H(u+x)\,du$ and $\omega(x) = e^{-x/2}/(1 - e^{-2x})$.

1. **Dimension-zero inheritance (`TheDimensionZeroInheritanceLaw.lean`).**
    Weil's quadratic form satisfies $Q(H) = \mathrm{archWindowForm}(H) - \partial_k\mathrm{tatePointCount}(A,H,k)|_{k=0}$. Sequential domination $\mathrm{tatePointCount}(A,H,\kappa_m) \le a(\kappa_m)$ along any $\kappa_m \downarrow 0$ with $a(0)=0$ and $a'(0)=\mathrm{archWindowForm}(H)$ forces $Q(H) \ge 0$ (`weilQuad_nonneg_of_seq_tateDomination`), hence `RiemannHypothesis` across all windows (`riemannHypothesis_of_local_archimedeanTateDomination`). Jordan's totients satisfy the two-sided Bombieri–Selberg envelope
   $$\frac{k^2}{2}\Lambda_2(n) \le J_k(n) - k\Lambda(n) \le k^2\bigl(J_1(n) - \Lambda(n)\bigr) \qquad (n \ge 2,\ 0 \le k \le 1)$$
   (`jordanTotient_sub_linear_ge_selberg`, `jordanTotient_sub_linear_le_sq`).

2. **Tilted Tate-Gamma families (`TateGammaFamilies.lean`).**
   Both $\mathrm{backwardTateGammaForm}_k(H)$ ($\Gamma_{\mathbb{R}}(s-k)/\Gamma_{\mathbb{R}}(s)$) and $\mathrm{symTateGammaForm}_k(H)$ vanish at $k = 0$, have two-sided $k = 0$ derivative $\mathrm{archGammaForm}(H)$ (`hasDerivAt_backwardTateGammaForm_zero`, `hasDerivAt_symTateGammaForm_zero`), satisfy $\le k\,\mathrm{archGammaForm}(H)$ on nonnegative profiles for $k \ge 0$, and satisfy $|A_k^\Gamma(H) - k\,\mathrm{archGammaForm}(H)| \le 18 k^2 \|H\|_2^2$ on $|k| \le 1/4$.

3. **Unconditional domination past the first prime fold $\log 2$ (`FirstFoldStageDomination.lean`).**
   Centering $H \in W_A$ into $[-A/2, A/2]$ transports the enlarged aperture floor to $Q(H) \ge \frac{1}{8000}\|H\|_2^2$ for all $0 \le A \le 2\,\mathrm{enlargedWeilFloorAperture}$, with
   $$\log 2 < \frac{181}{250} < 2\,\mathrm{enlargedWeilFloorAperture} < 1 < \log 3$$
   (`firstFoldSubstage_bounds`, `weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture`). Across $[0, 2\,\mathrm{enlargedWeilFloorAperture}]$ — including the first-fold sub-stage $[\log 2, 2\,\mathrm{enlargedWeilFloorAperture}]$ where $\mathrm{tatePointCount}(A,H,k) = \sqrt{2}(2^k-1)\int_{\mathbb{R}} H(u)H(u+\log 2)\,du$ — both $\mathrm{backwardTateGammaForm}_k(H) + k\,\mathrm{windowPoleForm}(H)$ and $\mathrm{symTateGammaForm}_k(H) + k\,\mathrm{windowPoleForm}(H)$ dominate $\mathrm{tatePointCount}(A,H,k)$ unconditionally for $0 \le k \le 1/160000$ (`firstFoldStage_backwardTateGammaDomination`, `firstFoldStage_symTateGammaDomination`, `firstFoldSubstage_explicit_primeTwo_domination`).

4. **Unshifted global impossibility and doubly-exponential horizon collapse (`UnshiftedImpossibilityAndHorizonCollapse.lean`).**
   - Composite Weil-cone obstruction: $J_k(6) = (2^k-1)(3^k-1) > 0 = \Lambda(6)$ refutes degree-$\alpha$ Weil positivity of $2J_k$ for all $k, \alpha > 0$ (`not_weilPositiveDegree_two_mul_jordanTotient`).
   - Unshifted blowup: on smooth harmonic plateaus $H_A(u) \approx e^{u/2}$ on $[-A, 0]$, $\mathrm{archGammaForm}(H_A) = O(1)$ and $|\mathrm{windowPoleForm}(H_A)| \le 2A^2$ while $\mathrm{tatePointCount}(A,H_A,k) \gtrsim e^{kA}$, refuting $\alpha\,\mathrm{archGammaForm} + \beta\,\mathrm{windowPoleForm}$ across all windows for every $k > 0$ and $\alpha, \beta \in \mathbb{R}$ (`not_forall_window_domination_archGamma_pole`).
   - Horizon collapse: on translated Riemann-kernel truncations `windowRiemannKernel A` ($\ge 0$), Selberg's $\Lambda_2(2) = (\log 2)^2$ forces a uniform $c_* k^2$ excess over the $1$-jet while $Q(H_A) \le C_0 \exp(-e^{A-2})$, forcing $k_0(A) \le C_* \exp(-e^{A-2})$ and refuting any uniform horizon $k_0 > 0$ (`exists_horizon_le_doubleExp`, `not_exists_uniform_horizon_backwardTateGamma`, `not_exists_uniform_horizon_symTateGamma`).

5. **Shifted-pole residue pinching and global no-go across all $\varphi \in \mathbb{R}$ (`ShiftedPoleResiduePinchingAndNoGo.lean`).**
   - 1D Dirichlet hyperbola asymptotic: for $0 < k < 1$ and $|H(w)|, |H'(w)| \le K e^{w/2}$,
     $$\bigl|\mathrm{tatePointCount}(A,H,k) - \zeta(1+k)^{-1}\mathrm{shiftedPoleForm}_k(H)\bigr| \le C_k K^2 (A+1)^2$$
     (`abs_tatePointCount_sub_eulerProduct_shiftedPoleForm_le`).
   - Two-sided residue pinching: testing on positive and negative wide harmonic plateaus forces any dominating combination $\alpha\,\mathrm{archGammaForm} + \beta\,\mathrm{windowPoleForm} + \varphi\,\mathrm{shiftedPoleForm}_k$ to satisfy $\varphi = \zeta(1+k)^{-1} < k$ (`shiftedPole_weight_pinched_eq_eulerProduct`, `eulerProductPoleWeight_lt_self`).
   - Refutation on Riemann's kernel: log-convexity of $\Gamma$ on $[3/2, 2]$ and $\zeta(1+k) < 1/k + 7/8$ give $4\xi(1+k)^2 < k\zeta(1+k)$ on $(0, 1]$ (`four_mul_riemannPhiTransform_sq_lt_mul_zeta`), refuting every $\varphi \le \zeta(1+k)^{-1}$ on `windowRiemannKernel A` and hence refuting all $\varphi \in \mathbb{R}$ (`not_exists_shiftedPole_weight_domination_linear`, `not_exists_shiftedPole_weight_domination_backwardTateGamma`, `not_exists_shiftedPole_weight_domination_symTateGamma`).

## Module Map

| File | Main declarations |
| --- | --- |
| `TheDimensionZeroInheritanceLaw.lean` | `weilQuad_nonneg_of_seq_tateDomination`, `riemannHypothesis_of_local_archimedeanTateDomination`, `jordanTotient_sub_linear_ge_selberg`, `jordanTotient_sub_linear_le_sq`, `linearArchimedeanDomination_of_weilFloor` |
| `TateGammaFamilies.lean` | `backwardTateGammaForm`, `symTateGammaForm`, `hasDerivAt_backwardTateGammaForm_zero`, `hasDerivAt_symTateGammaForm_zero`, `abs_backwardTateGammaForm_sub_linear_le`, `abs_symTateGammaForm_sub_linear_le` |
| `UnshiftedImpossibilityAndHorizonCollapse.lean` | `jordanTotient_six`, `not_weilPositiveDegree_two_mul_jordanTotient`, `not_forall_window_domination_archGamma_pole`, `exists_horizon_le_doubleExp`, `not_exists_uniform_horizon_backwardTateGamma`, `not_exists_uniform_horizon_symTateGamma` |
| `ShiftedPoleResiduePinchingAndNoGo.lean` | `shiftedPoleForm`, `hasDerivAt_mul_shiftedPoleForm_zero`, `eulerProductPoleWeight`, `four_mul_riemannPhiTransform_sq_lt_mul_zeta`, `abs_tatePointCount_sub_eulerProduct_shiftedPoleForm_le`, `shiftedPole_weight_pinched_eq_eulerProduct`, `not_exists_shiftedPole_weight_domination_backwardTateGamma`, `not_exists_shiftedPole_weight_domination_symTateGamma` |
| `FirstFoldStageDomination.lean` | `firstFoldSubstage_bounds`, `weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture`, `firstFoldStage_backwardTateGammaDomination`, `firstFoldStage_symTateGammaDomination`, `firstFoldSubstage_explicit_primeTwo_domination`, `archimedean_tate_domination_complete_solution` |
