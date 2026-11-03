# Archimedean Tate domination: first-fold positivity, horizon collapse, and shifted-pole residue pinching

- **ID:** archimedean-tate-domination-dichotomy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0211/obstacles-summary.md` §2.8
- **Statement:** No window-independent archimedean Tate family built from the Gamma factor and the pole (with unshifted pole, separate Gamma/pole weights, Esscher-tilted or symmetrized Tate-Gamma kernel, or Tate-shifted pole with any real weight) dominates the Jordan point counts $2(\tau_H(k)-\|H\|_2^2)$ across all windows $W_A$ on any uniform horizon $0 < k \le k_0$; unconditionally, domination holds past the first prime fold $\log 2$ on $[0, 2\,\mathrm{enlargedWeilFloorAperture}]$, while along the tower any window-local horizon collapses doubly exponentially and any shifted-pole weight is uniquely pinched to $1/\zeta(1+k)$ and refuted on Riemann's radical kernel.

## Goal

Settle `obstacles-summary.md` §2.8 unconditionally in both directions: establish dimension-zero descent, coercive window domination past the first fold $\log 2$, doubly-exponential collapse of the positivity horizon from Selberg's second jet $\Lambda_2$, and global impossibility at every $0 < k \le 1/4$ (and $0 < k < 1$ for linear Gamma plus shifted pole) via Möbius–Euler residue pinching and log-convexity of $\Gamma$.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions.ArchimedeanTateDomination` (`archimedean_tate_domination_complete_solution` and component modules below), `lake --old env lean` green, `#print axioms` PASS (`[propext, Classical.choice, Quot.sound]`)

## Exact decomposition and formalized theorems

For $A \ge 0$ and $H \in W_A$ (`IsWindowTest A H`), write
$$
\begin{aligned}
\mathrm{archGammaForm}(H) &= \Omega(0)\int_{\mathbb{R}} H(u)^2\,du + J_\infty(H),\\
\mathrm{windowPoleForm}(H) &= \tfrac{1}{2}\langle c,H\rangle^2 - \tfrac{1}{2}\langle s,H\rangle^2 = 2\Bigl(\int_{\mathbb{R}} H(u)e^{u/2}\,du\Bigr)\Bigl(\int_{\mathbb{R}} H(u)e^{-u/2}\,du\Bigr),\\
\mathrm{archWindowForm}(H) &= \mathrm{archGammaForm}(H) + \mathrm{windowPoleForm}(H),\\
\mathrm{tatePointCount}(A,H,k) &= 2\bigl(\tau_H(k) - \|H\|_2^2\bigr) = 2\sum_{2 \le n \le \lfloor e^A\rfloor} \frac{J_k(n)}{\sqrt{n}}\int_{\mathbb{R}} H(u)H(u+\log n)\,du,\\
\mathrm{shiftedPoleForm}_k(H) &= 2\Bigl(\int_{\mathbb{R}} H(u)e^{(1/2+k)u}\,du\Bigr)\Bigl(\int_{\mathbb{R}} H(u)e^{-(1/2+k)u}\,du\Bigr),\\
\mathrm{backwardTateGammaForm}_k(H) &= k\,\mathrm{archGammaForm}(H) - 2\int_0^\infty \omega(x)\Bigl(\frac{e^{kx}-1}{x}-k\Bigr)\Bigl(\int_{\mathbb{R}} H(u)H(u+x)\,du\Bigr)dx,\\
\mathrm{symTateGammaForm}_k(H) &= k\,\mathrm{archGammaForm}(H) - 2\int_0^\infty \omega(x)\Bigl(\frac{\sinh(kx)}{x}-k\Bigr)\Bigl(\int_{\mathbb{R}} H(u)H(u+x)\,du\Bigr)dx.
\end{aligned}
$$

1. **Dimension-zero inheritance and Bombieri–Selberg envelope (`TheDimensionZeroInheritanceLaw.lean`).**
   - `weilQuad_eq_archWindowForm_sub_deriv_tatePointCount`, `weilQuad_nonneg_of_seq_tateDomination`, `weilQuad_nonneg_of_local_tateDomination`, `riemannHypothesis_of_local_archimedeanTateDomination`: sequential domination along any $\kappa_m \downarrow 0$ with $a(0)=0$ and $a'(0)=\mathrm{archWindowForm}(H)$ forces $Q(H) \ge 0$, hence `RiemannHypothesis` across all windows.
   - `jordanTotient_sub_linear_ge_selberg`, `jordanTotient_sub_linear_le_sq`: for $n \ge 2$, $\frac{k^2}{2}\Lambda_2(n) \le J_k(n) - k\Lambda(n)$ for all $k \ge 0$, and $J_k(n) - k\Lambda(n) \le k^2(J_1(n) - \Lambda(n))$ for $0 \le k \le 1$.
   - `linearArchimedeanDomination_of_weilFloor`: on any window $W_A$ with $Q(H) \ge \mu\|H\|_2^2$, $\mathrm{tatePointCount}(A,H,k) \le k\,\mathrm{archWindowForm}(H)$ for $0 \le k \le \min(1, \mu / (C_A + 1))$.

2. **Tilted Tate-Gamma families (`TateGammaFamilies.lean`) and unconditional domination past $\log 2$ (`FirstFoldStageDomination.lean`).**
   - `hasDerivAt_backwardTateGammaForm_zero`, `hasDerivAt_symTateGammaForm_zero`, `backwardTateGammaForm_le_mul_archGammaForm_of_nonneg`, `symTateGammaForm_le_mul_archGammaForm_of_nonneg`, `abs_backwardTateGammaForm_sub_linear_le`, `abs_symTateGammaForm_sub_linear_le`: two-sided $k=0$ derivatives equal to $\mathrm{archGammaForm}(H)$, upper comparison $\le k\,\mathrm{archGammaForm}(H)$ on $H \ge 0$, and $18 k^2 \|H\|_2^2$ remainder bounds on $|k| \le 1/4$.
   - `firstFoldSubstage_bounds`, `weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture`: $\log 2 < \frac{181}{250} < 2\,\mathrm{enlargedWeilFloorAperture} < 1 < \log 3$ and $Q(H) \ge \frac{1}{8000}\|H\|_2^2$ for all $0 \le A \le 2\,\mathrm{enlargedWeilFloorAperture}$.
   - `firstFoldStage_linearDomination` ($0 \le k \le 1/16000$), `firstFoldStage_backwardTateGammaDomination`, `firstFoldStage_symTateGammaDomination`, `firstFoldSubstage_explicit_primeTwo_domination` ($0 \le k \le 1/160000$): unconditional domination across $[0, 2\,\mathrm{enlargedWeilFloorAperture}]$, including the first-fold sub-stage $[\log 2, 2\,\mathrm{enlargedWeilFloorAperture}]$ where $\mathrm{tatePointCount}(A,H,k) = \sqrt{2}(2^k-1)\int_{\mathbb{R}} H(u)H(u+\log 2)\,du$.

3. **Unshifted impossibility and doubly-exponential horizon collapse (`UnshiftedImpossibilityAndHorizonCollapse.lean`).**
   - `jordanTotient_six`, `not_weilPositiveDegree_two_mul_jordanTotient`: $J_k(6) = (2^k-1)(3^k-1) > 0 = \Lambda(6)$ refutes degree-$\alpha$ Weil positivity of $2J_k$ for all $k, \alpha > 0$.
   - `not_forall_window_domination_archGamma_pole`: on `harmonicPlateauTest A`, exponential point-count growth against $O(1)$ Gamma energy and $O(A^2)$ unshifted pole growth refutes $\alpha\,\mathrm{archGammaForm} + \beta\,\mathrm{windowPoleForm}$ across all windows for every $k > 0$ and $\alpha, \beta \in \mathbb{R}$.
   - `exists_horizon_le_doubleExp`, `not_exists_uniform_horizon_linearArchimedean`, `not_exists_uniform_horizon_backwardTateGamma`, `not_exists_uniform_horizon_symTateGamma`: on `windowRiemannKernel A` ($\ge 0$), Selberg's $\Lambda_2(2) = (\log 2)^2$ forces a uniform $c_* k^2$ excess over the $1$-jet while $Q(H_A) \le C_0 \exp(-e^{A-2})$, forcing $k_0(A) \le C_* \exp(-e^{A-2})$ and refuting any uniform horizon $k_0 > 0$.

4. **Shifted-pole residue pinching $\varphi = 1/\zeta(1+k)$ and global no-go (`ShiftedPoleResiduePinchingAndNoGo.lean`).**
   - `eulerProductPoleWeight_mul_zeta_eq_one`, `eulerProductPoleWeight_lt_self`, `abs_tatePointCount_sub_eulerProduct_shiftedPoleForm_le`: for $0 < k < 1$ and $|H(w)|, |H'(w)| \le K e^{w/2}$, $|\mathrm{tatePointCount}(A,H,k) - \zeta(1+k)^{-1}\mathrm{shiftedPoleForm}_k(H)| \le C_k K^2 (A+1)^2$.
   - `shiftedPole_weight_pinched_eq_eulerProduct`, `shiftedPole_weight_pinched_backwardTateGamma`, `shiftedPole_weight_pinched_symTateGamma`: testing on `harmonicPlateauTest B` and `signedPlateauTest M_k B` uniquely pinches any dominating shifted-pole weight to $\varphi = \zeta(1+k)^{-1} < k$, refuting $\varphi = k$ (`not_forall_window_domination_linear_shiftedPole`, `not_forall_window_domination_backwardTateGamma_shiftedPole`, `not_forall_window_domination_symTateGamma_shiftedPole`).
   - `four_mul_riemannPhiTransform_sq_lt_mul_zeta`, `not_forall_windowRiemannKernel_domination_of_le_eulerProduct`, `not_exists_shiftedPole_weight_domination_linear`, `not_exists_shiftedPole_weight_domination_backwardTateGamma`, `not_exists_shiftedPole_weight_domination_symTateGamma`: log-convexity of $\Gamma$ on $[3/2, 2]$ and $\zeta(1+k) < 1/k + 7/8$ give $4\xi(1+k)^2 < k\zeta(1+k)$ on $(0, 1]$, refuting all $\varphi \le \zeta(1+k)^{-1}$ on `windowRiemannKernel A` and hence refuting every $\varphi \in \mathbb{R}$.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Two independent mechanisms obstruct global domination across all windows: (i) near $k = 0$, Selberg's second jet $\Lambda_2(2) = (\log 2)^2 > 0$ creates a positive $O(k^2)$ arithmetic curvature on Riemann's positive near-radical tests `windowRiemannKernel A` where $Q(H_A) \le C_0\exp(-e^{A-2})$, forcing any window-local horizon $k_0(A)$ to collapse doubly exponentially (`exists_horizon_le_doubleExp`); (ii) at fixed $0 < k < 1$, 1D Euler–Maclaurin hyperbola asymptotics on positive and sign-flipped harmonic plateaus uniquely pinch any shifted-pole weight to $\varphi(k) = \zeta(1+k)^{-1} < k$ (`shiftedPole_weight_pinched_eq_eulerProduct`), and log-convexity of $\Gamma$ gives $4\xi(1+k)^2 < k\zeta(1+k)$ (`four_mul_riemannPhiTransform_sq_lt_mul_zeta`), refuting even $\varphi(k) = \zeta(1+k)^{-1}$ on `windowRiemannKernel A` (`not_exists_shiftedPole_weight_domination_linear`, `not_exists_shiftedPole_weight_domination_backwardTateGamma`, `not_exists_shiftedPole_weight_domination_symTateGamma`).
- **Strongest positive survivor:** (1) Unconditional positive domination past the first prime fold $\log 2$ across $[0, 2\,\mathrm{enlargedWeilFloorAperture}] \supset [\log 2, \frac{181}{250}]$ (`firstFoldStage_backwardTateGammaDomination`, `firstFoldStage_symTateGammaDomination`, `firstFoldSubstage_explicit_primeTwo_domination`); (2) Sequential dimension-zero inheritance and explicit Bombieri–Selberg quadratic envelope (`weilQuad_nonneg_of_seq_tateDomination`, `jordanTotient_sub_linear_ge_selberg`, `jordanTotient_sub_linear_le_sq`); (3) Exact Möbius–Euler residue pinching law $\varphi(k) = \zeta(1+k)^{-1}$ and strict archimedean–Euler inequality $4\xi(1+k)^2 < k\zeta(1+k)$ on $(0, 1]$ (`shiftedPole_weight_pinched_eq_eulerProduct`, `four_mul_riemannPhiTransform_sq_lt_mul_zeta`), combined in `archimedean_tate_domination_complete_solution`.
- **New insight:** `obstacles-summary.md` §2.8 framed a binary alternative between failure already at the first fold $\log 2$ and uniform tower domination. Neither holds: archimedean Tate families **do** dominate unconditionally past $\log 2$ wherever $Q$ retains a strict spectral floor, yet global positive-dimension domination fails because any $k > 0$ exposes both Selberg's $\Lambda_2$ curvature on $\Xi$'s radical and the Euler-product pole residue $\zeta(1+k)^{-1} \ne k$. Thus dimension-zero positivity cannot be inherited from a window-independent positive-dimension Gamma–pole comparison; positivity must operate directly at $k = 0$.
- **Status:** Formalized unconditionally in `formal/GaloisForLFunctions/ArchimedeanTateDomination/` (`TheDimensionZeroInheritanceLaw.lean`, `TateGammaFamilies.lean`, `UnshiftedImpossibilityAndHorizonCollapse.lean`, `ShiftedPoleResiduePinchingAndNoGo.lean`, `FirstFoldStageDomination.lean`), wired into `formal/GaloisForLFunctions/ArchimedeanTateDomination.lean` and `formal/GaloisForLFunctions/MainTheorems.lean`; `lake --old env lean` and `#print axioms` verified (`[propext, Classical.choice, Quot.sound]`).
