# Asymptotic Abscissa Law (`AsymptoticAbscissaLaw`)

## Route Context
Answers §2.9 of `docs/reports/review-0611/obstacles-summary.md`: whether an off-line zero of $\zeta(s)$ can be a one-off, formalized as `RHTower.AsymptoticAbscissaLaw`:
$$\forall h \ge 0,\quad \#\{\rho : \operatorname{Re}\rho > \tfrac{1}{2} + h\} < \infty \implies \{\rho : \operatorname{Re}\rho > \tfrac{1}{2} + h\} = \emptyset,$$
equivalently $\limsup_{|\gamma|\to\infty} (\operatorname{Re}\rho - \tfrac{1}{2}) = \sup_\rho (\operatorname{Re}\rho - \tfrac{1}{2})$.

## Mathematical Target
Establish an unconditional resolution of `RHTower.AsymptoticAbscissaLaw` and its corpus-wide consequences (`RiemannHypothesis ↔ ZerosApproachLine`, `RiemannHypothesis ↔ FiniteOffLine`, `RiemannHypothesis ↔ EventualHadamardPositivity`, `RiemannHypothesis ↔ EventualFilteredCentralGapBudget`, `RiemannHypothesis ↔ FiniteDimensional ℝ oddBoundStateSpace`).

## Structural Constraints from Corpus Countermodels
Any valid proof of `AsymptoticAbscissaLaw` for $\zeta(s)$ must simultaneously use properties that separate $\zeta(s)$ from all countermodels violating AAL:
1. **Euler product + small prime perturbation (`BeurlingRHSensitivityThreshold`):** $\zeta(s)\frac{(s-\beta)^2+\gamma^2}{(s-\beta)^2}$ violates AAL if $\zeta$ satisfies RH (fails holomorphy of $(s-1)\zeta(s)$ at $s=\beta$ and functional equation).
2. **Continuous Beurling system with $N(x) = \rho x + C + o(1)$ (`BeurlingOverRegularIntegersOffLineZeros`):** rational zeta with off-line zero pair $1-\mu \pm i\gamma$ and positive prime/integer densities (fails discrete $\log\mathbb{N}$ support and Riemann functional equation).
3. **Selberg zeta of hyperbolic surface with small eigenvalues $\lambda \in (0, 1/4)$:** Euler product + exact functional equation $s \leftrightarrow 1-s$ + finite real zeros in $(1/2, 1)$ (zeros lie on the real interval $(1/2, 1)$, whereas $\zeta(s) < 0$ on $(0, 1)$, and prime lengths are not $\log p$).
4. **Davenport–Heilbronn / linear combinations of $L$-functions:** exact functional equation + integer Dirichlet series $\sum c_n n^{-s}$ (fails Euler product / multiplicativity).
5. **Discrete Beurling countermodel vs functional-equation rigidity:** Broucke–Debruyne–Vindas random prime discretization applied to `overRegularZeta` (`BeurlingOverRegularIntegersOffLineZeros`) yields a discrete Beurling system $\mathcal{P}$ with $\mathbb{Q}$-independent $\{\log p_k\}$, Euler product, $N_{\mathcal{P}}(x) = \rho x + O(x^{1/2+\varepsilon})$, and nonvanishing Voronin universality, yet violating `AsymptoticAbscissaLaw` and `ZetaZeroDiscWeaklyRecurrent`. Conversely, `PositiveMeasureHamburgerRigidity` (`eq_riemannPrimeMeasure_of_beurling_functional_equation`) proves that no non-Riemann Borel Beurling prime measure satisfies $\xi(s) = \xi(1-s)$. Hence any proof of `AsymptoticAbscissaLaw` must combine **multiplicativity ($\Lambda$ / Euler product)** with **$\mathbb{N}$-integrality / Riemann's functional equation**, and must refute the single-quartet `FiniteOffLine` model $\beta_* \pm i\gamma_*, (1-\beta_*) \pm i\gamma_*$.

## Exact Structure of `¬ AsymptoticAbscissaLaw`
Negating `AsymptoticAbscissaLaw` ($\Theta_\infty := \limsup_{|\gamma|\to\infty} \operatorname{Re}\rho < \Theta := \sup_\rho \operatorname{Re}\rho$ with $\Theta > 1/2$) yields an isolated top layer:
- There exist $\beta_* \in (1/2, 1)$, $\delta > 0$ ($\beta_1 := \beta_* - \delta \ge 1/2$), and $T_* > 0$ such that:
  1. $\zeta(s) \ne 0$ for all $\operatorname{Re} s > \beta_*$;
  2. the top zero set $F_* = \{\rho : \operatorname{Re}\rho = \beta_*\}$ is **finite and nonempty**, consisting of conjugate pairs $\beta_* \pm i\gamma_j$ with $0 < \gamma_1 < \dots < \gamma_K \le T_*$;
  3. $\zeta(s) \ne 0$ on the open vertical strip $\beta_1 < \operatorname{Re} s < \beta_*$, and all zeros with $|\gamma| > T_*$ satisfy $1 - \beta_1 \le \operatorname{Re}\rho \le \beta_1$.

## Proved Obstructions to Direct Approaches
- **Zero-density self-return barrier (`ZetaRecurrenceAtEveryPointModuloItsZeros`):** Nonzero values $c \ne 0$ recur with positive lower density around every $c$-point (`exists_zetaDiscStronglyRecurrentOn_iff_ne_zero`), whereas self-returns around zeros have density zero (`exists_zetaSelfReturn_density_zero`). Conditioning a smooth Dirichlet approximation on $p^{-i\tau} \to 1$ ($p \le 2X_0$) either leaves a coherent $2X_0$-smooth tail $\prod_{p \le 2X_0}(1 - p^{-s})^{-1} \ne 0$, or in a compactly supported approximate functional equation inflates the dual Montgomery–Vaughan frequency by $e^{\pi(2X_0)}$ where $2(\sigma - 1) + 1 = 2\sigma - 1 > 0$ fails to decay.
- **Landau real-anchor shielding (`PowerLagLandauCriterion`):** Any real nonnegativity majorant for oscillating top-layer prime waves $W_*(x) = \sum_{\rho \in F_*} m_\rho x^\rho / \rho$ requires a positive DC component $c_0 x^{\beta_*}$, placing a real pole at $s = \beta_*$ that shields $\beta_* \pm i\gamma_j$ from Landau's theorem; nonlinear zero-side squares $\sum (\operatorname{integerLag} n)^2 n^{-s}$ likewise place a real pole at $s = 2\beta_*$ via conjugate pairing $q_2 = \bar{q}_1$.
- **Additive circle / short-interval energy:** Major-arc energy of $\sum_{n \le X} \Lambda(n) e(n\alpha)$ from $F_*$ is $O(X^{2\beta_*-1} \log Q) \ll X \log X$ since $2\beta_* - 1 < 1$; short-interval variance $\int_X^{2X} |\psi(x+H) - \psi(x) - H|^2 dx \asymp H^2 X^{2\beta_*-2}$ cannot be contradicted unconditionally without prime pair correlation.
- **Euler-head negative index (`TheIndexOfAGrowingEulerHeadIsUnbounded`):** Unbounded negative index of $\Gamma - \text{head}(p \le Y)$ arises from the sharp truncation kink $\min(\gamma, 1)$ at $m = Y$; restoring $p > Y$ smooths the window profile to $2\sqrt{\gamma}$, collapsing the detail–window coupling to rank $1$ (paid by the $s=1$ pole) even under RH.

## Dependencies
- `GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse`
- `GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers`
- `GaloisForLFunctions.RHTower.CrossRouteReceiverBridges`

## Proof Sketch
TBD upon surviving Phase 4 attack.

## Lean 4 Formalization Reference
Target subfolder: thematic module outside `RHTower` and `HTGeometry`.
