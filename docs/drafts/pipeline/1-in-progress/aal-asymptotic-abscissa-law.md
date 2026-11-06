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
5. **Exact discrete Beurling system + Riemann functional equation (`BeurlingRiemannFunctionalEquationRigidity`):** uniquely forces $\zeta(s)$ (`beurlingSystem_rigidity_of_completed_functional_equation`).

## Exact Structure of `¬ AsymptoticAbscissaLaw`
Negating `AsymptoticAbscissaLaw` yields a strict isolated top layer:
- There exist $\beta_* \in (1/2, 1)$ and $\delta > 0$ such that:
  1. $\zeta(s) \ne 0$ for all $\operatorname{Re} s > \beta_*$;
  2. the top zero set $F_* = \{\rho : \operatorname{Re}\rho = \beta_*\}$ is **finite and nonempty**, consisting of conjugate pairs $\beta_* \pm i\gamma_j$ with $\gamma_j > 0$ (since $\zeta(\sigma) \ne 0$ for $\sigma \in (0, 1)$);
  3. $\zeta(s) \ne 0$ on the open vertical strip $\beta_* - \delta < \operatorname{Re} s < \beta_*$, and all remaining nontrivial zeros satisfy $\operatorname{Re}\rho \le \beta_* - \delta$ (and by functional equation $\operatorname{Re}\rho \ge 1 - \beta_*$).

## Conjectures & Attacks
*(In progress — Phase 3/4 conjecture loop)*

## Dependencies
- `GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse`
- `GaloisForLFunctions.RHTower.AsymptoticAbscissaLawProducers`
- `GaloisForLFunctions.RHTower.CrossRouteReceiverBridges`

## Proof Sketch
TBD upon surviving Phase 4 attack.

## Lean 4 Formalization Reference
Target subfolder: thematic module outside `RHTower` and `HTGeometry`.
