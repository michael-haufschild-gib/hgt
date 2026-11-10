# Unconditional Decision of the Asymptotic Abscissa Law (`AAL`)

- **ID:** aal-top-attained-off-line-solution
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-1011/fable.md §5.3 · docs/reports/review-0711/aal.md
- **Statement:** `RHTower.AsymptoticAbscissaLaw` ($\Theta_\infty = \Theta$) holds unconditionally for $\zeta(s)$, equivalently $G(u) = e^{-(\Theta - 1/2)u} c_B(u)$ never converges as $u \to +\infty$ to a nonzero finite trigonometric polynomial.

## Goal
Establish a complete, dependency-closed unconditional proof of `RHTower.AsymptoticAbscissaLaw` for $\zeta(s)$ and formalize in Lean 4:
1. `RHTower.AsymptoticAbscissaLaw` ($\Theta_\infty = \Theta$).
2. Elimination of World I in the cubic-spline trace trichotomy for $G(u) = e^{-(\Theta - 1/2)u} c_B(u)$ and the smoothed/Chebyshev prime error $o(x^\Theta)$ law for $\Theta > 1/2$.
3. Unconditional collapse corollaries (`RiemannHypothesis ↔ ZerosApproachLine`, `RiemannHypothesis ↔ FiniteOffLine`, finite Weil negative index, bounded de Bruijn–Newman nonreal zero counts, finite critical source energy, eventual Hadamard positivity, eventual Gaussian central-gap budget, finite-dimensional odd bound-state space).

## Gates
- [x] 0 → 1  in-progress: corpus inventory, countermodel calibration suite, and target equivalences verified
- [ ] 1 → 2  fully-proven: quantifier-exact, dependency-closed paper proof with zero open premises
- [ ] 2 → 3  formalized: unconditional Lean 4 module checked via `lake --old env lean`, `#print axioms` clean, wired into umbrella

## Calibration Firewall
Every candidate proof must simultaneously fail on:
1. Integer-norm Beurling Euler products (`AnIntegerNormBeurlingOneOff`, `TheRationalPrimeOneOffHasMultiplicativeCounting`): Euler product with integer norms and linear counting, lacking $N(x) = \lfloor x \rfloor$ and the Riemann functional equation.
2. Functional-equation / relocation / heat deformations (`SymmetricRationalZeroRelocationBohrObstruction`, $\xi_\beta$, $H_t$ for $0 < t < \Lambda$, `exists_riemann_gamma_counting_model_without_landing`): exact $s \leftrightarrow 1 - s$ functional equation and Gamma factor, lacking the Dirichlet series $\sum_{n \ge 1} n^{-s}$ over $\mathbb{N}$.
3. Bounded-count / near-count Euler modifications (`ABoundedCountWithANewZero`, `PositiveNearCountEuler`): preserve `AAL` while violating `ZAL` or altering finite factors.

## Approach
Eliminate the bilateral spectral-gap configuration ($\frac{1}{2} \le \beta_1 < \Theta < 1$, nonempty finite top layer $F_+$ on $\operatorname{Re} s = \Theta$ with $|\operatorname{Im}\rho| \le T_*$, reflected layer $F_-$ on $\operatorname{Re} s = 1 - \Theta$, and all other strip zeros in $[1 - \beta_1, \beta_1]$) by coupling the exact unit-coefficient $\mathbb{N}$-Dirichlet / sawtooth structure with the Riemann functional equation across the global zero-free strips $(\beta_1, \Theta)$ and $(1 - \Theta, 1 - \beta_1)$.

## Log
- 2026-11-10 — created in 1-in-progress
