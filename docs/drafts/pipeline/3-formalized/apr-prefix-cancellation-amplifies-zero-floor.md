# Prefix cancellation amplifies the off-line zero floor

- **ID:** APR-PREFIX-ZERO-FLOOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0511/route-wd.md` §1 · `ArithmeticProduction/EveryOffLineZeroPinsAFloor.lean`
- **Statement:** If $\sum_{d \in S, d \mid n} a_d = \delta_{n,1}$ for $1 \le n \le y_1$, then $\mathrm{mollifierDefect}(S, a) \ge \frac{(2\operatorname{Re}\rho - 1)\|1 - \rho\|^2}{\|\rho\|^4}\, y_1^{2\operatorname{Re}\rho - 1}$ at every off-line zeta zero $\rho$, and unweighted $[1, T]$ critical-line moments are controlled by $2(T - 1) + 4\pi(\frac{1}{4} + T^2)\,\mathrm{mollifierDefect}(S, a)$.

## Goal
Extend the length-independent sawtooth Laplace floor of `EveryOffLineZeroPinsAFloor` to initial-segment divisor-cancelling polynomials, obtaining exact $y_1^{2\operatorname{Re}\rho - 1}$ amplification and two-way coupling between `mollifierDefect` and unweighted critical-line second moments.

## Gates
- [x] 0 → 1  in-progress: sawtooth linearity on $[0, y_1 + 1)$ and shifted Laplace Cauchy–Schwarz split formulated
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, unconditional paper proof closed
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/ArithmeticProduction/PrefixCancellationAmplifiesTheZeroFloor.lean` (`sawtoothDefect_eq_mul_valueAtOne_of_prefix_cancel`, `mollifierDefect_floor_mul_rpow_of_prefix_cancel`, `mollifierDefect_sharpCoeff_floor`, `xiZeroHalfPlaneBound_of_frequently_sharpDefect_le`, `riemannHypothesis_of_frequently_sharpDefect_subpolynomial`, `integral_normSq_zeta_realDirichletPoly_le_of_mollifierDefect`)

## Proof mechanism
1. **Extended sawtooth linearity:** By the hyperbola identity $\sum_{d \in S} a_d \lfloor \lfloor x \rfloor / d \rfloor = \sum_{1 \le n \le \lfloor x \rfloor} (\sum_{d \in S, d \mid n} a_d) = 1$ for $1 \le x < y_1 + 1$, `sawtoothDefect S a x = x · D(1)` holds identically on $[0, y_1 + 1)$.
2. **Shifted Laplace quadratic minimization:** Splitting the Laplace identity at $u = \log y_1$ evaluates the head explicitly via `valueAtOne` and bounds the tail $u > \log y_1$ by Cauchy–Schwarz against $e^{-(2\operatorname{Re}\rho - 1) u}$. Minimizing the resulting positive-definite quadratic in $|D(1)|\, y_1^{1 - \operatorname{Re}\rho}$ yields the $D(1)$-independent lower bound $\frac{(2\operatorname{Re}\rho - 1)\|1 - \rho\|^2}{\|\rho\|^4}\, y_1^{2\operatorname{Re}\rho - 1}$.
3. **Unweighted $[1, T]$ Plancherel bridge:** Pointwise $\|z\|^2 \le 2 + 2(\frac{1}{4} + T^2)\frac{\|1 - z\|^2}{1/4 + t^2}$ on $[1, T]$ integrates via `mollifierDefect_eq` to $2(T - 1) + 4\pi(\frac{1}{4} + T^2)\,\mathrm{mollifierDefect}(S, a)$.

## Log
- 2026-11-06 — formalized in `ArithmeticProduction/PrefixCancellationAmplifiesTheZeroFloor.lean` and wired into `ArithmeticProduction.lean`.
