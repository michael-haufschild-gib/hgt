# Beurling one-off zero countermodels and quantitative critical-line functional-equation defect trade-off

- **ID:** beurling-one-off-countermodels-and-defect-tradeoff
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For $\frac{1}{3} < \mu < \frac{1}{2}$, $0 < \nu < 3\mu - 1$, and $\gamma \ne 0$, the positive-density Beurling zeta function `overRegularZeta μ ν γ` has exact pole-free right-half-plane zero set $\{s : \frac{1}{2} + h < \operatorname{Re} s \land s \ne 1 \land \mathrm{overRegularZeta}\,\mu\,\nu\,\gamma\,s = 0\} = \{(1 - \mu) \pm i\gamma\}$ for every $h \in [0, \frac{1}{2} - \mu)$ and vertical limit $\lim_{|t|\to\infty} \mathrm{overRegularZeta}\,\mu\,\nu\,\gamma\,(\sigma + it) = 1$, violating both the asymptotic abscissa law and weak zero-disc recurrence; conversely, for any countable Beurling system $B$ with critical-line functional-equation defect $g \in L^1(\mathbb{R})$, $\int \|g\| = 0$ forces exact integer norms and rational-prime norms, while any prime-count mismatch, prime displacement $> \delta$, or relative integer displacement $> \eta$ forces an explicit positive lower bound on $\int \|g(t)\|\,dt$.

## Paper proof

1. **Zero classification and non-recurrence of `overRegularZeta`.** On $\operatorname{Re} s > -(3\mu - 1 - \nu)$ with $s \ne 1$, the denominator $(s - 1)(s + 3\mu - 1 - \nu)(s + 3\mu - 1 + \nu)$ is nonzero (`overRegularZeta_denom_ne_zero`), so `overRegularZeta μ ν γ s = 0` iff $((s - (1 - \mu))^2 + \gamma^2)(s + (4\mu - 1)) = 0$, i.e. $s = (1 - \mu) \pm i\gamma$ or $s = -(4\mu - 1)$. Since $-(4\mu - 1) < 0 < \frac{1}{2} + h < 1 - \mu$, only $(1 - \mu) \pm i\gamma$ lie in $\operatorname{Re} s > \frac{1}{2} + h$. From the partial-fraction decomposition (`overRegularZeta_eq_partialFractions`), $\mathrm{overRegularZeta}(\sigma + it) \to 1$ as $t \to \pm\infty$, so $\|\mathrm{overRegularZeta}(\rho_0 + i\tau) - \mathrm{overRegularZeta}(\rho_0)\| \ge \frac{1}{2}$ for all large $|\tau|$ at $\rho_0 = (1 - \mu) + i\gamma$.

2. **Zero-defect rational-prime rigidity and quantitative $L^1$ defect lower bounds.** When $\int \|g\| = 0$, $400 N^2 \int \|g\| = 0 \le 1$ and $\sqrt{\frac{3\pi}{2} \int \|g\|} = 0$ for all $N \ge 4$, so `beurling_primes_of_critical_line_defect` gives $B.\mathrm{intNorm}\,x = \operatorname{round}(B.\mathrm{intNorm}\,x)$, unique attainment of every $m \ge 1$, and exact norm-preserving bijections between Beurling primes $< N - \frac{3}{2}$ and rational primes $\le N - 2$. Contrapositively, non-existence of a prime bijection forces $\int \|g\| > \frac{1}{400 N^2}$; a Beurling prime at distance $> \delta$ from all rational primes $\le N - 2$ forces $\int \|g\| \ge \min(\frac{1}{400 N^2}, \frac{2\delta^2}{3\pi N^2})$; and a generalized integer with $|B.\mathrm{intNorm}\,x - \operatorname{round}(B.\mathrm{intNorm}\,x)| > \eta \cdot B.\mathrm{intNorm}\,x$ forces $\int \|g\| \ge \min(\frac{1}{6400}, \frac{2\eta^2}{3\pi})$.

## Lean

Module `formal/GaloisForLFunctions/ArithmeticPositiveDuality/BeurlingOneOffZeroCountermodelsAndDefectTradeoff.lean` (wired in `ArithmeticPositiveDuality.lean`):
- `overRegularZeta_eq_zero_iff`
- `overRegularZeta_eq_zero_conj`
- `overRegularZeta_right_zeroSet_eq_pair`
- `tendsto_overRegularZeta_im_atTop`
- `tendsto_overRegularZeta_im_atBot`
- `not_weakRecurrence_overRegularZeta`
- `beurling_intNorm_eq_round_and_primes_of_zero_defect`
- `critical_line_defect_gt_of_not_prime_equiv`
- `critical_line_defect_ge_of_prime_dist_gt`
- `critical_line_defect_ge_of_intNorm_dist_gt`

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  compiles with `lake --old env lean`
