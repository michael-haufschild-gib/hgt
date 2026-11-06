# Beurling One-Off Zero Countermodels and Quantitative Critical-Line Functional-Equation Defect Trade-Off

- **Status:** `2-fully-proven`
- **Target subfolder:** `formal/GaloisForLFunctions/ArithmeticPositiveDuality/BeurlingOneOffZeroCountermodelsAndDefectTradeoff.lean`

## Theorem Statements

1. **Complete Zero Classification & One-Off Non-Recurrence of `overRegularZeta` (`overRegularZeta_eq_zero_iff`, `overRegularZeta_right_zeroSet_eq_pair`, `tendsto_overRegularZeta_im_atTop`, `not_weakRecurrence_overRegularZeta`):**
   For $\frac{1}{3} < \mu < \frac{1}{2}$, $0 < \nu < 3\mu - 1$, and $\gamma \ne 0$, the continuous Beurling zeta function `overRegularZeta μ ν γ` (whose prime and integer densities are nonnegative on $(0, \infty)$ and whose integer count satisfies $N(x) = \rho x + C + o(1)$) satisfies:
   - On $\{s \in \mathbb{C} : -(3\mu - 1 - \nu) < \operatorname{Re} s \wedge s \ne 1\}$,
     $$\text{overRegularZeta }\mu\ \nu\ \gamma\ s = 0 \iff s = (1 - \mu) + i\gamma \;\lor\; s = (1 - \mu) - i\gamma \;\lor\; s = -(4\mu - 1);$$
   - For every $h \in [0, \frac{1}{2} - \mu)$, the right-half-plane zero set $\{s \in \mathbb{C} : \frac{1}{2} + h < \operatorname{Re} s \wedge \text{overRegularZeta }\mu\ \nu\ \gamma\ s = 0\}$ equals the two-element set $\{(1 - \mu) + i\gamma,\ (1 - \mu) - i\gamma\}$, violating the asymptotic abscissa law;
   - For every fixed $\sigma \in \mathbb{R}$, $\lim_{|t| \to \infty} \text{overRegularZeta }\mu\ \nu\ \gamma\ (\sigma + it) = 1$, and at the off-line zero $\rho_0 = (1 - \mu) + i\gamma$, $\|\text{overRegularZeta }\mu\ \nu\ \gamma\ (\rho_0 + i\tau) - \text{overRegularZeta }\mu\ \nu\ \gamma\ \rho_0\| \ge \frac{1}{2}$ for all sufficiently large $|\tau|$, refuting weak zero-disc recurrence.

2. **Zero-Defect Rational-Prime Rigidity and Quantitative Functional-Equation Defect Lower Bound (`beurling_intNorm_eq_round_and_primes_of_zero_defect`, `critical_line_defect_ge_of_prime_card_ne`, `critical_line_defect_ge_of_prime_dist_gt`, `critical_line_defect_ge_of_intNorm_dist_gt`):**
   Under the hypotheses of `beurling_primes_of_critical_line_defect` for a countable Beurling system $B$ with critical-line functional-equation defect $g \in L^1(\mathbb{R})$:
   - **Zero-defect rigidity:** If $\int_{\mathbb{R}} \|g(t)\|\,dt = 0$, then every generalized integer $x : B.\text{Integer}$ satisfies $B.\text{intNorm } x = \operatorname{round}(B.\text{intNorm } x)$, every integer $m \ge 1$ is within $\frac{1}{8}$ of a unique generalized integer (hence equals its norm), and for every $N \ge 4$ the Beurling primes of norm $< N - \frac{3}{2}$ are in exact norm-preserving bijection with the rational primes $\le N - 2$.
   - **Quantitative trade-off lower bounds:** For every $N \ge 4$:
     1. If the set of Beurling primes of norm $< N - \frac{3}{2}$ is not in bijection with $\{q \in \mathbb{N} : q.\text{Prime} \wedge q + 2 \le N\}$, then $\int_{\mathbb{R}} \|g(t)\|\,dt > \frac{1}{400 N^2}$.
     2. If some Beurling prime $p$ of norm $< N - \frac{3}{2}$ satisfies $|B.\text{labelNorm } p - q| > \delta$ ($\delta \ge 0$) for every rational prime $q \le N - 2$, then
        $$\int_{\mathbb{R}} \|g(t)\|\,dt \ge \min\!\left(\frac{1}{400 N^2},\; \frac{2\,\delta^2}{3\pi N^2}\right).$$
     3. If some generalized integer $x$ satisfies $|B.\text{intNorm } x - \operatorname{round}(B.\text{intNorm } x)| > \eta \cdot B.\text{intNorm } x$ ($\eta \ge 0$), then
        $$\int_{\mathbb{R}} \|g(t)\|\,dt \ge \min\!\left(\frac{1}{6400},\; \frac{2\,\eta^2}{3\pi}\right).$$

## Proof Outline

1. On $\operatorname{Re} s > -(3\mu - 1 - \nu)$ with $s \ne 1$, the denominator $(s - 1)(s + 3\mu - 1 - \nu)(s + 3\mu - 1 + \nu)$ is nonzero (`overRegularZeta_denom_ne_zero`), so `overRegularZeta μ ν γ s = 0` iff $((s - (1 - \mu))^2 + \gamma^2)(s + (4\mu - 1)) = ((s - ((1 - \mu) + i\gamma))(s - ((1 - \mu) - i\gamma)))(s + 4\mu - 1) = 0$. Since $-(4\mu - 1) < 0 < \frac{1}{2} + h < 1 - \mu$ and $\gamma \ne 0$, only the conjugate pair $(1 - \mu) \pm i\gamma$ lies in $\operatorname{Re} s > \frac{1}{2} + h$. Dividing numerator and denominator by $s^3$ gives $\lim_{|t| \to \infty} \text{overRegularZeta}(\sigma + it) = 1$.
2. When $\int \|g\| = 0$, $400 N^2 \int \|g\| = 0 \le 1$ and $\sqrt{\frac{3\pi}{2} \int \|g\|} = 0$ for every $N \ge 4$, so `beurling_primes_of_critical_line_defect` gives $|B.\text{intNorm } x - \operatorname{round}(B.\text{intNorm } x)| = 0$ and $|B.\text{labelNorm } p - e(p)| = 0$. Conversely, if $400 N^2 \int \|g\| \le 1$ (resp. $6400 \int \|g\| \le 1$ at $N = 4$), squaring $\delta < \sqrt{\frac{3\pi}{2} \int \|g\|} \, N$ (resp. $\eta < \sqrt{\frac{3\pi}{2} \int \|g\|}$) yields $\int \|g\| > \frac{2\delta^2}{3\pi N^2}$ (resp. $> \frac{2\eta^2}{3\pi}$).
