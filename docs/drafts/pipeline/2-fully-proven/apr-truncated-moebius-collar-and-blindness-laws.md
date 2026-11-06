# Truncated Möbius collar dichotomy, $\ell^2$-blindness, and the shifted-inverse countermodel on $\mathbb{N}$

- **ID:** APR-COLLAR-AND-BLINDNESS-LAWS
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0511/route-wd.md` §1 · `ArithmeticProduction/PrefixCancellationAmplifiesTheZeroFloor.lean`
- **Statement:** For $c_X(n) = \sum_{d \mid n, d \le X} \mu(d)$, on $(X, X^2]$ every composite integer with a prime factor $> X$ has $c_X(n) = 0$ (while primes $p > X$ satisfy $c_X(p) = 1$ and $n \in (X, 2X]$ satisfy $c_X(n) = -\mu(n)$), every collar polynomial $\sum_{X < n \le X R} c_X(n) n^{-s}$ factors as $-\sum_{r=1}^R r^{-s} \sum_{X < m \le X R / r} \mu(m) m^{-s}$, prefix-vanishing unit-sign sequences with $\sum_{n \le M} c_n^2 \le M$ still admit critical-line moments $\ge \frac{X}{100\log(2X)}$ on $[1, T]$, and the multiplicative shifted-inverse pair $(a_\delta, b_\delta)$ on $\mathbb{N}$ satisfies $(a_\delta * b_\delta) = \delta_1$, $\|a_\delta\|, \|b_\delta\| \le 1$, and $\sum_{d \ge 1} \frac{\|b_\delta(d)\|^2}{d} < \infty$ yet blows up as $\frac{\kappa_\delta X^{2\delta}}{\log(2X)}$ on $[1, T]$.

## Goal
Establish the exact arithmetic support and collar factorization laws of $c_X(n)$ together with unconditional countermodels proving that neither linear $\ell^2$ coefficient energy nor bounded Euler-product invertibility on $\mathbb{N}$ with $\sum \|b(d)\|^2/d < \infty$ suffices for `route-wd.md` §1 without global pole-only entirety.

## Gates
- [x] 0 → 1  in-progress: smooth–prime dichotomy, complementary divisor flip, $\ell^2$-blindness construction, gauge equivariance, and shifted-inverse $\mathbb{N}$-countermodel formulated
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, complete unconditional paper proofs
- [ ] 2 → 3  formalized: `formal/GaloisForLFunctions/ArithmeticProduction/TruncatedMoebiusCollarAndBlindnessLaws.lean`

## Theorems and complete paper proofs `[PROVED HERE]`

### Theorem 1 (Smooth–prime dichotomy on $(X, X^2]$ and collar Dirichlet factorization) `[PROVED HERE]`
Let $c_X(n) = \sum_{d \mid n, d \le X} \mu(d)$ for $X \ge 1$.
1. **First octave:** For $X < n \le 2X$, every proper divisor $d \mid n$ satisfies $d \le n/2 \le X$, so $c_X(n) = \sum_{d \mid n} \mu(d) - \mu(n) = -\mu(n)$.
2. **Primes above $X$:** For prime $p > X$, $\{d \mid p : d \le X\} = \{1\}$, so $c_X(p) = 1$.
3. **Composite rough vanishing on $(X, X^2]$:** If $X < n \le X^2$, $n$ is not prime, and some prime $p > X$ divides $n$, write $n = p m$. Since $n$ is not prime and $n > X \ge 1$, $m \ge 2$; since $p m \le X^2 < p X$, $m < X < p$. Thus $p \nmid m$, $\gcd(p, m) = 1$, and $\{d \mid p m : d \le X\} = \{d \mid m\}$, giving $c_X(n) = \sum_{d \mid m} \mu(d) = 0$.
4. **Complementary divisor flip and collar Cauchy–Schwarz:** For $n \ge 2$, $c_X(n) = -\sum_{m \mid n, m > X} \mu(m)$. Bijecting $(n, m) \leftrightarrow (r, m)$ via $n = r m$ over $X < n \le X R$ ($R \ge 1$) yields
   $$\sum_{X < n \le X R} c_X(n)\, n^{-s} = -\sum_{r=1}^R r^{-s} \sum_{X < m \le \lfloor X R / r \rfloor} \mu(m)\, m^{-s},$$
   and Cauchy–Schwarz on $\operatorname{Re} s = \frac{1}{2}$ bounds $\int_1^T \|\sum_{X < n \le X R} c_X(n) n^{-1/2-it}\|^2\,dt$ by $(1 + \log R) \sum_{r=1}^R \int_1^T \|\sum_{X < m \le \lfloor X R / r \rfloor} \mu(m) m^{-1/2-it}\|^2\,dt$. $\square$

### Theorem 2 (Multiplicative gauge-twist equivariance) `[PROVED HERE]`
For any finite support $S \subset \mathbb{N}_+$, coefficients $b : \mathbb{N} \to \mathbb{C}$, and completely multiplicative $\chi : \mathbb{N} \to \mathbb{C}$ ($\chi(d q) = \chi(d)\chi(q)$ for $d, q \ge 1$), every $n \ge 1$ satisfies
$$\sum_{d \in S,\, d \mid n} \bigl(b(d)\chi(d)\bigr)\,\chi(n / d) = \chi(n) \sum_{d \in S,\, d \mid n} b(d),$$
and if $\|\chi(n)\| = 1$ for $n \ge 1$, both sides have identical modulus at every $n \ge 1$. $\square$

### Theorem 3 ($\ell^2$-blindness of prefix-cancelled unit-sign sequences) `[PROVED HERE]`
For every $X \ge 2$ and $T \ge 2$, there exists $c : \mathbb{N} \to \mathbb{Z}$ with $c(1) = 1$, $c(n) = 0$ for $2 \le n \le X$, $|c(n)| \le 1$ for all $n \in \mathbb{N}$ (hence $\sum_{n=1}^M c(n)^2 \le M$ for all $M$), and
$$\int_1^T \left\|\sum_{n \in \mathrm{Ioc}\ X\ (2X)} (c(n) : \mathbb{C})\, n^{-1/2 - it}\right\|^2 dt \ge \frac{X}{100 \log(2X)}.$$

*Proof.* Set $t_0 = \frac{3}{2}$ and $z_n = n^{-1/2 - i t_0}$ for $n \in \mathrm{Ioc}\ X\ (2X)$. Since $\|z_n\| = n^{-1/2} \ge (2X)^{-1/2}$ and $\|z_n\| \le |\operatorname{Re} z_n| + |\operatorname{Im} z_n|$, either $\sum |\operatorname{Re} z_n| \ge \frac{\sqrt{X}}{2\sqrt{2}}$ or $\sum |\operatorname{Im} z_n| \ge \frac{\sqrt{X}}{2\sqrt{2}}$. Choosing $c(n) \in \{\pm 1\}$ on $\mathrm{Ioc}\ X\ (2X)$ to match the signs of $\operatorname{Re} z_n$ (resp. $\operatorname{Im} z_n$) gives $\|\sum c(n) z_n\| \ge \frac{\sqrt{X}}{2\sqrt{2}}$. For $|t - t_0| \le \eta := \frac{1}{8\log(2X)}$, $[t_0 - \eta, t_0 + \eta] \subseteq [1, 2] \subseteq [1, T]$ and $\|n^{-i(t-t_0)} - 1\| \le |(t - t_0)\log n| \le \frac{1}{8}$, shifting the sum by at most $X \cdot \frac{1}{8\sqrt{X}} = \frac{\sqrt{X}}{8}$. Hence $\|\sum c(n) n^{-1/2-it}\| \ge (\frac{1}{2\sqrt{2}} - \frac{1}{8})\sqrt{X} \ge \frac{\sqrt{X}}{5}$ throughout $[t_0 - \eta, t_0 + \eta]$ of length $2\eta = \frac{1}{4\log(2X)}$, yielding $\ge \frac{X}{100\log(2X)}$. $\square$

### Theorem 4 (Shifted-inverse multiplicative countermodel on $\mathbb{N}$) `[PROVED HERE]`
For every $\delta \in (0, \frac{1}{2})$, set $s_\delta := (\frac{1}{2} - \delta) - 2i$, $a_\delta(n) := \mathbf{1}_{n \ge 1}\,\mu(n)\,n^{-s_\delta}$, $b_\delta(d) := \mathbf{1}_{d \ge 1}\,d^{-s_\delta}$, and $F_\delta(s) := \zeta(s + s_\delta)^{-1}$. Then:
1. $a_\delta, b_\delta$ are multiplicative on $\mathbb{N}$, $\sum_{d \mid n} a_\delta(d) b_\delta(n/d) = \delta_{n,1}$ for all $n \ge 1$, $\|a_\delta(n)\| \le 1$, $\|b_\delta(d)\| \le 1$, $\sum_{d=1}^\infty \frac{\|b_\delta(d)\|^2}{d} < \infty$, and $L(a_\delta, s) = F_\delta(s)$ on $\operatorname{Re} s > \frac{1}{2} + \delta$;
2. $t \mapsto F_\delta(\frac{1}{2}+it)$ is continuous and zero-free across $[1, 3]$, and there exists $\kappa_\delta > 0$ such that for every $X \ge 2$,
   $$\int_1^3 \left\|F_\delta\!\left(\tfrac{1}{2}+it\right) \sum_{d=1}^X b_\delta(d)\, d^{-1/2-it}\right\|^2 dt \ge \frac{\kappa_\delta\, X^{2\delta}}{\log(2X)},$$
   hence for every $T \ge 3$ the Lebesgue $L^2$ integral on $(1, T]$ satisfies $\int_{(1, T]}^- \|F_\delta(\frac{1}{2}+it) \sum_{d=1}^X b_\delta(d) d^{-1/2-it}\|^2 dt \ge \frac{\kappa_\delta X^{2\delta}}{\log(2X)}$.

*Proof.* Property (1) is immediate since $\|b_\delta(d)\|^2 / d = d^{-(2 - 2\delta)}$ with $2 - 2\delta > 1$. On $t \in [1, 3]$, $\frac{1}{2} + it + s_\delta = (1 - \delta) + i(t - 2)$ has real part $1 - \delta \in (\frac{1}{2}, 1)$ and $|t - 2| \le 1 \le \frac{9}{2}$, so $\xi((1-\delta)+i(t-2)) \ne 0$ (`xi_ne_zero_of_abs_im_le_nine_halves`), hence $\zeta((1-\delta)+i(t-2)) \ne 0$ (`riemannZeta_ne_zero_of_xi_ne_zero`) and $F_\delta(\frac{1}{2}+it)$ is continuous on $[1, 3]$. By continuity at $t = 2$, $\|F_\delta(\frac{1}{2}+it)\| \ge c_1 > 0$ for $|t - 2| \le r_\delta$ with $r_\delta \in (0, \frac{1}{2}]$. Meanwhile $b_\delta(d) d^{-1/2-2i} = d^{-(1-\delta)} \ge X^{-(1-\delta)}$ for $1 \le d \le X$, so $S(2) := \sum_{d=1}^X d^{-(1-\delta)} \ge X \cdot X^{-(1-\delta)} = X^\delta$. For $|t - 2| \le \eta := \frac{r_\delta}{\log(2X)}$, $\|d^{-i(t-2)} - 1\| \le |t - 2|\log d \le r_\delta \le \frac{1}{2}$, so $\|\sum_{d=1}^X b_\delta(d) d^{-1/2-it} - S(2)\| \le \frac{1}{2} S(2)$ and $\|\sum_{d=1}^X b_\delta(d) d^{-1/2-it}\| \ge \frac{1}{2} X^\delta$ across $[2 - \eta, 2 + \eta] \subseteq [1, 3]$, giving $\int_1^3 \ge \frac{c_1^2 r_\delta}{2} \frac{X^{2\delta}}{\log(2X)}$ and monotonicity on $(1, 3] \subseteq (1, T]$ for all $T \ge 3$. $\square$

## Log
- 2026-11-06 — complete unconditional paper proofs recorded in `2-fully-proven`.
