# Multiplicative Hecke algebra Poisson positivity no-go and exact resonant dispersion

- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Statement:** On the full commutative Hecke algebra $\{T_n\}_{n \ge 1}$, the resonant state functional $\mu_n(u)$ ($\operatorname{Re} u < 0$) coincides with the half-plane Poisson integral of the real tempered Hecke eigenvalue $\lambda_n(it) = W_{it}(n)$, making every $C^*$-square $\sum_{m,k \in S} \overline{c_m} c_k \sum_{d \mid \gcd(m,k)} \mu_{mk/d^2}(u)$ nonnegative even off the critical line ($\operatorname{Re} u \ne -\frac{1}{4}$); at every strip zero $\rho$ of $\Lambda$, the exact $L^2(\mathcal{D})$ Hecke eigen-defect is $2(1 - p^{\operatorname{Re}\rho - 1})\|\Lambda^Y E_u\|_{L^2(\mathcal{D})}^2$ for all $Y \ge p$, characterizing `RiemannHypothesis` and `XiZeroHalfPlaneBound` from any single prime $p$ and single height $Y \ge p$.

## Proof mechanism

1. **Multiplicative Hecke eigenvalue product law.** For $W_u(n) = n^u \sum_{d \mid n} d^{-2u} = \sum_{ad = n} a^u d^{-u}$ ($n \ge 1$), strong induction on $m \ge 1$ via the prime Hecke recurrence $W_u(p m_1) + \mathbf{1}_{p \mid m_1} W_u(m_1 / p) = (p^u + p^{-u}) W_u(m_1)$ proves
   $$W_u(m)\,W_u(n) = \sum_{d \mid \gcd(m, n)} W_u(m n / d^2) \qquad (m, n \ge 1,\ u \in \mathbb{C}).$$
   For $m = p m_1$ ($p$ prime), expanding $W_u(m_1) W_u(n)$ and applying the prime recurrence inside the sum leaves the divisor difference $\{d \mid \gcd(m_1, n) : p \mid (m_1 n / d^2)\} \setminus \{d : p \mid m_1 \land d \mid \gcd(m_1/p, n)\}$, which maps bijectively via $d \mapsto p d$ onto $\{c \mid \gcd(p m_1, n)\} \setminus \{c \mid \gcd(m_1, n)\}$. On $u = it$ ($t \in \mathbb{R}$), antidiagonal reversal $ad = n \leftrightarrow da = n$ gives $\overline{W_{it}(n)} = W_{it}(n)$.

2. **Exact Poisson mixture identity and $C^*$-positivity no-go.** By upper-half-plane Poisson reproduction (`integral_halfPlanePoisson_one_mul_eq_apply_I`), for $\sigma > 0$ and $t_0, x \in \mathbb{R}$,
   $$\int_{-\infty}^\infty P_\sigma(t - t_0)\,e^{i x t}\,dt = \exp(-\sigma |x| + i t_0 x).$$
   Summing over $ad = n$ with $x = \log(a/d)$ and $\sigma = -\operatorname{Re} u > 0$, $t_0 = \operatorname{Im} u$ yields
   $$\mu_n(u) := \sum_{ad = n} \begin{cases} (a/d)^u & d < a \\ (d/a)^{\bar{u}} & a < d \\ 1 & a = d \end{cases} = \int_{-\infty}^\infty P_{-\operatorname{Re} u}(t - \operatorname{Im} u)\,W_{it}(n)\,dt.$$
   Using the multiplication law of Step 1 and reality of $W_{it}(m)$, every finite Hecke combination $c : \mathbb{N} \to \mathbb{C}$ on $S \subset \mathbb{N}_{>0}$ satisfies
   $$\sum_{m \in S} \sum_{k \in S} \overline{c_m}\,c_k \sum_{d \mid \gcd(m,k)} \mu_{m k / d^2}(u) = \int_{-\infty}^\infty P_{-\operatorname{Re} u}(t - \operatorname{Im} u)\,\Big\|\sum_{m \in S} c_m W_{it}(m)\Big\|^2\,dt \ge 0.$$

3. **Exact $L^2(\mathcal{D})$ Hecke eigen-defect dispersion and single-prime RH criteria.** Every zero $\rho$ of $\Lambda$ in $0 < \operatorname{Re}\rho < 1$ satisfies $\zeta(\rho) = 0$ and hence $\operatorname{Im}\rho \ne 0$ (`riemannZeta_real_strip_ne_zero`). Conjugation `heckeTruncated_conj` extends `heckeSecondMoment_resonant` from $\operatorname{Im}\rho > 0$ to all strip zeros. Expanding $\big\|T_p \Lambda^Y E_u - (p^u + p^{\bar{u}})\Lambda^Y E_u\big\|^2$ at $u = \rho/2 - 1/2$ and using $2 + 2\operatorname{Re}(q^2) - 4(\operatorname{Re} q)^2 = 2(1 - \|q\|^2)$ for $q = p^u$ cancels the ordinate phase identically, leaving
   $$\int_{\mathcal{D}} \big\|T_p \Lambda^Y E_u - (p^u + p^{\bar{u}})\Lambda^Y E_u\big\|^2 = 2\big(1 - p^{\operatorname{Re}\rho - 1}\big)\int_{\mathcal{D}} \|\Lambda^Y E_u\|^2 \qquad (Y \ge p).$$
   Because $\rho \leftrightarrow 1 - \rho$ splits any off-line pair strictly across $\operatorname{Re}\rho = \frac{1}{2}$, a one-sided bound $\le 2(1 - p^{-1/2})\|\Lambda^Y E_u\|^2$ (or $\ge 2(1 - p^{-1/2})\|\Lambda^Y E_u\|^2$) at any single prime $p$ and single height $Y \ge p$ is equivalent to `RiemannHypothesis`, and $\le 2(1 - p^{-1/2-\beta})\|\Lambda^Y E_u\|^2$ ($\beta \ge 0$) is equivalent to `XiZeroHalfPlaneBound β`.

## No-go closure
- **Exact killing theorem/mechanism:** Extending single-prime resonant Hecke moments to polynomial/$C^*$ combinations in the full commutative Hecke algebra $\{T_n\}_{n \ge 1}$ cannot produce a negative GNS square at an off-line zero ($\operatorname{Re} u \ne -\frac{1}{4}$), because $\mu_n(u)$ is the positive Poisson integral of the real tempered Hecke character $W_{it}(n)$ on $\operatorname{Re} u < 0$.
- **Strongest positive survivor:** The exact cutoff- and ordinate-independent $L^2(\mathcal{D})$ Hecke eigen-defect law $\int_{\mathcal{D}} \|T_p \Lambda^Y E_u - (p^u + p^{\bar{u}})\Lambda^Y E_u\|^2 = 2(1 - p^{\operatorname{Re}\rho - 1})\int_{\mathcal{D}} \|\Lambda^Y E_u\|^2$ valid at every strip zero $\rho$ of $\Lambda$ and every $Y \ge p$, together with the resulting single-prime, single-height one-sided equivalences for `RiemannHypothesis` and `XiZeroHalfPlaneBound`.
- **New insight:** While the resonant expectation functional on the commutative Hecke algebra is indistinguishable from a positive tempered Poisson state, the individual truncated state $\Lambda^Y E_u \in L^2(\mathcal{D})$ fails to be a Hecke eigenstate by an exact phase-free norm defect $2(1 - p^{\operatorname{Re}\rho - 1})$ with no blind primes, whose reflection asymmetry detects any off-line zero from $p = 2$ alone.
- **Status:** Dependency-closed; formalized in `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ResonantHeckePoissonMixtureAndDispersion.lean`.

## Lean

Target module: `formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ResonantHeckePoissonMixtureAndDispersion.lean`.
