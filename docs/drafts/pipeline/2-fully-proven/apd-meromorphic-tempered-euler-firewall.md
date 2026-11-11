# The Meromorphic Tempered Positive Euler-Product Firewall and Left-Strip Pole Obstruction

- **ID:** apd-meromorphic-tempered-euler-firewall
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-1011/fable.md §5.3 · formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheCriticalLineFirewall.lean
- **Statement:** Unconditionally, either `RHTower.AsymptoticAbscissaLaw` holds or for every $\beta \in (\Theta, 1)$ and $\gamma_0 \ne 0$ the truncated shifted-zeta quotient $F_{\mathrm{pos}}(s)$ is meromorphic on $\mathbb{C}$, holomorphic on $\{\operatorname{Re} s > \Theta + \beta - 1\} \setminus \{1\}$ with simple pole of positive residue at $s = 1$, has a convergent distinct-prime Euler product, real nonnegative Ramanujan-bounded multiplicative `LSeries` ($0 \le a_n \ll_\varepsilon n^\varepsilon$), prime-power logarithmic derivative $0 \le \widetilde{\Lambda}(n) \le 2\Lambda(n)$, polynomial vertical bounds on $F_{\mathrm{pos}}$ and $1/F_{\mathrm{pos}}$ right of $\Theta$, violates `HalfPlaneAbscissaLaw` above $\Theta$ with exact off-line zero set $\{\beta \pm i\gamma_0\}$, and has a genuine pole in the left critical strip $0 < \operatorname{Re} s < 1 - \Theta \le \frac{1}{2}$ (and under `RiemannHypothesis`, infinitely many poles on $\operatorname{Re} s = \beta - \frac{1}{2} \in (0, \frac{1}{2})$).

## Goal
Eliminate simultaneously all three escape hatches of existing positive Beurling / rational-prime one-off countermodels (`AnIntegerNormBeurlingOneOff`, `FiniteLayersInEulerProductsOverTheRationalPrimes`, `NonTemperedShiftedZetaPairCountermodel`): exponential vertical growth from rounded Laplace cutoffs, failure of global meromorphicity on $\mathbb{C}$, and repeated-prime / non-Ramanujan coefficients, while isolating left-strip holomorphy across $0 < \operatorname{Re} s < 1 - \Theta_0$ (and the functional equation) as the exact analytic obstruction.

## Gates
- [x] 0 → 1  in-progress: exact algebraic prime-power formula for truncated shifted-zeta quotients and left-strip pole localization
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof `[PROVED HERE]`
- [ ] 2 → 3  formalized: Lean module `GaloisForLFunctions.ArithmeticPositiveDuality.TheMeromorphicTemperedEulerFirewall`, `lake --old env lean` green, `#print axioms` clean

## Paper Proof `[PROVED HERE]`

### 1. Frontier saturation implies `AsymptoticAbscissaLaw`
If $\Theta = \operatorname{zetaZeroAbscissa} = 1$, suppose `rightOf zetaZeroConfig h` were finite for some $h \ge 0$. If $1/2 + h \ge 1$, then every $\rho \in \mathcal{Z}_\zeta$ automatically satisfies $\operatorname{Re}\rho < 1 \le 1/2 + h$. If $1/2 + h < 1 = \Theta$, let $M = \max\{\operatorname{Re}\rho \mid \rho \in \operatorname{rightOf}(\mathcal{Z}_\zeta, h) \cup \{1/2 + h\}\}$; since every $\rho \in \mathcal{Z}_\zeta$ has $\operatorname{Re}\rho < 1$, $M < 1 = \Theta$, contradicting `exists_zetaZero_mem_openStrip_lt_re` at $\max(M, 1/2) < \Theta$. Hence $\Theta = 1 \implies \operatorname{AsymptoticAbscissaLaw}$.

### 2. The meromorphic tempered positive Euler-product model above any zero-free frontier $\Theta_0 \in [\frac{1}{2}, 1)$
Let $\Theta_0 \in [\frac{1}{2}, 1)$ satisfy $\forall z \in \mathbb{C},\; \Theta_0 < \operatorname{Re} z \implies \zeta(z) \ne 0$. Fix $\beta \in (\Theta_0, 1)$, $\gamma_0 \in \mathbb{R} \setminus \{0\}$, set $\rho_0 = \beta + i\gamma_0$, and choose $P_0 \in \mathbb{N}$ such that $P_0 \ge 2$ and $2(P_0 + 1)^{\beta - 1} \le 1$ (explicitly $P_0 = \max(2, \lceil 2^{1/(1 - \beta)} \rceil)$, since $\beta - 1 < 0$).

Define on $\mathbb{C}$:
$$
F_{\mathrm{pos}}(s) := \zeta(s) \cdot \operatorname{invZeta}(s + 1 - \rho_0) \cdot \operatorname{invZeta}(s + 1 - \overline{\rho_0}) \cdot \prod_{\substack{p \le P_0 \\ p \text{ prime}}} \bigl(1 - p^{\rho_0 - 1 - s}\bigr)^{-1} \bigl(1 - p^{\overline{\rho_0} - 1 - s}\bigr)^{-1},
$$
where $\operatorname{invZeta}(w) = (w - 1)\, \operatorname{zetaResidueUnit}(w)^{-1}$ is the entire-unit reciprocal regularization of $1/\zeta$ with $\operatorname{invZeta}(1) = 0$ and $\operatorname{invZeta}'(1) = 1$.

1. **Global meromorphicity and extended right-half-plane holomorphy:**
   `riemannZeta`, `invZeta`, and each $(1 - p^{w - s})^{-1}$ ($p \ge 2$) are meromorphic on $\mathbb{C}$ (`Meromorphic F_pos`). For $\operatorname{Re} s > \Theta_0 + \beta - 1$ (note $\Theta_0 + \beta - 1 < \Theta_0$ since $\beta < 1$):
   - $\operatorname{Re}(s + 1 - \rho_0) = \operatorname{Re} s + 1 - \beta > \Theta_0$ and $\operatorname{Re}(s + 1 - \overline{\rho_0}) > \Theta_0$, so $\operatorname{zetaResidueUnit}$ is nonvanishing at both shifted points, making both `invZeta` factors holomorphic at $s$;
   - since $\Theta_0 \ge \frac{1}{2} > 0$, $\operatorname{Re} s > \Theta_0 + \beta - 1 > \beta - 1$, so $|p^{\rho_0 - 1 - s}| = p^{\beta - 1 - \operatorname{Re} s} < 1$ for every $p \ge 2$, making every finite prime factor holomorphic and nonzero at $s$;
   - `riemannZeta` is holomorphic at every $s \ne 1$.
   Thus $F_{\mathrm{pos}}$ is holomorphic on $\{s \in \mathbb{C} \mid \Theta_0 + \beta - 1 < \operatorname{Re} s\} \setminus \{1\} \supset \{\operatorname{Re} s > \Theta_0\} \setminus \{1\}$.

2. **Simple pole at $s = 1$ with positive residue:**
   Since $\gamma_0 \ne 0$, $2 - \rho_0 \ne 1$ and $\operatorname{Re}(2 - \rho_0) = 2 - \beta > 1$, so the cofactor $C_{\mathrm{pos}}(s) = F_{\mathrm{pos}}(s)/\zeta(s)$ is continuous at $s = 1$ with
   $$
   C_{\mathrm{pos}}(1) = |\zeta(2 - \rho_0)|^{-2} \prod_{\substack{p \le P_0 \\ p \text{ prime}}} |1 - p^{\rho_0 - 2}|^{-2} > 0,
   $$
   hence $\lim_{s \to 1, s \ne 1} (s - 1) F_{\mathrm{pos}}(s) = C_{\mathrm{pos}}(1) > 0$.

3. **Exact finite off-line zero set in $\{\operatorname{Re} s > \Theta_0\} \setminus \{1\}$:**
   For $\operatorname{Re} s > \Theta_0$ and $s \ne 1$, $\zeta(s) \ne 0$, every finite factor $(1 - p^{w - s})^{-1}$ is nonzero, and $\operatorname{zetaResidueUnit}(s + 1 - \rho_0) \ne 0$, $\operatorname{zetaResidueUnit}(s + 1 - \overline{\rho_0}) \ne 0$. Hence
   $$
   F_{\mathrm{pos}}(s) = 0 \iff (s + 1 - \rho_0 = 1 \text{ or } s + 1 - \overline{\rho_0} = 1) \iff s \in \{\rho_0, \overline{\rho_0}\}.
   $$
   In particular, $\{s \mid \Theta_0 < \operatorname{Re} s, s \ne 1, F_{\mathrm{pos}}(s) = 0\} = \{\rho_0, \overline{\rho_0}\}$ is finite and nonempty, so `¬ HalfPlaneAbscissaLaw (F_pos_clearedPole) Θ_0` (and directly `¬ HalfPlaneAbscissaLaw` on $\operatorname{Re} s > \Theta_0$ away from the pole at $1$).

4. **Multiplicative `LSeries`, Ramanujan bound, distinct-prime Euler product, and $0 \le \widetilde{\Lambda}(n) \le 2\Lambda(n)$:**
   Define `muTwist P₀ w : ArithmeticFunction ℂ` by `muTwist P₀ w n = μ(n) n^w` when $n \ge 1$ has all prime factors $> P_0$, and $0$ otherwise. `muTwist P₀ w` is multiplicative and satisfies $\lVert\operatorname{muTwist}_{P_0, w}(n)\rVert \le 1$ for $\operatorname{Re} w = \beta - 1 < 0$. Set $A_{\mathrm{pos}} = \zeta_{\mathrm{arith}} * \operatorname{muTwist}_{P_0, \rho_0 - 1} * \operatorname{muTwist}_{P_0, \overline{\rho_0} - 1}$.
   - $A_{\mathrm{pos}}$ is multiplicative, and at prime powers $p^k$ ($k \ge 1$):
     - if $p \le P_0$: $A_{\mathrm{pos}}(p^k) = 1$;
     - if $p > P_0$: $A_{\mathrm{pos}}(p) = 1 - p^{\rho_0 - 1} - p^{\overline{\rho_0} - 1} = 1 - 2 p^{\beta - 1}\cos(\gamma_0 \log p) \in [0, 2]$, and for $k \ge 2$, $A_{\mathrm{pos}}(p^k) = |1 - p^{\rho_0 - 1}|^2 \in [0, \frac{9}{4}]$.
   - By `multiplicative_factorization`, every $A_{\mathrm{pos}}(n)$ is a nonnegative real number, $A_{\mathrm{pos}}(1) = 1$, and for every $\varepsilon > 0$ only finitely many primes satisfy $p^\varepsilon < \frac{9}{4}$, giving $0 \le A_{\mathrm{pos}}(n) \le C_\varepsilon n^\varepsilon$ for all $n \ge 1$.
   - On $\operatorname{Re} s > 1$, `LSeries A_pos s = F_pos s` and the distinct-prime Euler product $\prod_{p : \mathrm{Primes}} E_p(s)$ converges (`HasProd`) to $F_{\mathrm{pos}}(s)$, where $E_p(s) = (1 - p^{-s})^{-1}$ for $p \le P_0$ and $E_p(s) = (1 - p^{\rho_0 - 1 - s})(1 - p^{\overline{\rho_0} - 1 - s})(1 - p^{-s})^{-1}$ for $p > P_0$.
   - The logarithmic derivative satisfies $-F_{\mathrm{pos}}'(s)/F_{\mathrm{pos}}(s) = \operatorname{LSeries}(\widetilde{\Lambda}, s)$ on $\operatorname{Re} s > 1$, where $\widetilde{\Lambda}(n) = \Lambda(n)$ when all prime factors of $n$ are $\le P_0$, $\widetilde{\Lambda}(p^k) = \Lambda(p^k)(1 - 2 p^{k(\beta - 1)}\cos(k\gamma_0 \log p))$ for $p > P_0$, and $0$ otherwise, satisfying $0 \le \widetilde{\Lambda}(n) \le 2\Lambda(n)$ for all $n \in \mathbb{N}$.

5. **Polynomial vertical bounds on $F_{\mathrm{pos}}$ and $1/F_{\mathrm{pos}}$ right of $\Theta_0$:**
   On any closed vertical strip $\Theta_0 + \delta \le \operatorname{Re} s \le d$ with $|\operatorname{Im} s| \ge |\gamma_0| + 2$:
   - $\zeta(s)$ satisfies the convexity polynomial bound `exists_bound_norm_riemannZeta_strip`;
   - $1/\zeta(s)$, $\operatorname{invZeta}(s + 1 - \rho_0)$, $\operatorname{invZeta}(s + 1 - \overline{\rho_0})$, and their reciprocals satisfy polynomial/subpolynomial bounds via `exists_invZeta_shift_data_of_zeroFree` and `exists_bound_norm_riemannZeta_strip`;
   - the finite prime product and its reciprocal are bounded above and below by positive constants uniformly in $\operatorname{Im} s$ since $\operatorname{Re} s > \beta - 1$.

6. **Left-strip pole obstruction (`exists_pole_in_left_strip`, `infinite_poles_under_rh`):**
   Assume $\Theta_0 = \Theta = \operatorname{zetaZeroAbscissa} < 1$. Set $\eta = \frac{1}{2}(1 - \beta) > 0$. By `exists_zetaZero_mem_openStrip_lt_re`, there is a zero $\rho_*$ of $\zeta$ with $\Theta - \eta < \operatorname{Re}\rho_* \le \Theta$ and $\operatorname{Re}\rho_* < 1$ (note $\Theta - \eta = \Theta - \frac{1-\beta}{2} > \frac{1}{2} - \frac{1}{4} = \frac{1}{4} > 0$). By `riemannZeta_one_sub_eq_zero_of_mem_openStrip`, $w_* = 1 - \rho_*$ satisfies $\zeta(w_*) = 0$ and $1 - \Theta \le \operatorname{Re} w_* < 1 - \Theta + \eta < \frac{3}{4} < 1$.
   At $s_* := w_* - 1 + \rho_0$,
   $$
   0 < \beta - \Theta \le \operatorname{Re} s_* < 1 - \Theta - \tfrac{1 - \beta}{2} < 1 - \Theta \le \tfrac{1}{2}.
   $$
   Every zero $z$ of $\zeta$ in $0 < \operatorname{Re} z < 1$ satisfies $\operatorname{Re} z \ge 1 - \Theta$ (by functional-equation reflection and `re_le_zetaZeroAbscissa`), so $\zeta(s_*) \ne 0$. Meanwhile $s_* + 1 - \rho_0 = w_* \ne 1$ has $\zeta(w_*) = 0$, while $s_* + 1 - \overline{\rho_0} = w_* + 2i\gamma_0 \ne 1$, so $\lVert\operatorname{invZeta}(s + 1 - \rho_0)\,\operatorname{invZeta}(s + 1 - \overline{\rho_0})\rVert \to +\infty$ as $s \to s_*$ ($s \ne s_*$), forcing $\lVert F_{\mathrm{pos}}(s)\rVert \to +\infty$ on $\mathcal{N}_{\ne}(s_*)$. Under `RiemannHypothesis` ($\Theta = \frac{1}{2}$), every critical-line zero $w = \frac{1}{2} + i\gamma$ of $\zeta$ (`exists_Xi_zero_gt`) yields such a pole $s = (\beta - \frac{1}{2}) + i(\gamma + \gamma_0)$ on $\operatorname{Re} s = \beta - \frac{1}{2} \in (0, \frac{1}{2})$ at arbitrarily large heights.

## Log
- 2026-11-11 — created and proved in `2-fully-proven`
