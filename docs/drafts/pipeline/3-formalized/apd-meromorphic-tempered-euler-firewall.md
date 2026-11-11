# The Meromorphic Tempered Positive Euler-Product Firewall and Left-Strip Pole Obstruction

- **ID:** apd-meromorphic-tempered-euler-firewall
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1011/fable.md §5.3 · formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheCriticalLineFirewall.lean
- **Lean Module:** `GaloisForLFunctions.ArithmeticPositiveDuality.TheMeromorphicTemperedEulerFirewall`
- **Lean Declarations:**
  - `GaloisForLFunctions.ArithmeticPositiveDuality.asymptoticAbscissaLaw_of_zetaZeroAbscissa_eq_one`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.posCutoff`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.posTruncatedZeta`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.posTruncatedCoeff`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.posTruncatedVonMangoldt`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.hasProd_and_LSeries_posTruncatedZeta`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.neg_logDeriv_posTruncatedZeta_eq_LSeries`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.meromorphicOn_posTruncatedZeta`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.differentiableOn_posTruncatedZeta`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.exists_pos_residue_posTruncatedZeta_one`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.zeroSet_posTruncatedZeta_eq_pair`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.not_halfPlaneAbscissaLaw_posTruncatedZeta`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.exists_poly_bounds_posTruncatedZeta`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.exists_left_strip_pole_posTruncatedZeta`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.exists_left_strip_pole_above_of_riemannHypothesis`
  - `GaloisForLFunctions.ArithmeticPositiveDuality.asymptoticAbscissaLaw_or_exists_meromorphic_tempered_euler_oneOff`
- **Statement:** Unconditionally, either `RHTower.AsymptoticAbscissaLaw` holds or $\Theta = \operatorname{zetaZeroAbscissa} < 1$ and for every $\beta \in (\Theta, 1)$ and $\gamma_0 \ne 0$ the truncated shifted-zeta quotient $F_{\mathrm{pos}}(s)$ is meromorphic on $\mathbb{C}$, holomorphic on $\{\operatorname{Re} s > \Theta + \beta - 1\} \setminus \{1\}$ with simple pole of positive residue at $s = 1$, has a convergent distinct-prime Euler product, real nonnegative Ramanujan-bounded multiplicative `LSeries` ($0 \le a_n \le C_\varepsilon n^\varepsilon$), prime-power logarithmic derivative $0 \le \widetilde{\Lambda}(n) \le 2\Lambda(n)$, polynomial vertical bounds on $F_{\mathrm{pos}}$ and $1/F_{\mathrm{pos}}$ right of $\Theta$, violates `HalfPlaneAbscissaLaw` above $\Theta$ with exact off-line zero set $\{\beta \pm i\gamma_0\}$, and has a genuine pole strictly inside the left critical strip $0 < \operatorname{Re} s < 1 - \Theta \le \frac{1}{2}$ (and under `RiemannHypothesis`, infinitely many poles on $\operatorname{Re} s = \beta - \frac{1}{2} \in (0, \frac{1}{2})$).

## Goal
Eliminate simultaneously all three escape hatches of existing positive Beurling and rational-prime one-off countermodels (`AnIntegerNormBeurlingOneOff`, `FiniteLayersInEulerProductsOverTheRationalPrimes`, `NonTemperedShiftedZetaPairCountermodel`): exponential vertical growth from rounded Laplace cutoffs, failure of global meromorphicity on $\mathbb{C}$, and repeated-prime / non-Ramanujan coefficients, while isolating left-strip holomorphy across $0 < \operatorname{Re} s < 1 - \Theta_0$ (and functional-equation symmetry) as the exact analytic obstruction.

## Gates
- [x] 0 → 1  in-progress: exact algebraic prime-power formula for truncated shifted-zeta quotients and left-strip pole localization
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof `[PROVED HERE]`
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.ArithmeticPositiveDuality.TheMeromorphicTemperedEulerFirewall`, `lake --old env lean` green, `#print axioms` `[propext, Classical.choice, Quot.sound]`

## Paper Proof `[PROVED HERE]`

### 1. Frontier saturation implies `AsymptoticAbscissaLaw`
If $\Theta = \operatorname{zetaZeroAbscissa} = 1$ and `¬ AsymptoticAbscissaLaw`, `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` produces $\beta_* < 1$ such that $\zeta(z) \ne 0$ for all $\operatorname{Re} z > \beta_*$. Then $\Theta = \sup\{\operatorname{Re}\rho \mid \rho \in \mathcal{Z}_\zeta\} \le \beta_* < 1$, contradicting $\Theta = 1$. Hence $\Theta = 1 \implies \operatorname{AsymptoticAbscissaLaw}$.

### 2. The meromorphic tempered positive Euler-product model above any zero-free frontier $\Theta_0 \in [\frac{1}{2}, 1)$
Let $\Theta_0 \in [\frac{1}{2}, 1)$ satisfy $\forall z \in \mathbb{C},\; \Theta_0 < \operatorname{Re} z \implies \zeta(z) \ne 0$. Fix $\beta \in (\Theta_0, 1)$, $\gamma_0 \in \mathbb{R} \setminus \{0\}$, set $\rho_0 = \beta + i\gamma_0$, and define $P_0 = \max(2, \lceil 2^{1/(1 - \beta)} \rceil) \in \mathbb{N}$, so $P_0 \ge 2$ and $2(P_0 + 1)^{\beta - 1} \le 1$.

Define on $\mathbb{C}$:
$$
F_{\mathrm{pos}}(s) := \zeta(s) \cdot \operatorname{invZeta}(s + 1 - \rho_0) \cdot \operatorname{invZeta}(s + 1 - \overline{\rho_0}) \cdot \prod_{\substack{p \le P_0 \\ p \text{ prime}}} \bigl(1 - p^{\rho_0 - 1 - s}\bigr)^{-1} \bigl(1 - p^{\overline{\rho_0} - 1 - s}\bigr)^{-1},
$$
where $\operatorname{invZeta}(w) = (w - 1)\, \operatorname{zetaResidueUnit}(w)^{-1}$ is the entire-unit reciprocal regularization of $1/\zeta$ with $\operatorname{invZeta}(1) = 0$ and $\operatorname{invZeta}'(1) = 1$.

1. **Global meromorphicity and extended right-half-plane holomorphy:**
   `riemannZeta`, `invZeta`, and each $(1 - p^{w - s})^{-1}$ ($p \ge 2$) are meromorphic on $\mathbb{C}$ (`MeromorphicOn F_pos univ`). For $\operatorname{Re} s > \Theta_0 + \beta - 1$ (strictly crossing $\Theta_0$ to the left since $\beta < 1$):
   - $\operatorname{Re}(s + 1 - \rho_0) = \operatorname{Re} s + 1 - \beta > \Theta_0$ and $\operatorname{Re}(s + 1 - \overline{\rho_0}) > \Theta_0$, so $\operatorname{zetaResidueUnit}$ is nonvanishing at both shifted points, making both `invZeta` factors holomorphic at $s$;
   - since $\Theta_0 \ge \frac{1}{2} > 0$, $\operatorname{Re} s > \Theta_0 + \beta - 1 > \beta - 1$, so $|p^{\rho_0 - 1 - s}| = p^{\beta - 1 - \operatorname{Re} s} < 1$ for every $p \ge 2$, making every finite prime factor holomorphic and nonzero at $s$;
   - `riemannZeta` is holomorphic at every $s \ne 1$.
   Thus $F_{\mathrm{pos}}$ is holomorphic on $\{s \in \mathbb{C} \mid \Theta_0 + \beta - 1 < \operatorname{Re} s \text{ and } s \ne 1\}$.

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
   Since $\zeta(1) \ne 0$ and $C_{\mathrm{pos}}(1) > 0$, $F_{\mathrm{pos}}(1) \ne 0$ as well, so $\{s \in \mathbb{C} \mid \Theta_0 < \operatorname{Re} s \text{ and } F_{\mathrm{pos}}(s) = 0\} = \{\rho_0, \overline{\rho_0}\}$ is finite and nonempty, proving `¬ HalfPlaneAbscissaLaw F_pos Θ_0`.

4. **Multiplicative `LSeries`, Ramanujan bound, distinct-prime Euler product, and $0 \le \widetilde{\Lambda}(n) \le 2\Lambda(n)$:**
   Define `posTruncatedCoeff P₀ β γ₀ : ArithmeticFunction ℝ` multiplicatively via local prime-power values $a(p^k) = 1$ for $p \le P_0$, $a(p) = 1 - 2 p^{\beta - 1}\cos(\gamma_0 \log p) \in [0, 2]$ for $p > P_0$, and $a(p^k) = \lvert 1 - p^{\rho_0 - 1}\rvert^2 \in [0, 4]$ for $p > P_0$, $k \ge 2$.
   - Every $a(n) \ge 0$, $a(1) = 1$, and for every $\varepsilon > 0$ only finitely many primes satisfy $p^\varepsilon < 4$, yielding $0 \le a(n) \le C_\varepsilon n^\varepsilon$ for all $n \ge 1$.
   - On $\operatorname{Re} s > 1$, `LSeries a s = F_pos s` and the distinct-prime Euler product $\prod_{q : \mathrm{Nat.Primes}} E_q(s)$ converges (`HasProd`) to $F_{\mathrm{pos}}(s)$, where $E_q(s) = (1 - q^{-s})^{-1}$ for $q \le P_0$ and $E_q(s) = (1 - q^{-s})^{-1}(1 - q^{\rho_0 - 1 - s})(1 - q^{\overline{\rho_0} - 1 - s})$ for $q > P_0$.
   - On $\operatorname{Re} s > 1$, $-F_{\mathrm{pos}}'(s)/F_{\mathrm{pos}}(s) = \operatorname{LSeries}(\widetilde{\Lambda}, s)$ where $\widetilde{\Lambda}(n) = \Lambda(n)$ when $n.\mathrm{minFac} \le P_0$ and $\widetilde{\Lambda}(n) = \Lambda(n)(1 - 2 n^{\beta - 1}\cos(\gamma_0 \log n))$ otherwise, satisfying $0 \le \widetilde{\Lambda}(n) \le 2\Lambda(n)$ for all $n \in \mathbb{N}$.

5. **Polynomial vertical bounds on $F_{\mathrm{pos}}$ and $1/F_{\mathrm{pos}}$ right of $\Theta_0$:**
   On any closed vertical strip $\Theta_0 + \delta \le \operatorname{Re} s \le d$ with $|\operatorname{Im} s| \ge |\gamma_0| + 6$:
   - $\zeta(s)$, $\zeta(s + 1 - \rho_0)$, and $\zeta(s + 1 - \overline{\rho_0})$ satisfy convexity polynomial bounds (`exists_bound_norm_riemannZeta_strip`);
   - $1/\zeta(s)$, $\operatorname{invZeta}(s + 1 - \rho_0)$, and $\operatorname{invZeta}(s + 1 - \overline{\rho_0})$ satisfy polynomial bounds via `exists_invZeta_shift_data_of_zeroFree`;
   - the finite prime product and its reciprocal are bounded above by positive constants uniformly in $\operatorname{Im} s$ since $\operatorname{Re} s > \beta - 1$.

6. **Left-strip pole obstruction (`exists_left_strip_pole_posTruncatedZeta`, `exists_left_strip_pole_above_of_riemannHypothesis`):**
   Assume $\Theta_0 = \Theta = \operatorname{zetaZeroAbscissa} < 1$. By `exists_zetaZero_mem_openStrip_lt_re` at $b = \Theta - \frac{1 - \beta}{2} \in (\frac{1}{4}, \Theta)$, there exists a strip zero $\rho_1$ of $\zeta$ with $\Theta - \frac{1 - \beta}{2} < \operatorname{Re}\rho_1 \le \Theta < 1$. Set $s_0 := \rho_0 - \rho_1$. Then
   $$
   0 < \beta - \Theta \le \operatorname{Re} s_0 < \beta - \Theta + \tfrac{1 - \beta}{2} < 1 - \Theta \le \tfrac{1}{2}.
   $$
   If $\zeta(s_0) = 0$, functional-equation reflection (`riemannZeta_one_sub_eq_zero_of_mem_openStrip`) gives $\zeta(1 - s_0) = 0$ with $\operatorname{Re}(1 - s_0) > \Theta$, contradicting `riemannZeta_ne_zero_of_zetaZeroAbscissa_lt`. Hence $\zeta(s_0) \ne 0$. Meanwhile $s_0 + 1 - \rho_0 = 1 - \rho_1 \ne 1$ satisfies $\zeta(1 - \rho_1) = 0$ by reflection, while $s_0 + 1 - \overline{\rho_0} \ne 1$ and $\operatorname{Re}(\rho_0 - 1 - s_0) = \operatorname{Re}\rho_1 - 1 < 0$, so $\lVert F_{\mathrm{pos}}(s)\rVert \to +\infty$ on $\mathcal{N}_{\ne}(s_0)$ and $F_{\mathrm{pos}}$ is not analytic at $s_0$. Under `RiemannHypothesis`, Hardy's critical-line zeros $w_0 = \frac{1}{2} + it$ (`exists_Xi_zero_gt`) produce genuine poles $s_0 = w_0 - 1 + \rho_0$ along $\operatorname{Re} s = \beta - \frac{1}{2} \in (0, \frac{1}{2})$ with $|s_0.\mathrm{im}| > T$ for every $T \in \mathbb{R}$.

## Log
- 2026-11-11 — created, proved, and formalized in `GaloisForLFunctions.ArithmeticPositiveDuality.TheMeromorphicTemperedEulerFirewall`
