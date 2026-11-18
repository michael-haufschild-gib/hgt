# Structural Laws, Pole Isolations, Probe Decompositions, and Recurrence Obstructions of a Single Off-Line Quartet

- **ID:** zfc-ecs-elt-single-quartet-insights
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1811/obstacles-summary.md` §2.17
- **Statement:** Unconditional structural theorems on `HasSingleOffLineQuartet ρ₀`, Euler dilation pole isolation, Eisenstein zero-scattering duals, translated-probe Laplace-tent and pole-neutral triple decompositions of Weil's form, self-return confinement, `N`-smooth alternating Euler-product Rouché domination, and universal two-prime dilation spanning.

## Goal
Establish six self-contained families of unconditional theorems governing a hypothetical single off-line quartet $Q(\rho_0) = \{\rho_0, \bar\rho_0, 1 - \rho_0, 1 - \bar\rho_0\}$ ($\frac12 < \operatorname{Re}\rho_0 < 1$) of $\zeta(s)$ and the analytic/arithmetic observables tested against it.

## Gates
- [x] 0 → 1  in-progress: well-posed, unconditional mathematical statements
- [x] 1 → 2  fully-proven: complete paper proofs (`[PROVED HERE]`), zero open dependencies
- [ ] 2 → 3  formalized: Lean 4 modules in `ZeroForcingCalculus`, `ExclusionOfTheCriticalState/Index`, and `ExceptionalLayerTheory`

## Paper Proofs (`[PROVED HERE]`)

### 1. Affine-Reflected Nonvanishing, Half-Quartet Pole Isolation, and Eisenstein Dual Modes
Assume `HasSingleOffLineQuartet ρ₀`, so $\frac12 < \beta := \operatorname{Re}\rho_0 < 1$, $\gamma := \operatorname{Im}\rho_0$ satisfies $|\gamma| > 4$, and $\{\rho \in (0,1) + i\mathbb{R} : \zeta(\rho)=0,\ \operatorname{Re}\rho \neq \frac12\} = Q(\rho_0)$.

1. **Affine-reflected and integer-shifted nonvanishing (`[PROVED HERE]`).**
   - For every integer $k \ge 2$ and $\rho \in Q(\rho_0)$, let $u_k(\rho) := 1 - \rho/k$ and $v_k(\rho) := ((k-1) + \rho)/k$. Since $0 < \operatorname{Re}\rho < 1$ and $k \ge 2$, both $u_k(\rho)$ and $v_k(\rho)$ have real part in $(1 - 1/k, 1) \subseteq (1/2, 1)$ and imaginary part of modulus $|\gamma|/k < |\gamma|$. Any zero there would be off-line, hence in $Q(\rho_0)$, contradicting $|\operatorname{Im}| = |\gamma|$. Thus $\zeta(1 - \rho/k) \neq 0$ and $\zeta(((k-1)+\rho)/k) \neq 0$.
   - For $\rho \in Q(\rho_0)$, $\operatorname{Re}(2 - \rho) = 2 - \operatorname{Re}\rho > 1$, so $\zeta(2 - \rho) \neq 0$ and $\xi(2 - \rho) \neq 0$. By functional symmetry $\xi(\rho - 1) = \xi(2 - \rho) \neq 0$. Since $\operatorname{Im}(\rho - 1) = \operatorname{Im}\rho \neq 0$, $\rho - 1$ is neither $1$ nor a negative even integer nor $0$, where $\Gamma_{\mathbb{R}}(s)$ and $s(s-1)$ are finite and nonzero; hence $\zeta(\rho - 1) \neq 0$.

2. **Exact half-quartet pole isolation of `dilatedPowerQuotient k m` (`[PROVED HERE]`).**
   For $k \ge 2$ and $m \in \mathbb{N}$, write $F_{k,m}(s) = ((s-1)\zeta(s))^m / \zeta(ks) = u(s)^m (ks - 1) / u(ks)$ on punctured neighborhoods via $u(z) = (z-1)\zeta(z)$ ($u(1)=1$). If $\operatorname{Re} s > \frac{1}{2k}$, then $\operatorname{Re}(ks) > \frac12$; $u(ks) = 0$ iff $ks$ is a zero of $\zeta$ with $\operatorname{Re}(ks) > \frac12$, i.e., $ks \in \{\rho_0, \bar\rho_0\}$ ($s \in \{\rho_0/k, \bar\rho_0/k\}$). At both points $\zeta(s) \neq 0$ and $s \neq 1$, so $\operatorname{ord}_s F_{k,m} = -\operatorname{ord}_{\rho_0}\zeta < 0$. Thus
   $$\{s \in \mathbb{C} : \operatorname{Re} s > \tfrac{1}{2k} \ \wedge\ \operatorname{ord}_s F_{k,m} < 0\} = \{\rho_0/k, \bar\rho_0/k\},$$
   while the reflected pair $\{(1-\rho_0)/k, (1-\bar\rho_0)/k\}$ lies strictly in $\{0 < \operatorname{Re} s < \frac{1}{2k}\}$ with the same pole order $-\operatorname{ord}_{\rho_0}\zeta < 0$.

3. **Eisenstein zero-scattering dual modes (`[PROVED HERE]`).**
   Set $w_- := 1 - \rho_0/2$ and $w_+ := (1 + \rho_0)/2$, corresponding to $2w_- - 1 = 1 - \rho_0$ and $2w_+ - 1 = \rho_0$ in $\phi(w) = \xi(2w-1)/\xi(2w)$. Since $\frac12 < \beta < 1$:
   $$\tfrac12 < \operatorname{Re} w_- = 1 - \tfrac{\beta}{2} < \tfrac34 < \operatorname{Re} w_+ = \tfrac{1+\beta}{2} < 1.$$
   Moreover $\xi(2w_\pm - 1) = 0$, whereas $\operatorname{Re}(2w_-) = 2 - \beta > 1$ and $\operatorname{Re}(2w_+) = 1 + \beta > \frac32 > 1$ give $\xi(2w_\pm) \neq 0$, and Part 1 ($k = 2$) gives $\zeta(w_\pm) \neq 0$. Their hyperbolic Laplace spectral parameters satisfy $\operatorname{Im}(w_-(1-w_-)) = \frac12(1-\beta)\gamma \neq 0$, $\operatorname{Im}(w_+(1-w_+)) = -\frac12\beta\gamma \neq 0$, and $w_-(1-w_-) - w_+(1-w_+) = \frac{2\rho_0 - 1}{4} \neq 0$.

### 2. Translated-Probe Laplace-Tent Decomposition and Pole-Neutral Three-Probe Profiles
Let $e_p(u) = \mathbf{1}_{(-\infty,0)}(u) e^{pu}$ (`probe p`) and $\tau_R f(u) = f(u+R)$ (`shiftProfile f R`).

1. **Symmetric Laplace tent overlap and horizon split (`[PROVED HERE]`).**
   For $p > 0$ and $L, R \ge 0$, $e_p(t) e_p(t - L + R) = e^{p(R-L)} e^{2pt}$ on $t < \min(0, L - R)$ and $0$ otherwise. Integrating from $-\infty$ to $\min(0, L-R)$ yields $\frac{1}{2p} e^{p(R-L) + 2p\min(0, L-R)} = \frac{e^{-p|L-R|}}{2p}$. Similarly, since $L + R \ge 0$, $\min(0, -L-R) = -L-R$, giving $\int_{\mathbb{R}} e_p(t) e_p(t + L + R)\,dt = \frac{e^{-p(L+R)}}{2p}$. Consequently, for $p > \frac12$ and $R \ge 0$:
   $$\operatorname{primePairTerm}(e_p, \tau_R e_p, n) = \frac{\Lambda_{\mathrm{atom}}(n)}{2p}\bigl(e^{-p|\log n - R|} + e^{-p(\log n + R)}\bigr) \ge 0,$$
   $\operatorname{primeMixedForm}(\tau_R e_p, e_p) = \operatorname{primeMixedForm}(e_p, \tau_R e_p) \ge 0$, and splitting $n \ge 1$ at $N = \lfloor e^R \rfloor_+$ decomposes $\operatorname{primeMixedForm}(e_p, \tau_R e_p)$ into
   $$\frac{e^{-pR}}{2p}\sum_{n=1}^{\lfloor e^R\rfloor_+} \Lambda(n) n^{p - 1/2} + \frac{e^{pR}}{2p}\sum_{k=0}^\infty \frac{\Lambda(k + \lfloor e^R\rfloor_+ + 1)}{(k + \lfloor e^R\rfloor_+ + 1)^{1/2 + p}} + \frac{e^{-pR}}{2p}\sum_{n=1}^\infty \frac{\Lambda(n)}{n^{1/2 + p}}.$$

2. **Translated pole identity, Gamma majorant, $O(e^{R/2})$ upper ceiling, and nonnegative two-probe divergence (`[PROVED HERE]`).**
   - For $p > \frac12$ and $R \in \mathbb{R}$, expanding `coshHalfMoment_shiftProfile` and `sinhHalfMoment_shiftProfile` on $e_p$ gives $C(e_p) = \frac{p}{p^2 - 1/4}$, $S(e_p) = \frac{-1/2}{p^2 - 1/4}$, and
     $$2 C(e_p) C(\tau_R e_p) - 2 S(e_p) S(\tau_R e_p) = \frac{2\cosh(R/2)}{p^2 - 1/4} = \frac{e^{R/2} + e^{-R/2}}{p^2 - 1/4}.$$
   - For $p > 0$ and $R, r \in \mathbb{R}$, $|\operatorname{gammaFourierPair}(e_p, \tau_R e_p, r)| \le \| \widehat{e_p}(r)\| \|\widehat{\tau_R e_p}(r)\| = \frac{1}{p^2 + r^2}$, whence $|\operatorname{gammaMixedForm}(e_p, \tau_R e_p)| \le \frac{1}{2\pi p}\int_{\mathbb{R}} \frac{p}{p^2 + r^2}|\gamma_{\mathrm{bracket}}(r)|\,dr < \infty$ uniformly in $R$.
   - Since $\operatorname{primeMixedForm}(e_p, \tau_R e_p) \ge 0$, for $p > \frac12$ and $R \ge 0$, $\operatorname{bareMixedEnergy}(e_p, \tau_R e_p) \le \Gamma_{\max}(p) + \frac{2 e^{R/2}}{p^2 - 1/4}$.
   - Under `HasSingleOffLineQuartet ρ₀`, for $p > 4$ and $G_R := e_p + \tau_R e_p \ge 0$ ($R \ge 0$), bilinearity and joint shift invariance give $\operatorname{bareMixedEnergy}(G_R, G_R) = 2\operatorname{bareMixedEnergy}(e_p, e_p) + 2\operatorname{bareMixedEnergy}(e_p, \tau_R e_p)$, which takes values $> M$ and $< -M$ for every $M \in \mathbb{R}$ as $R \ge 0$ varies.

3. **Explicit pole-neutral three-probe profiles (`[PROVED HERE]`).**
   For $4 < p < q < r$, define the Lagrange coefficients of $f(t) = t^2 - \frac14$ at $(-p, -q, -r)$:
   $$c_1 = \frac{p^2 - 1/4}{(p-q)(p-r)}, \quad c_2 = \frac{q^2 - 1/4}{(q-p)(q-r)}, \quad c_3 = \frac{r^2 - 1/4}{(r-p)(r-q)},$$
   and $H_{p,q,r} := c_1 e_p + c_2 e_q + c_3 e_r \in \mathrm{CriticalHalfLineEnergyDomain}$. Partial fractions give $c_1 + c_2 + c_3 = 1$ and, for $\operatorname{Re} w > -p$,
   $$\mathcal{L} H_{p,q,r}(w) = \frac{w^2 - 1/4}{(p + w)(q + w)(r + w)}.$$
   At $w = \pm \frac12$ the numerator vanishes, so $C(\tau_R H) = S(\tau_R H) = 0$ for all $R \in \mathbb{R}$, completely eliminating the pole term from $\operatorname{bareMixedEnergy}(H, \tau_R H)$. Since $\int_{-\infty}^0 H(u) e^{u/2}\,du = 0$ while $\lim_{u \to 0^-} H(u) = 1 > 0$, $H_{p,q,r}$ necessarily changes sign on $(-\infty, 0)$. Because $\mathcal{L} H(\rho_0 - \frac12) \mathcal{L} H(\frac12 - \bar\rho_0) \neq 0$ ($\frac12 < \operatorname{Re}\rho_0 < 1$, $\operatorname{Im}\rho_0 \neq 0$), under `HasSingleOffLineQuartet ρ₀` the pure prime pairing $\frac12(\operatorname{primeMixedForm}(H, \tau_R H) + \operatorname{primeMixedForm}(\tau_R H, H))$ is unbounded both above and below on $R \ge 0$, whereas under `RiemannHypothesis` it is uniformly bounded on $R \ge 0$; hence any one-sided bound (above or below) on $R \ge 0$ for a single triple $4 < p < q < r$ rules out all single off-line quartets.

### 3. Self-Return Confinement, Smooth Alternating Euler Tail Domination, Universal Two-Prime Dilations, and Fractional-Part Identities

1. **Compact self-return confinement and failure of weak recurrence (`[PROVED HERE]`).**
   Under `HasSingleOffLineQuartet ρ₀`, `FiniteOffLine` holds while `¬ RiemannHypothesis` holds; by `riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent`, `¬ ZetaZeroDiscWeaklyRecurrent` (and `¬ ZetaWeaklyRecurrent`). Quantitatively, for $0 < r < \min(\operatorname{Re}\rho_0 - \frac12, 1 - \operatorname{Re}\rho_0)$, $d := \operatorname{zetaNonvanishingDistance}(\rho_0, r) > 0$, and for every $\varepsilon < d$ and $\tau \in \operatorname{zetaReturnSet}(\overline{B}(\rho_0, r), \varepsilon)$, `exists_zero_of_mem_zetaReturnSet_of_lt_distance` furnishes $z \in \overline{B}(\rho_0, r)$ with $\zeta(z + i\tau) = 0$. Since $\operatorname{Re}(z + i\tau) \ge \operatorname{Re}\rho_0 - r > \frac12$ and $\operatorname{Re}(z + i\tau) \le \operatorname{Re}\rho_0 + r < 1$, single-quartet rigidity forces $z + i\tau \in \{\rho_0, \bar\rho_0\}$, hence $|\tau| \le r$ or $|\tau + 2\operatorname{Im}\rho_0| \le r$; in particular $|\tau| \le 2|\operatorname{Im}\rho_0| + r$.

2. **`N`-smooth alternating Euler-product nonvanishing and Rouché tail floor (`[PROVED HERE]`).**
   For $N \ge 2$ and any multiplicative $\omega : \mathbb{N} \to^* \mathbb{C}$ with $|\omega(p)| = 1$ for primes $p \le N$, define on $\operatorname{Re} s > 0$:
   $$\widetilde{E}_N(s;\omega) := (1 - 2^{1-s}\omega(2)) \prod_{\substack{p \le N \\ p\text{ prime}}} (1 - p^{-s}\omega(p))^{-1}.$$
   Since $|p^{-s}\omega(p)| = p^{-\operatorname{Re} s} < 1$ on $\operatorname{Re} s > 0$, the product over $p \le N$ expands absolutely over $(N+1)$-smooth integers as $\sum_{n\text{ }(N+1)\text{-smooth}} \omega(n) n^{-s}$; multiplying by $1 - 2\cdot 2^{-s}\omega(2)$ flips the sign of even $(N+1)$-smooth integers ($2^a m$ with $a \ge 1$, $m$ odd: $1 - 2 = -1 = (-1)^{2^a m - 1}$) and preserves odd ones ($1 = (-1)^{m-1}$), giving
   $$\widetilde{E}_N(s;\omega) = \sum_{\substack{n \ge 1 \\ P^+(n) \le N}} (-1)^{n-1} \omega(n) n^{-s} = A_N(s;\omega) + T_N^{\mathrm{sm}}(s;\omega),$$
   where $A_N(s;\omega) = \sum_{n=1}^N (-1)^{n-1}\omega(n)n^{-s}$ (since every $1 \le n \le N$ is $(N+1)$-smooth) and $T_N^{\mathrm{sm}}(s;\omega) = \sum_{n > N,\, P^+(n) \le N} (-1)^{n-1}\omega(n)n^{-s}$. On $\{0 < \operatorname{Re} s < 1\}$, $|2^{1-s}\omega(2)| = 2^{1 - \operatorname{Re} s} > 1$ and $|p^{-s}\omega(p)| = p^{-\operatorname{Re} s} < 1$, so $\widetilde{E}_N(\cdot;\omega)$ is holomorphic and everywhere nonvanishing on $\{0 < \operatorname{Re} s < 1\}$. Consequently, around any zero $\rho_0$ of $\zeta$ with $\frac12 < \operatorname{Re}\rho_0 < 1$ and $\overline{B}(\rho_0, r) \subset \{\frac12 < \operatorname{Re} s < 1\}$, $\widetilde{E}_N(\cdot;\omega) / (1 - 2^{1-s}) \in \mathrm{nonvanishingDiscTargets}(\rho_0, r)$, so
   $$\sup_{z \in \overline{B}(\rho_0, r)} \left|\frac{\widetilde{E}_N(z;\omega)}{1 - 2^{1-z}} - \zeta(z)\right| \ge \operatorname{zetaNonvanishingDistance}(\rho_0, r) > 0.$$
   Setting $m_2 := \inf_{z \in \overline{B}(\rho_0, r)} |1 - 2^{1-z}| \ge 2^{1 - (\operatorname{Re}\rho_0 + r)} - 1 > 0$, any uniform approximation $\sup_{\overline{B}(\rho_0, r)} |A_N(z;\omega) - (1 - 2^{1-z})\zeta(z)| \le \varepsilon$ forces $\sup_{\overline{B}(\rho_0, r)} |T_N^{\mathrm{sm}}(z;\omega)| \ge m_2 \operatorname{zetaNonvanishingDistance}(\rho_0, r) - \varepsilon$.

3. **Universal all-scale two-prime dilation span law (`[PROVED HERE]`).**
   For $\gamma \neq 0$, if $\sin(\gamma\log 2) = \sin(\gamma\log 3) = 0$, then $\gamma\log 2 \in \pi\mathbb{Z}$ and $\gamma\log 3 \in \pi\mathbb{Z}$, so $2\gamma\log 2, 2\gamma\log 3 \in 2\pi\mathbb{Z}$, contradicting `primeLogPhaseClockPair_two_three_injective` at $2\gamma$ vs $0$. For $q_0 > 0$ with $\sin(\gamma\log q_0) \neq 0$ and any $u > 0$, solving the real $2 \times 2$ linear system $u^{\rho_0} = \alpha + \beta q_0^{\rho_0}$ in $\{1, e^{i\gamma\log q_0}\}$ gives
   $$\alpha_{\rho_0,q_0}(u) = u^{\operatorname{Re}\rho_0}\frac{\sin(\gamma(\log q_0 - \log u))}{\sin(\gamma\log q_0)}, \qquad \beta_{\rho_0,q_0}(u) = \frac{u^{\operatorname{Re}\rho_0}}{q_0^{\operatorname{Re}\rho_0}}\frac{\sin(\gamma\log u)}{\sin(\gamma\log q_0)},$$
   satisfying $(u:\mathbb{C})^{\rho_0} = \alpha_{\rho_0,q_0}(u) + \beta_{\rho_0,q_0}(u)(q_0:\mathbb{C})^{\rho_0}$. Under `HasSingleOffLineQuartet ρ₀`, choosing $q_0 \in \{2, 3\}$ with $\sin(\operatorname{Im}\rho_0\cdot \log q_0) \neq 0$ and applying `hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave` at $x$, $q_0 x$, and $ux$ cancels the $x^{\rho_0}$ quartet wave identically for **every** $u \ge 1$ and $x \ge 16$, yielding an explicit $O(\sqrt{ux}\log^2(ux) + (|\alpha| + |\beta|)\sqrt{x}\log^2 x)$ bound on $(\psi(ux) - ux) - \alpha(\psi(x) - x) - \beta(\psi(q_0 x) - q_0 x)$ (and identically for $\theta$).

4. **Zero-pinned fractional-part Mellin equivalences and upper-range divisor concentration (`[PROVED HERE]`).**
   - For $0 < \operatorname{Re} s < 1$, $s \neq 0$ and $s \neq 1$, so `integral_Ioi_zero_fract_cpow`, `integral_Ioi_one_fract_cpow_of_re_pos`, and `integral_Ioi_zero_fract_dilate_cpow` ($c > 0$, $c^s \neq 0$) immediately give:
     $$\zeta(s) = 0 \iff \int_0^\infty \{u\} u^{-s-1}\,du = 0 \iff \int_1^\infty \{t\} t^{-s-1}\,dt = \frac{1}{s-1} \iff \int_0^\infty \{ct\} t^{-s-1}\,dt = 0.$$
   - For $X \ge 1$ and $N = \lfloor X \rfloor_+$, $\lfloor X / d \rfloor = \lfloor N / d \rfloor$ for all $d \ge 1$, so $\{X/d\} = X/d - \lfloor N/d \rfloor$. Summing $\Lambda(d)\{X/d\}$ over $1 \le d \le N$ and applying `Mertens.log_summatory_eq` gives $\sum_{d=1}^N \Lambda(d)\{X/d\} = X\sum_{d=1}^N \frac{\Lambda(d)}{d} - \sum_{m=1}^N \log m$. On $1 \le d \le \lfloor\sqrt{X}\rfloor_+$, $0 \le \{X/d\} < 1$ yields $0 \le \sum_{d=1}^{\lfloor\sqrt{X}\rfloor_+} \Lambda(d)\{X/d\} \le \psi(\sqrt{X})$, isolating the entire global remainder in the upper divisor range $\lfloor\sqrt{X}\rfloor_+ < d \le \lfloor X \rfloor_+$ up to $[0, \psi(\sqrt{X})]$.

## Log
- 2026-11-18 — complete paper proofs written in `2-fully-proven`; proceeding directly to Lean 4 formalization.
