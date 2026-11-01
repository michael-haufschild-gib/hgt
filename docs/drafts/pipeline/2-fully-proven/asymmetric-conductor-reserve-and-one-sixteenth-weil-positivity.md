# Asymmetric Conductor Reserve, Quadratic-Overlap Residuals, and Power-Log Weil Positivity Below 1/16

- **ID:** asymmetric-conductor-reserve-and-one-sixteenth-weil-positivity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-3110/obstacles-summary.md · Q1 / Q2a / Confinement & Residual Exponents
- **Statement:** On $(V_1)^\perp$, a linear prefix cutoff $L_1(c) = \lceil \max(3, 256 e^2 c) \rceil$ localizes the $O(c^9)$ overlap penalty strictly onto the prefix mass $P$ and leaves only $O(c^2)$ mass cost on the terminal strip $S$, lifting polynomial conductor-complement coercivity on $(V_{\lfloor N^\theta \rfloor})^\perp$ ($0 < \theta < 1/6$) from $\alpha < 1/16$ to $\alpha < 1/9$; combined with prefix-localized $O(c^{11})$ sublevel confinement and quadratic-in-$c$ ($O(c^2 (\log N)^{1/k}/\log N)$) complete-Weil conductor residuals across all eight explicit-formula channels, `completeWeilMatrix tiltedUnitSpline c N` is unconditionally positive definite across $1 \le c \le (\log N)^\alpha$ for every $0 < \alpha < 1/16$.

## Goal
Break both the $\alpha < 1/16$ polynomial conductor-complement barrier (`PolynomialConductorComplementCoercivityAndSharpenedOverlap`) and the $\alpha < 1/19$ unconditional all-vector positivity ceiling (`TheCompleteWeilMatrixIsPositiveBelowTheResidualCeiling`) by:
1. Eliminating the symmetric global mass penalty $-C c^9 (P + S)$ in `TwoRegionConductorReserve`, replacing $K c^{16} \le \log R / D - 1$ by $K c^9 \le \log R / D - 1$ on $(V_R)^\perp$ and confining bounded-energy unit vectors $\hat{z} \in (V_{Q_1})^\perp$ to $\log R' \le C_R c^{11} + \log Q_1$ whenever $c^{16}/\log N \to 0$.
2. Eliminating three powers of $c$ ($c^5 \to c^2$) across all eight single-conductor residual channels of `completeWeilMatrix φ c N`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `AsymmetricTwoRegionConductorReserve`, `QuadraticOverlapConductorResiduals`, and `CompleteWeilPositivityBelowOneSixteenth`, `lake --old env lean` green, `#print axioms` PASS

## Approach
Three coupled theorems, proved unconditionally without added hypotheses or budget increases:

### Theorem 1 (Asymmetric Prefix/Terminal Reserve on $(V_1)^\perp$, $\alpha < 1/9$ Complement Coercivity, and Prefix-Localized Sublevel Confinement) `[PROVED HERE]`
Let $\varphi_0 := \operatorname{tiltedUnitSpline}$, $c \ge 1$, $L_1(c) := \lceil \max(3, 256 e^2 c) \rceil$, and $M := \lfloor N / L_1(c) \rfloor$ for $N$ with $H_0 c^2 \le N$. For $z \in (\operatorname{conductorSubspace} 1 N)^\perp$, let $x := \operatorname{primeHorizonExtension} z$, $P := \sum_{n=1}^M x_n^2$, and $S := \sum_{n=M+1}^N x_n^2$.

1. **Exact vanishing of the pole source on $(V_1)^\perp$:**
   Since $\operatorname{normalizedRamanujanHorizonVector} 1 N$ has coordinates $(\log N)^{-1/2} n^{-1/2}$ on $[1, N]$ ($\tilde{c}_1(n) = 1$) and $\langle z, v_{1,N} \rangle = 0$, we have $\sum_{n=1}^N x_n / \sqrt{n} = 0$. By translation scaling $g(u - \log n) e^{-u/2} = n^{-1/2} g(u - \log n) e^{-(u - \log n)/2}$ (`integral_atomicTest_mul`), $\int \operatorname{atomicTest}(N, x, g)(u) e^{-u/2}\,du = (\int g(v) e^{-v/2}\,dv) \sum_{n=1}^N x_n / \sqrt{n} = 0$, so the rank-2 pole moment product $2 \mathcal{P}(f_x) / G$ vanishes identically on $(V_1)^\perp$.

2. **Split-source logarithmic tail localization (`M = \lfloor N / L_1(c) \rfloor`):**
   For each $n \in (M, N]$, $\log n = \sum_{d \mid n} \Lambda(d)$ (`ArithmeticFunction.sum_vonMangoldt_divisors`) splits into pairs $(m, t)$ with $m t = n$ and $m \le M$ versus $m > M$:
   - For $m \le M$ and $M < m t \le N$, Young's inequality $x_{mt}^2 \le (1 + 1/u)(x_{mt} - x_m/\sqrt{t})^2 + (1 + u) x_m^2 / t$ with $u = 8/\delta$ spends at most $(1 + \delta/8)(D_N(x) - D_M(x)) + (1 + 8/\delta)\operatorname{cutoffPrimeCost}(M, N) P$, where $\operatorname{cutoffPrimeCost}(M, N) \le \log(2 L_1(c)) + J_0 \ll 1 + \log c$. Crucially, the $O(c^7 (1 + \log c))$ Young factor multiplies **only $P$**, never $S$.
   - For $m > M$ and $m t = n \le N$, $m \ge M + 1$ and $N < (M + 1) L_1(c)$ force $t < L_1(c)$, so $\sum_{t \mid n,\, n/t > M} \Lambda(t) \le \sum_{t=1}^{L_1(c)} \Lambda(t) \le (\log 4 + 4) L_1(c)$ (`sum_vonMangoldt_Icc_le`), contributing at most $(\log 4 + 4) L_1(c) S = O(c) S$ with **zero** defect cost.
   Adding $(\log N - \log M) S \le \log(2 L_1(c)) S$ yields
   $$(\log N) S \le \Big(1 + \frac{\delta}{8}\Big)\big(D_N(x) - D_M(x)\big) + C_{\mathrm{tp}} c^7 (1 + \log c) P + C_{\mathrm{ts}} c S.$$

3. **Ordered archimedean split at linear cutoff $L_1(c)$:**
   Since $w = c/N$ and $w M \le c / L_1(c) \le 1/(256 e^2)$, we have $w \le \operatorname{atomSpacing}(M)/2$ and $32 e^2 w M \le 1/8$. Thus `archForm_atomicTest_ge_separated_defect` on $f_0 = \operatorname{atomicTest}(M, x, g)$ retains
   $$\frac{\operatorname{archForm}(f_0)}{G} \ge (\log N) P - C_0 c P - \frac{1}{8} D_M(x),$$
   absorbing the prefix self-defect into $\frac{7}{8} D_M(x)$ instead of $\delta D_N(x)$. On $f_1 = \operatorname{atomicTest}(N, y, g)$ ($y = \operatorname{atomicTailCoefficients} M x$), `archForm_atomicTest_ge_growing` gives $\operatorname{archForm}(f_1)/G \ge \delta (\log N) S - b_0 c S$ with $\delta = \min(\operatorname{growingMassConstant}, 1/2) / c^7$, and `archForm_add_ge_of_ordered` subtracts at most $2\pi (1 + 2 e c)(P + S)$.

4. **Split-row bound on `nonRatioForm`:**
   Write $V(m, n) = \sum_{k < \lceil N e^w \rceil + 1} \Lambda_{\mathrm{atom}}(k) \operatorname{upInd}(w, k, m, n)$ (`DirectedPrimeRowsPreserveTheDefect`). Whenever $\operatorname{upInd}(w, k, m, n) \ne 0$, we have $n \ne k m$ ($|n - k m| \ge 1$) and $|\log n - \log(k m)| \le w \le 1$, so $1 \le |n - k m| \le n(e^w - 1) \le e w n = (e c / N) n$, forcing $n \ge N / (e c) > M$ (since $L_1(c) \ge 256 e^2 c > e c$). Hence $V(m, n) = 0$ for all $n \le M$, and $2 |x_m| |x_n| V(m, n)$ is supported strictly on $n > M$:
   - **Cross pairs ($m \le M$, $n > M$):** `directed_young` with $t_0 = \frac{\delta}{8 \operatorname{nonRatioDownConstant} c}$ bounds the sum by $\frac{\operatorname{nonRatioUpConstant} c}{t_0} P + \frac{\delta}{8}(\log N + 1) S = O(c^9) P + \frac{\delta}{8}(\log N + 1) S$.
   - **Tail–tail pairs ($m > M$, $n > M$):** `directed_young` with $t_1 = 1$ bounds the outgoing row by $\operatorname{nonRatioUpConstant} c S$. For the incoming row at fixed $n \in (M, N]$, any active $(k, m)$ with $m \ge M + 1$ satisfies $k m \le n e^w \le e N < e (M + 1) L_1(c)$, so $k < \lceil e L_1(c) \rceil =: K_1(c) = O(c)$, and $|k m - n| \le d_n := n(e^w - 1) \le e c$. For each fixed $k \in [2, K_1(c)]$, any two integers $m_1 < m_2$ with $|k m_i - n| \le d_n$ satisfy $k(m_2 - m_1) \le 2 d_n$, so at most $\lfloor 2 d_n / k \rfloor + 1$ values of $m$ occur; since $\Lambda_{\mathrm{atom}}(k)\sqrt{n/m} \le e^{w/2}\Lambda(k)$, summing over $2 \le k \le K_1(c)$ gives at most $e^{1/2}(\log 4 + 4)\big(2 e c (1 + \log K_1(c)) + K_1(c)\big) = O(c(1 + \log c)) \le O(c^2)$ per $n > M$.
   Combining Steps 1–4 with $(1 - \frac{7\delta}{8})(1 + \frac{\delta}{8}) \le 1 - \frac{3\delta}{4}$ proves the **Asymmetric Prefix/Terminal Reserve on $(V_1)^\perp$**:
   $$\frac{1}{2} D_M(x) + \frac{a}{c^7} D_N(x) + \frac{a}{c^7}(\log N) S - C_0 c^9 P - C_1 c^2 S \le \operatorname{completeWeilEnergy}(\varphi_0, c, N, z)$$
   with $0 < a \le 1/8$.

5. **Two-region $(V_R)^\perp$ coercivity at $K c^9 \le \log R / D - 1$ and $\alpha < 1/9$ on $(V_{\lfloor N^\theta \rfloor})^\perp$:**
   For $w \in (\operatorname{conductorSubspace} R N)^\perp$ ($R \ge 2$, $w \in (V_1)^\perp$ automatically since $V_1 \subseteq V_R$), `poleDefect_prefix_ge_of_conductor_orthogonal` and `poleDefect_ge_explicit_on_conductor_orthogonal` give $D_M(x) \ge k(\frac{15}{16} P - 2 B S)$ and $D_N(x) \ge k(P + S)$ with $k = \log R / D - 1$ and $B = \operatorname{terminalPacketCost}(R, M, N) / \log M$. Under $K c^9 \le k$ (with $K = \max(8 C_0, 4 C_1 / a)$) and $B \le a / (4 c^7)$:
   - $C_0 c^9 \le k/8$, leaving $(\frac{15}{32} - \frac{1}{8}) k P \ge \frac{1}{4} k P$;
   - $C_1 c^2 \le \frac{a k}{4 c^7}$ and $k B \le \frac{a k}{4 c^7}$, leaving $\frac{a k}{2 c^7} S$.
   Setting $R = \lfloor N^\theta \rfloor$ ($0 < \theta < 1/6$) gives $k \asymp \theta \log N$ and $B \ll (1 + \log c)/\log N$, so $K c^9 \le k$ and $B \le a/(4 c^7)$ hold across $1 \le c \le (\log N)^\alpha$ for every $0 < \alpha < 1/9$.

6. **Asymmetric cross-term absorption ($K c^{11} \le k$) and prefix-localized confinement ($\log R' \le C_R c^{11} + \log Q_1$):**
   Replacing `TwoRegionConductorReserve` in `ConductorCrossAbsorption` by Step 5 requires only $K_0 c^9 \le k$ and $128 C_n c^{11} \le a k$, hence $K c^{11} \le k$. Now let $\hat{z} \in (V_{Q_1})^\perp$ ($Q_1 \ge 2$) satisfy $\|\hat{z}\| = 1$ ($P + S = 1$) and $\operatorname{completeWeilEnergy}(\varphi_0, c, N, \hat{z}) \le E_0$. Step 4 immediately yields **both**:
   - $D_M(\hat{x}) \le 2(C_0 + C_1 + E_0) c^9 =: K_{\mathrm{pre}} c^9$, and
   - $\frac{a}{c^7}(\log N) S \le (C_0 + C_1 + E_0) c^9 \implies S \le \frac{C_0 + C_1 + E_0}{a} \frac{c^{16}}{\log N} \le \frac{1}{16}$ once $K_S c^{16} / \log N \le 1$.
   Applying `exists_explicit_quadratic_conductor_projection` on $[1, M]$ with tolerance $1/16$ and defect bound $K_{\mathrm{pre}} c^9$ produces $R_0 \ge 2$ with $\log R_0 \le C_{\mathrm{app}} c^9$ and $p_0 = \sum_{m=1}^{R_0} b_m v_{m,M} \in V_{R_0}(M)$ such that $\|\hat{z}|_{[1,M]} - p_0\|_M^2 \le \frac{1}{16} P \le \frac{1}{16}$. By `half_and_three_halves_riesz_of_log_le` on $[1, M]$, $\sum_{m=1}^{R_0} b_m^2 \le 2 \|p_0\|_M^2 \le 4$. Lifting $p_0$ to $p_N := \sqrt{\frac{\log N}{\log M}} \sum_{m=1}^{R_0} b_m v_{m,N} \in V_{R_0}(N)$ matches $p_0$ identically on $[1, M]$ and has terminal squared norm $\sum_{n \in (M,N]} (p_N)_n^2 \le \frac{\operatorname{terminalPacketCost}(R_0, M, N)}{\log M} \sum_{m=1}^{R_0} b_m^2 \le 4 B_0 \le \frac{1}{32}$. Using $(x_n - y_n)^2 \le 2 x_n^2 + 2 y_n^2$ on $(M, N]$,
   $$\|\hat{z} - p_N\|_N^2 \le \frac{1}{16} + 2 S + 2 \sum_{n \in (M,N]} (p_N)_n^2 \le \frac{1}{16} + \frac{2}{16} + \frac{2}{32} = \frac{1}{4}.$$
   Setting $G := \lceil \exp(C_{\mathrm{gap}} c^{11}) \rceil$ and $R' := \max(\max(R_0, G), Q_1)$ yields $\log R' \le C_R c^{11} + \log Q_1$ and retains $\|P_{R'}\hat{z}\|^2 \ge 3/4$ with adjunction-debited energy $\le E_0 + 1$.

---

### Theorem 2 (Quadratic-Overlap Complete-Weil Single-Conductor Residuals: $c^5 \to c^2$) `[PROVED HERE]`
Let $\varphi : \mathbb{R} \to \mathbb{R}$ be $C^2$, supported in $[0, 1]$, with $\int \varphi^2 > 0$. Across $0 < m \le (\log N)^A$ ($A \ge 0$), $k \ge 1$, $c \ge 1$, and $4(e + 3)^2 c^2 \le N$:
$$\|W_{\varphi,c,N} v_{m,N} - E_\varphi(c, m) v_{m,N}\|^2 \le K \cdot m(1 + \log m)^2 \left(\frac{c^2 (\log N)^{1/k}}{\log N} + c^{10}\Big(\frac{\log N}{N}\Big)^2\right).$$
Using the exact 8-term identity `completeWeilMatrix_ramanujan_residual_eq_at_every_overlap`, the three channels already at $\le c^2 / \log N$ (`fullPrimeMatrix` at $c^0/\log N$, `selfError` at $c^2/N^2$, `fullWeilCenterMatrix` at $c^2/\log N$) are joined by sharpening the remaining five channels:

1. **Separated cross error (`hx'`):** By `abs_separatedCrossError_le`, $|K_{\mathrm{sep}}(n, j)| \le K_0 (c/N)^2 \frac{\max(n,j)^2}{|n-j|^2} \mathbf{1}_{|\log j - \log n| > 2c/N}$, and $|\tilde{c}_m(j)| \le \sqrt{m}$. Split $j \in [1, N] \setminus \{n\}$ into:
   - *Far pairs* ($2|j - n| > \max(n, j)$): $\max(n, j)^2 / |n - j|^2 \le 4$, so summing $j^{-1/2}$ over $[1, N]$ ($\le 2\sqrt{N}$) gives $\le 8 K_0 \sqrt{m} c^2 N^{-3/2}$, whose squared norm over $n \in [1, N]$ is $\le 64 K_0^2 m c^4 / N^2$.
   - *Moderate pairs* ($2|j - n| \le \max(n, j)$, hence $n/2 \le j \le 2n$ and $\min(j, n) \ge n/2$): $2c/N < |\log j - \log n| \le |j - n|/\min(j, n) \le 2|j - n|/n$ forces $|j - n| \ge d_n := \max(1, \lceil c n / N \rceil)$. Since $\sum_{h = d_n}^N h^{-2} \le d_n^{-2} + \sum_{h = d_n+1}^N \frac{1}{h(h-1)} \le 2/d_n$ and $d_n \ge c n / N$, the moderate row sum is bounded by $K_0 (c/N)^2 (2n)^2 \frac{\sqrt{2m}}{\sqrt{n}} \cdot \frac{4}{d_n} \le 16\sqrt{2} K_0 \sqrt{m} \frac{c \sqrt{n}}{N}$. Squaring and summing over $n \in [1, N]$ ($\sum_{n=1}^N n \le N^2$) gives $\le 512 K_0^2 m c^2$, i.e. $O(m c^2 / \log N)$ after dividing by $\log N$.

2. **Two-pole moment error (`hq'`):** By `abs_atomPoleErrorCoefficient_le_of_le`, $|\alpha_{c,N}| \le C_0 (c/N)^2$. Using $|\sum_{j=1}^N \tilde{c}_m(j)/j| \le \sqrt{m}(1 + \log N)$ and $|\sum_{j=1}^N \tilde{c}_m(j)| \le \sqrt{m} N$, row $n$ of `fullWeilPoleErrorMatrix` on `ramanujanHorizonVector m N` is bounded by $C_0 (c/N)^2 \sqrt{m} (\sqrt{n}(1 + \log N) + N/\sqrt{n})$. Squaring and summing over $n \in [1, N]$ yields $O(m c^4 (\log N)^2 / N^2)$, or $O(m c^4 (\log N) / N^2) \ll m c^{10} (\log N / N)^2$ after normalization.

3. **Near-center replacement (`hn'`):** For $j \in \operatorname{nearRowIndices}(c, N, n)$, `nearRow_geometry_small_width` gives $N \le R_c n$, $N \le R_c j$ ($R_c = 2 e^2 c$), and $1 \le |j - n| \le R_c$. Also $|\log j - \log n| \ge |j - n|/\max(j, n) \ge |j - n|/N$, so $\frac{1}{N}\operatorname{archLevyDensity}|\log j - \log n| \le \frac{1}{2|j - n|} + \frac{e^{1/2}}{4 N} \le \frac{C_1}{|j - n|}$. Since $|\log(j/n)| \le 2c/N \le 2$ gives $j \ge n / e^2$, summing $|j - n|^{-1}$ over $1 \le |j - n| \le \lfloor R_c \rfloor$ bounds row $n$ by $C_2 \sqrt{m} c (1 + \log c) n^{-1/2} \mathbf{1}_{N \le R_c n}$. Squaring and summing $n^{-1}$ over $N/R_c \le n \le N$ (`harmonic_quotient_tail_le`) yields $O(m c^2 (1 + \log c)^3 / \log N)$.

4. **Downward near-Gamma and exterior prime source (`hd'`):**
   - *Interior near-Gamma (`hnear_sq`):* On $j \in \operatorname{nearRowIndices}(c, N, n)$, $N/j \le R_c$ implies $0 \le \log N - \log j \le \log R_c = O(1 + \log c)$ (rather than $R_c = O(c)$), giving $|F(n, j)| \le E_1 \varphi(m)(1 + \log m)(1 + \log c)$. Moreover $|j - n| \le n (R_c / N)$ (`nearRow_geometry_small_width` proof) and $j \ge n / e^2$, so each active row $n \ge N / R_c$ has $\le 2 n R_c / N$ terms (wait: when $n R_c / N < 1$, `nearRowIndices` is empty since $|j - n| \ge 1$!), hence row $n$ is bounded by $2 e (n R_c / N) E_1 \varphi(m)(1 + \log m)(1 + \log c) / \sqrt{n}$. Squaring and summing over $n \in [1, N]$ ($\sum_{n=1}^N n/N^2 \le 1$) gives $O(\varphi(m)^2(1 + \log m)^2 c^2 (1 + \log c)^2 / \log N)$.
   - *Exterior prime strip (`hext_sq`):* On $\ell \in (N, \operatorname{exteriorPrimeCutoff}(c, N)]$, $\ell > N$ and $\ell \le 3 N$, so $\log \ell / \sqrt{\ell} \le \log(3N)/\sqrt{N}$. The strip has width $\le (e + 1)c$ and active rows $\le (e + 2)c$, giving squared norm $O(\varphi(m)^2 c^3 (\log N)^2 / (N \log N)) \ll \varphi(m)^2 (c^2 / \log N + c^{10}(\log N / N)^2)$ (since $c^3 (\log N)^2 / N \le c^2$ for $c \le N^{1/3}$).

5. **Upward prime boundary and variable-cutoff reciprocal shell (`hu'`):**
   - *Cutoff change (`linearized - reciprocal`):* By `linearizedUpwardOffset_eq_reciprocal_of_not_boundary`'s proof, `linearizedUpwardOffset` and `reciprocalUpwardOffset` agree whenever $|k n - N| > B$ ($B = \lceil (e + 1)c \rceil$).
     - For $1 \le n \le B$: since $4 B^2 \le N$, every $k$ with $|k n - N| \le B$ has $k n \ge N - B \ge N/2$, so $\Lambda(k)/k \le \frac{2 n \log N}{N}$ and at most $\frac{2B}{n} + 2 \le 4B/n$ values of $k$ satisfy $|k n - N| \le B$. Summing over $h \in [1, B]$ gives $|\Delta_n| \le 16 \varphi(m) B^2 (\log N) / N$; dividing by $\sqrt{n}$, squaring, and summing over $1 \le n \le B$ gives $O(\varphi(m)^2 B^4 (1 + \log B) (\log N)^2 / N^2) \ll \varphi(m)^2 c^{10} (\log N)^2 / N$.
     - For $B < n \le N$: any two $k_1 < k_2$ with $|k_i n - N| \le B$ satisfy $(k_2 - k_1) n \le 2 B < 2 n$, so $k_2 - k_1 \le 1$; hence $k \in \{\lfloor N/n \rfloor, \lfloor N/n \rfloor + 1\}$ (at most **2** integers!). For $B < n \le N/4$, $k \ge \lfloor N/n \rfloor \ge 2$ and $k \ge \frac{N}{2n}$, so $\Lambda(k)/k \le 2/\sqrt{k} \le 2\sqrt{2 n / N}$, giving $|\Delta_n|/\sqrt{n} \le 16\sqrt{2}\varphi(m) B / \sqrt{N}$. For $N/4 < n \le N$, $\Lambda(k)/k \le 1$ and $1/\sqrt{n} \le 2/\sqrt{N}$, giving $|\Delta_n|/\sqrt{n} \le 16\varphi(m) B / \sqrt{N}$. Squaring and summing over $B < n \le N$ yields $\le 512 \varphi(m)^2 B^2 = O(\varphi(m)^2 c^2)$.
   - *Shifted reciprocal shell (`VariableCutoffConductorResiduals`):* At $T = 2 c \exp((\log N)^{1/k})$, $\log(2 T) = \log(4 c) + (\log N)^{1/k} \le 2 + \log c + (\log N)^{1/k}$ (replacing $\log(4c) \le 4c - 1$), so `b^2 * (1 + log(2T))` is $O(\varphi(m)^2 c^2 (1 + \log c + (\log N)^{1/k})) = O(\varphi(m)^2 c^2 (\log N)^{1/k})$, and `a^2 * (1 + L)` is already $O(c^2 / \log N)$.

   Since $(1 + \log c)^3 \ll (\log N)^{1/k}$ (choosing $2k$ internally so $(\log N)^{1/(2k)}(1 + \log c)^3 \le C_k (\log N)^{1/k}$), all eight channels sum to $O\big(m(1 + \log m)^2 (c^2 (\log N)^{1/k}/\log N + c^{10}(\log N/N)^2)\big)$, and summing relative weights over $1 \le m \le Q$ via `sum_linear_conductor_relative_weights_le` yields $O\big((c^{14} + Q^2)(1 + \log Q)^2 (c^2 (\log N)^{1/k}/\log N + c^{10}(\log N/N)^2)\big)$.

---

### Theorem 3 (Unconditional All-Vector Complete-Weil Positivity Below $1/16$) `[PROVED HERE]`
Let $0 < \alpha < 1/16$. Set $\tau := (1 - 16\alpha)/100 > 0$, $q := 6\alpha + \tau \in (0, 1/2)$, $\nu := \tau/10$, $Q_1 := \lfloor (\log N)^q \rfloor$, and $k := \lceil 1/\tau \rceil + 1$:
- **Low-band relative residual (`hlow_exp`):** $(c^{14} + Q_1^2)(1 + \log Q_1)^2 \cdot c^2 (\log N)^{1/k} / \log N$ has exponents $16\alpha + 1/k + 2\nu - 1 \le -\nu$ (since $16\alpha + 100\tau = 1$) and $2q + 2\alpha + 1/k + 2\nu - 1 = 14\alpha + 2\tau + 1/k + 2\nu - 1 \le -\nu$.
- **Prefix-localized confinement & high-region coercivity (`hmain` + `hlag` + `hgap`):** By Theorem 1(6), any unit vector $\hat{z} \in (V_{Q_1})^\perp$ with energy $\le 2\kappa_{\mathrm{sp}} + 2$ satisfies $S \le 1/16$ (since $16\alpha + \nu - 1 \le -\nu$) and confines to $R'$ with $\log R' \le C_R c^{11} + \log Q_1$. Every high-region monomial in `HighConductorWeilCoercivity` and `AsymmetricConductorCrossAbsorption` has exponent at most $\max(2 + 11, 11)\alpha = 13\alpha < 1 - 3\nu$; lag decay $c^3/\sqrt{Q_1}$ has exponent $3\alpha - q/2 = -\tau/2 \le -\nu$; and the logarithmic gap $\frac{1}{4}\log Q_1 - \log c \ge (\frac{1}{2}\alpha + \frac{\tau}{4})\log\log N - \frac{1}{4} \to +\infty$.
- Applying `matrix_posDef_of_relative_conductor_budget` to `spectralFloorWeilMatrix c N` establishes `PosDef`, the uniform $\frac{\kappa_{\mathrm{sp}}}{2 c^7}\|x\|^2$ spectral floor, `completeWeilMatrix tiltedUnitSpline c N` positive definiteness, `weilQuad ≥ 0` on all atomic test functions, and the $\frac{b_1}{c^{23}}\operatorname{poleDefect}_N(x)$ reserve across $1 \le c \le (\log N)^\alpha$ for all $0 < \alpha < 1/16$.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** The naive conjecture that $\operatorname{completeWeilEnergy}(\varphi_0, c, N, z) \ge \beta \theta (\log N) c^{-(2+\varepsilon)} \|z\|^2$ holds for all $z \in (V_{\lfloor N^\theta \rfloor})^\perp$ for $\varphi_0 = \operatorname{tiltedUnitSpline}$ is **FALSE**: alternating vectors $y_n = (-1)^n \mathbf{1}_{(N - H, N]}$ ($H = \lfloor N / c^8 \rfloor$) projected onto $(V_{\lfloor N^\theta \rfloor})^\perp$ experience cubic-spline finite-difference cancellation $\|f_y\|_{L^2}^2 / G \asymp c^{-7}\|y\|^2$ and vanishing prime sum, realizing energy $\asymp c^{-7}(\log N)\|z\|^2$. Likewise, invoking `logarithmicReserveMatrix.PosDef` (`TheCompleteWeilLogarithmicReserveSurvivesGrowingOverlap`) at $c = (\log N)^\alpha$ is **CIRCULAR** because its horizon requirement exponentiates $c^{16}$, restricting it to $c \le (\log\log N)^\alpha$.
- **Strongest positive survivor:** The Asymmetric Prefix/Terminal Reserve on $(V_1)^\perp$ (Theorem 1) + Quadratic-Overlap Single-Conductor Residuals (Theorem 2) + All-Vector Positivity up to $\alpha < 1/16$ (Theorem 3).
- **New insight:** Even though the terminal archimedean reserve genuinely drops as $c^{-7}$, the $O(c^9)$ Young penalty from directed non-ratio prime lags and tail defect localization acts **only on the separated prefix mass $P$** where an order-$1$ prefix defect reserve $+\frac{1}{2} D_M(x)$ is available, whereas the terminal strip mass $S$ incurs only $O(c^2)$ self-cost. This decouples $(V_{\lfloor N^\theta \rfloor})^\perp$ coercivity ($\alpha < 1/9$) from the scale-invariant prefix–tail non-ratio Cauchy–Schwarz balance $\frac{\sqrt{c \cdot (c \log N)}}{c^{-7}\log N} = \frac{c^8}{\sqrt{\log N}}$ ($\alpha < 1/16$).
- **Status:** Complete dependency-closed paper proof above; proceeding immediately to Lean 4 formalization.

## Log
- 2026-11-01 — created in 1-in-progress with complete paper proof and promoted to 2-fully-proven
