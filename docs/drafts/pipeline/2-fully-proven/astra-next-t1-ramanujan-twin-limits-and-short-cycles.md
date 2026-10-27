# Closed-Form Ramanujan Parity-Twin Limits, Pole-Node Erasure, and Symmetry-Parity Short-Cycle Positivity (`RBG` Open Topic #1)

- **ID:** astra-next-t1-ramanujan-twin-limits-and-short-cycles
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-2710/astra.md · Focus Question 3 / `RenormalizedBiarithmeticGeometry/README.md` Open Topic #1
- **Statement:** Closed-form evaluation of the Cesàro Gram matrix and twisted digamma / cyclotomic-harmonic limit matrices of even-shifted and torsion-aligned Ramanujan germs, proof of exact pole-node erasure of `-orbitIntersection` (`Λ(t)`) on the survival cone, unconstrained PSD of the pole-node-completed cyclotomic-harmonic kernel, dyadic parity-split scale anomaly `torsionEnergy r q (2q) → -φ(q) log 2`, and midpoint parity-transposition + coercive `m = 1` short-cycle Weil positivity for `p = 2` past `3/10`.

## Goal
Resolve `RenormalizedBiarithmeticGeometry` Open Topic #1 completely and unconditionally:
1. Evaluate in closed form the Cesàro Gram matrix, scheme-independent survival cone, and renormalized `r → 1⁻` limit matrix `A` in `evenShift_ramanujanParityTwin_survival` (as well as its torsion-aligned `k + 1` / `2(k + 1)` counterpart coupled to pole-node completion `x = 0`).
2. Test whether positivity on the joint `{q, 2q}` / Ramanujan survival cone constrains short-cycle prime forms `g - T_{2^m} g`, proving BOTH the exact algebraic obstruction (**Pole-Node Erasure Law**: `-orbitIntersection(q_α, q_β)` is node-independent and vanishes identically on the survival cone even after pole-node completion at `x = 0`) AND three non-trivial positive survivors (**Unconstrained PSD Cyclotomic-Harmonic Kernel**, **Dyadic Parity-Split Scale Anomaly**, and **Midpoint Parity-Transposition & Coercive `m = 1` Short-Cycle Weil Positivity on `[-η, η]` up to `η ≤ 181/500 - (log 2)/2`**).

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, internal corpus audit completed
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `RamanujanParityTwinLimitsAndShortCycleObstruction.lean`, `lake --old env lean` green, axiom check PASS

## Approach & Complete Dependency-Closed Paper Proof (`[PROVED HERE]`)

### 1. Closed-Form Cesàro Gram and Scheme-Independent Parity-Twin Survival Cone
Let $\iota$ be a `Fintype` with `[DecidableEq ι]`, and let $\mathrm{ord} : \iota \to \mathbb{N}$ satisfy $0 < \mathrm{ord}(\alpha)$ and $4 \nmid \mathrm{ord}(\alpha)$ for all $\alpha \in \iota$. Let $q_\alpha := \mathrm{oddCore}(\mathrm{ord}(\alpha)) > 0$ (`oddCore_pos`). By `ramanujanMode_evenShift_eq_oddCore`, for every $k \in \mathbb{N}$,
$$c_{\mathrm{ord}(\alpha)}(2k) = c_{q_\alpha}(k), \qquad c_{\mathrm{ord}(\alpha)}(2(k+1)) = c_{q_\alpha}(k+1).$$
Let $Q := \prod_{\gamma \in \iota} q_\gamma > 0$. Since $q_\alpha \mid Q$ for all $\alpha$, `RBG.sum_ramanujanMode_mul` gives
$$\frac{1}{Q} \sum_{k=0}^{Q-1} c_{\mathrm{ord}(\alpha)}(2k) c_{\mathrm{ord}(\beta)}(2k) = \frac{1}{Q} \sum_{k=0}^{Q-1} c_{q_\alpha}(k) c_{q_\beta}(k) = \begin{cases} \varphi(q_\alpha) & \text{if } q_\alpha = q_\beta, \\ 0 & \text{if } q_\alpha \ne q_\beta. \end{cases}$$
For the torsion-aligned modes $b_\alpha(k) := c_{\mathrm{ord}(\alpha)}(2(k+1)) = c_{q_\alpha}(k+1)$, since $c_m$ is $Q$-periodic whenever $m \mid Q$ (`ramanujanMode_periodic_of_dvd`, proved from `IsPrimitiveRoot.pow_eq_one_iff_dvd`), $\sum_{k=0}^{Q-1} f(k+1) = \sum_{k=0}^{Q-1} f(k) + f(Q) - f(0) = \sum_{k=0}^{Q-1} f(k)$, giving the identical Cesàro Gram matrix.

For any valid node assignment $x : \iota \to \mathbb{R}$ ($1 + x_\alpha + x_\beta > 0$ for all $\alpha, \beta$) and **every** renormalization counterterm $f : \mathbb{R} \to \mathbb{R}$, `RBG.periodicGerm_survivalCone_eq` identifies the survival cone with $\{C : \iota \to \mathbb{R} \mid \sum_{\alpha, \beta} C_\alpha C_\beta G_{\alpha\beta} = 0\}$. Partitioning $\iota$ by fibers of $\alpha \mapsto q_\alpha$:
$$\sum_{\alpha, \beta} C_\alpha C_\beta G_{\alpha\beta} = \sum_{m \in \mathrm{image}(q)} \varphi(m)\Bigl(\sum_{q_\alpha = m} C_\alpha\Bigr)^2.$$
Since $q_\alpha > 0 \implies \varphi(q_\alpha) > 0$, this quadratic form vanishes if and only if $\sum_{q_\alpha = m} C_\alpha = 0$ for every $m \in \mathbb{N}$. On a twin pair $\{q, 2q\}$ with $q$ odd, $\mathrm{oddCore}(q) = \mathrm{oddCore}(2q) = q$, so $(C_q, C_{2q})$ survives if and only if $C_q + C_{2q} = 0$.

### 2. Arithmetic-Progression Germ Limits (`[L ∣ k]` and `[L ∣ k + 1]`)
Fix $L \in \mathbb{N}$ with $L > 0$.
1. **Scale-logarithm identity:** For $r \in (0, 1)$, $1 - r^L = (1 - r) \sum_{i=0}^{L-1} r^i$ (`mul_neg_geom_sum` / `geom_sum_mul_neg`). Both $1 - r > 0$ and $\sum_{i=0}^{L-1} r^i \ge r^0 = 1 > 0$, so
   $$\log(1 - r^L) - \log(1 - r) = \log\Bigl(\sum_{i=0}^{L-1} r^i\Bigr) \xrightarrow{r \to 1^-} \log L.$$
2. **Unshifted progression (`[L ∣ k]`, $w > 0$):** For $0 \le r < 1$, reindexing along the injection $j \mapsto L j$ gives
   $$\sum_{k=0}^\infty \frac{r^k [L \mid k]}{k + w} = \frac{1}{L} \sum_{j=0}^\infty \frac{(r^L)^j}{j + w/L} = \frac{1}{L} \operatorname{latticeGerm}(r^L, w/L).$$
   For $r \in (0, 1)$, write
   $$\frac{1}{L}\operatorname{latticeGerm}(r^L, w/L) + \frac{1}{L}\log(1 - r) = \frac{1}{L}\bigl(\operatorname{latticeGerm}(r^L, w/L) + \log(1 - r^L)\bigr) - \frac{1}{L}\bigl(\log(1 - r^L) - \log(1 - r)\bigr).$$
   Since $r \mapsto r^L$ maps $(0, 1)$ into $(0, 1)$ and tends to $1$ in $\mathcal{N}_{<}(1)$ as $r \to 1^-$, composing `RBG.tendsto_latticeGerm_add_log (w := w/L)` ($w/L > 0$) yields the limit
   $$\frac{-\operatorname{Re}\psi(w/L) - \gamma - \log L}{L}.$$
3. **Torsion-aligned progression (`[L ∣ k + 1]`, $u > -L$, in particular $u \ge 0$):** Since $L \ge 1$, $L \mid k + 1 \iff \exists j \in \mathbb{N},\; k = L j + (L - 1)$. Reindexing along the injection $j \mapsto L j + (L - 1)$ gives, for $0 \le r < 1$,
   $$\sum_{k=0}^\infty \frac{r^k [L \mid k + 1]}{k + 1 + u} = \frac{r^{L-1}}{L} \operatorname{latticeGerm}\bigl(r^L, 1 + u/L\bigr).$$
   For $r \in (0, 1)$, write
   $$\frac{r^{L-1}}{L} G_{r^L}(1 + u/L) + \frac{1}{L}\log(1 - r) = \frac{r^{L-1}}{L}\bigl(G_{r^L}(1 + u/L) + \log(1 - r^L)\bigr) - \frac{r^{L-1}}{L}\log\Bigl(\sum_{i=0}^{L-1} r^i\Bigr) + \frac{\sum_{i=0}^{L-2} r^i}{L} \cdot (1 - r)\log(1 - r).$$
   As $r \to 1^-$, $(1 - r)\log(1 - r) \to 0$ (`Real.tendsto_pow_mul_log_nhds_zero_of_lt_one` / substitution $t = 1 - r \to 0^+$), $r^{L-1} \to 1$, and $-\operatorname{Re}\psi(1 + u/L) - \gamma = -\operatorname{harmonicFn}(u/L)$ (`RBG.harmonicFn`), yielding the limit
   $$\frac{-\operatorname{harmonicFn}(u/L) - \log L}{L}.$$

### 3. Closed-Form Twisted Digamma and Cyclotomic-Harmonic Limit Matrices
By `AET.ramanujanSum_eq_sum_moebius` and `Nat.sum_divisorsAntidiagonal'`, for $m > 0$ and $t \in \mathbb{N}$,
$$c_m(t) = \sum_{a \mid m} \mu(m/a) \cdot (a \cdot [a \mid t]).$$
Hence for $m, n > 0$, since $(a \mid t \wedge b \mid t) \iff \operatorname{lcm}(a, b) \mid t$,
$$c_m(t) c_n(t) = \operatorname{doubleMoebius}_{m,n}\!\bigl((a, b) \mapsto a b [\operatorname{lcm}(a,b) \mid t]\bigr).$$
Also, by `AET.sum_moebius_mul_gcd` and `AET.sum_moebius_ite_dvd`,
$$\operatorname{doubleMoebius}_{m,n}\!\bigl((a, b) \mapsto \gcd(a, b)\bigr) = \sum_{a \mid m} \mu(m/a) [n \mid a]\varphi(n) = \begin{cases} \varphi(m) & \text{if } m = n, \\ 0 & \text{if } m \ne n, \end{cases}$$
because if $n \mid m$ with $m = n k$, $\sum_{c \mid k} \mu(k/c) \varphi(n) = \varphi(n) [k = 1] = \varphi(n) [m = n]$ (`AET.sum_divisors_moebius`).
Since $a b / \operatorname{lcm}(a, b) = \gcd(a, b)$ (`Nat.gcd_mul_lcm`) and $\operatorname{doubleMoebius}_{m,n}(\gcd \cdot \log \operatorname{lcm}) = \operatorname{doubleMoebius}_{m,n}(\operatorname{logEnergy}) = \operatorname{orbitIntersection}(m, n)$ (`AET.logEnergy_eq`, `AET.orbitIntersection_eq_doubleMoebius`):
- **Unshifted / `evenShift_ramanujanParityTwin` closed-form limit (`q_α = oddCore(ord α)`):**
  $$\lim_{r \to 1^-} \Bigl(\operatorname{periodicGerm}(a^{\mathrm{ev}}, x, r)_{\alpha\beta} + G_{\alpha\beta} \log(1 - r)\Bigr) = -\operatorname{orbitIntersection}(q_\alpha, q_\beta) - \operatorname{cyclotomicDigamma}(q_\alpha, q_\beta, 1 + x_\alpha + x_\beta),$$
  where $\operatorname{cyclotomicDigamma}(m, n, w) := \operatorname{doubleMoebius}_{m,n}\!\bigl((a, b) \mapsto \gcd(a, b)(\operatorname{Re}\psi(w/\operatorname{lcm}(a,b)) + \gamma)\bigr)$.
- **Torsion-aligned (`k + 1` or `2(k + 1)`) closed-form limit:**
  $$\lim_{r \to 1^-} \Bigl(\operatorname{periodicGerm}(b^{\mathrm{ev}}, x, r)_{\alpha\beta} + G_{\alpha\beta} \log(1 - r)\Bigr) = -\operatorname{orbitIntersection}(q_\alpha, q_\beta) - \operatorname{cyclotomicHarmonic}(q_\alpha, q_\beta, x_\alpha + x_\beta),$$
  where $\operatorname{cyclotomicHarmonic}(m, n, u) := \operatorname{doubleMoebius}_{m,n}\!\bigl((a, b) \mapsto \gcd(a, b)\operatorname{harmonicFn}(u/\operatorname{lcm}(a,b))\bigr)$. At $x_\alpha = x_\beta = 0$, $\operatorname{harmonicFn}(0) = 0$, so the limit equals $-\operatorname{orbitIntersection}(q_\alpha, q_\beta)$ (`= -\varphi(q_\alpha)\Lambda(t)` on $q_\beta = q_\alpha t, t > 1$).

### 4. Exact Obstruction & Positive Survivors (`RBG` Open Topic #1)
1. **Pole-Node Erasure Law (`poleNode_erasure_of_orbitIntersection`):** For ANY node-independent kernel $K(q_\alpha, q_\beta)$ (in particular $K = -\operatorname{orbitIntersection}$) and ANY $C$ in the survival cone ($\forall m,\; \sum_{q_\alpha = m} C_\alpha = 0$ — including pole-node completion $C_{m,0} = -\sum_i c_{m,i}$ at $x_{m,0} = 0$):
   $$\sum_{\alpha, \beta} C_\alpha C_\beta K(q_\alpha, q_\beta) = \sum_{m, n \in \mathrm{image}(q)} K(m, n)\Bigl(\sum_{q_\alpha = m} C_\alpha\Bigr)\Bigl(\sum_{q_\beta = n} C_\beta\Bigr) = 0.$$
   Hence on the entire survival cone, the renormalized quadratic form reduces strictly to $-\sum_{\alpha, \beta} C_\alpha C_\beta \operatorname{cyclotomicHarmonic}(q_\alpha, q_\beta, x_\alpha + x_\beta)$ (resp. $-\operatorname{cyclotomicDigamma}$): the prime-side torsion intersection $\Lambda(t)$ is **identically erased** by per-order neutrality and cannot distinguish $\zeta$ from off-line configurations on general short cycles $g - T_{2^m} g$.
2. **Positive Survivor 1 — Unconstrained PSD Cyclotomic-Harmonic Kernel (`cyclotomicHarmonicKernel_nonneg`):** Given arbitrary positive orders $m_1, \dots, m_n > 0$, nonnegative nodes $x_1, \dots, x_n \ge 0$, and real weights $c_1, \dots, c_n \in \mathbb{R}$, augment $\iota = \mathrm{Fin}\,n \oplus \mathrm{Fin}\,n$ with pole nodes $(\mathrm{inl}\,i \mapsto (m_i, x_i))$, $(\mathrm{inr}\,i \mapsto (m_i, 0))$ and weights $C(\mathrm{inl}\,i) = c_i$, $C(\mathrm{inr}\,i) = -c_i$. Then $\sum_{m_\alpha = M} C_\alpha = \sum_{m_i = M} (c_i - c_i) = 0$, so $C$ lies in the torsion-aligned Ramanujan survival cone! Since the periodic germ is PSD for all $r \in [0, 1)$ (`RBG.periodicGerm_posSemidef`), passing to $r \to 1^-$, erasing $-\operatorname{orbitIntersection}$ via Pole-Node Erasure, and using $\operatorname{cyclotomicHarmonic}(m, n, 0) = 0$ proves unconditionally:
   $$0 \le \sum_{i, j} c_i c_j \Bigl(\operatorname{cyclotomicHarmonic}(m_i, m_j, x_i) + \operatorname{cyclotomicHarmonic}(m_i, m_j, x_j) - \operatorname{cyclotomicHarmonic}(m_i, m_j, x_i + x_j)\Bigr),$$
   strictly generalizing `RBG.harmonicKernel_nonneg` ($m_i \equiv 1$).
3. **Positive Survivor 2 — Dyadic Parity-Split Scale Anomaly (`torsionEnergy_dyadic_parity_split`, `tendsto_oddTorsionEnergy_sub_half_even`):** Why does `torsionEnergy r q (2q)` ($q$ odd, $q > 0$) converge to $-\varphi(q)\log 2$ without pole-node erasure? Because for $0 \le r < 1$ and odd $q > 0$, $c_{2q}(2j) = +c_q(j)$ while $c_{2q}(2j+1) = -c_q(2j+1)$ (`ramanujanMode_two_mul_odd_of_odd`: for odd $q$ and odd $t$, $\gcd(2, t) = 1$, $c_2(t) = \mu(2) = -1$, and by multiplicativity of Ramanujan sums on coprime moduli $2$ and $q$, $c_{2q}(t) = c_2(t) c_q(t) = -c_q(t)$!). Splitting `hasSum_torsionEnergy` over $k = 2j$ and $k = 2j + 1$ gives
   $$\operatorname{torsionEnergy}(r, q, 2q) = \frac{1}{2}\operatorname{torsionEnergy}(r^2, q, q) - \operatorname{oddTorsionEnergy}(r, q, q),$$
   where $\operatorname{oddTorsionEnergy}(r, m, n) := \sum_{j=0}^\infty \frac{r^{2j+1}}{2j+1} c_m(2j+1) c_n(2j+1)$ is PSD! Since $\operatorname{torsionEnergy}(r, q, 2q) \to -\operatorname{orbitIntersection}(q, 2q) = -\varphi(q)\log 2$ (`tendsto_torsionEnergy_of_ne`, `orbitIntersection_hecke`) while $\frac{1}{2}\operatorname{torsionEnergy}(r^2, q, q) + \frac{\varphi(q)}{2}\log(1 - r^2) \to -\frac{1}{2}\operatorname{orbitIntersection}(q, q)$, adding $\frac{\varphi(q)}{2}\log\frac{1 - r^2}{1 - r} = \frac{\varphi(q)}{2}\log(1 + r) \to \frac{\varphi(q)}{2}\log 2$ identifies the exact dyadic scale anomaly:
   $$\operatorname{oddTorsionEnergy}(r, q, q) + \frac{\varphi(q)}{2}\log(1 - r) \xrightarrow{r \to 1^-} -\frac{1}{2}\operatorname{orbitIntersection}(q, q) + \frac{\varphi(q)}{2}\log 2.$$
4. **Positive Survivor 3 — Midpoint Parity-Transposition Law & Coercive `m = 1` Short-Cycle Weil Positivity (`shortCycle_parity_orthogonal_split`, `even_shortCycle_m_one_re_W_ge`):**
   For any $g \in C^2_c(\mathbb{R}, \mathbb{C})$ and shift $v \in \mathbb{R}$, let $h := T_{-v/2}(g - T_v g)$, i.e., $h(x) = g(x + v/2) - g(x - v/2)$.
   - By Hecke translation isometry (`W_self_eq_towerMoment_zero` + `towerMoment_translate_zero`), $W_\zeta(g - T_v g, g - T_v g) = W_\zeta(h, h)$ and $\int \|g - T_v g\|^2 = \int \|h\|^2$.
   - Decomposing $g = g_{\mathrm{ev}} + g_{\mathrm{odd}}$ (`g_ev(x) = (g(x)+g(-x))/2`, `g_odd(x) = (g(x)-g(-x))/2`), the midpoint-centered difference **transposes parity**: $h_{\mathrm{odd}} := T_{-v/2}(g_{\mathrm{ev}} - T_v g_{\mathrm{ev}})$ is **strictly odd** ($h_{\mathrm{odd}}(-x) = -h_{\mathrm{odd}}(x)$) and $h_{\mathrm{ev}} := T_{-v/2}(g_{\mathrm{odd}} - T_v g_{\mathrm{odd}})$ is **strictly even** ($h_{\mathrm{ev}}(-x) = h_{\mathrm{ev}}(x)$). By even/odd orthogonality of `fullZeroForm` (`fullZeroForm_eq_even_add_odd`),
     $$\operatorname{Re} W_\zeta(g - T_v g, g - T_v g) = \operatorname{Re} W_\zeta(g_{\mathrm{ev}} - T_v g_{\mathrm{ev}}, g_{\mathrm{ev}} - T_v g_{\mathrm{ev}}) + \operatorname{Re} W_\zeta(g_{\mathrm{odd}} - T_v g_{\mathrm{odd}}, g_{\mathrm{odd}} - T_v g_{\mathrm{odd}}).$$
   - Specializing to $p = 2, m = 1$ ($v = \log 2$) and any even $g \in C^2(\mathbb{R}, \mathbb{C})$ ($\forall x,\; g(-x) = g(x)$) supported in $[-\eta, \eta]$ with $0 < \eta \le \frac{181}{500} - \frac{\log 2}{2}$ ($> \frac{3}{200}$, since $\log 2 < 0.6931471808 \implies \frac{181}{500} - \frac{\log 2}{2} > 0.0154$): $\operatorname{tsupport}(h) \subseteq [-\frac{181}{500}, \frac{181}{500}]$ and $h$ is strictly odd, so `AIP.fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths` gives unconditionally
     $$\frac{1}{1000} \int_{\mathbb{R}} \|g(x) - g(x - \log 2)\|^2 \, dx \le \operatorname{Re} W_\zeta(g - T_{\log 2} g, g - T_{\log 2} g),$$
     crossing past the $3/10$ barrier of `ACS.zeta_twoWindows_local_global` on the entire symmetric short-cycle sector at $m = 1$.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** `poleNode_erasure_of_orbitIntersection` — in the renormalized limit of both unshifted/even-shifted and torsion-aligned Ramanujan germs, the prime-side torsion intersection $-\operatorname{orbitIntersection}(q_\alpha, q_\beta)$ depends solely on the discrete fiber orders $(q_\alpha, q_\beta)$ and is independent of continuous nodes $x_\alpha$. Because survival requires $\sum_{q_\alpha = m} C_\alpha = 0$ on every order fiber (including under pole-node completion $x = 0$), $-\operatorname{orbitIntersection}(q_\alpha, q_\beta)$ pairs to $0$ identically on the entire survival cone, erasing $\Lambda(t)$ and leaving a source-independent cyclotomic-archimedean kernel.
- **Strongest positive survivor:** Three unconditional positive theorems: (1) `cyclotomicHarmonicKernel_nonneg` (unconstrained PSD of the pole-node-completed cyclotomic-harmonic kernel on $\mathbb{N}_+ \times \mathbb{R}_{\ge 0}$); (2) `torsionEnergy_dyadic_parity_split` & `tendsto_oddTorsionEnergy_add_half_log` (exact parity-split dyadic scale anomaly locating $\varphi(q)\log 2$ in the sign flip $+c_q$ vs $-c_q$ between even and odd frequencies); (3) `shortCycle_parity_orthogonal_split` & `even_shortCycle_m_one_re_W_ge` (midpoint parity-transposition law and coercive $1/1000$ Weil positivity of $g - T_{\log 2} g$ for all symmetric $C^2$ tests up to $\eta \le 181/500 - (\log 2)/2$).
- **New insight:** Periodic-germ renormalization survival erases pure torsion intersections because $(1-r)^{-1}$ divergences are per-order uniform; arithmetic prime weights survive only across *opposite-sign parity channels* (`2k` vs `2k+1`) where divergences cancel without per-order coefficient neutralization, while on short cycles $g - T_v g$ midpoint centering swaps symmetric windows into the odd Weil sector.
- **Status:** Dependency-closed paper proof complete; proceeding directly to Lean 4 formalization in `TransThresholdPairCorrelation/RamanujanParityTwinLimitsAndShortCycleObstruction.lean`.

## Log
- 2026-10-27 — created and completed dependency-closed paper proof in `2-fully-proven/`
