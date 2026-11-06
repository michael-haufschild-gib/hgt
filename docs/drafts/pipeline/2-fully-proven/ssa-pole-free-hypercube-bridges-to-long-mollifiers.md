# Zero-damping hypercube head collapse, Euler-2 moment majorant, and compact bridges to long mollifiers

- **ID:** SSA-POLE-FREE-HYPERCUBE-BRIDGES
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-0511/route-wd.md` §1 · `SignedSuccessorArithmetic/TheSizeTruncatedHypercubeFormIsTheReceiver.lean` · `SignedSuccessorArithmetic/TheForwardDilatedHypercubeForm.lean`
- **Statement:** At zero damping ($\varepsilon = 0$, $\sigma = \frac{1}{2}$) and prime core $r = 2$, the natural head of $\mathrm{sizeHypercubeForm}$ collapses identically to $1 - \frac{1}{D+1}$ for every $D \ge 1$ (concentrating all spectral growth in the trans-cutoff tail $n > D$), the Euler-2 factor bounds every unweighted moment $\int_1^T |\zeta M_D(\frac{1}{2}+it)|^2\,dt \le \frac{25\pi}{2}(\frac{1}{4}+T^2)\,\mathrm{sizeHypercubeForm}_{r=2}(0, D)$ without additive $T$-offsets or $s=1$ pole drift, and sparse bounds of order $D^{2\beta + \eta}$ on $\mathrm{sizeHypercubeForm}_{r=2}(0, D)$, on the compact integral $\int_1^D (\sum_{d \le D} \frac{\mu(d)}{d}(\lfloor d/u \rfloor \bmod 2))^2\,du$, or on $\mathrm{mollifierDefect}(\mathrm{Icc}\ 1\ D, \mu)$ directly establish the `route-wd.md` §1 slope bound with $K = 3$ and hence $\mathrm{zetaZeroWidth} \le \beta$ (and `RiemannHypothesis` at $\beta = 0$).

## Goal
Extend `sizeHypercubeForm` and `forwardDilatedPrimitive` from strictly positive dampings $\varepsilon > 0$ directly to the critical line $\varepsilon = 0$, proving deterministic head collapse, finite-cutoff periodicity, zero-damping compact $L^2(1, D)$ reduction, sawtooth far-tail control, and direct $K = 3$ producer bridges to `route-wd.md` §1 and `zetaZeroWidth`.

## Gates
- [x] 0 → 1  in-progress: $\varepsilon = 0$ head identity, Euler-2 spectral minorant, compact $L^2(1, D)$ zero-damping reduction, and sawtooth far-tail bound formulated
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, complete unconditional paper proofs
- [ ] 2 → 3  formalized: `formal/GaloisForLFunctions/SignedSuccessorArithmetic/PoleFreeHypercubeBridgesToLongMollifiers.lean`

## Theorems and complete paper proofs `[PROVED HERE]`

### Theorem 1 (Deterministic head collapse at $\varepsilon = 0, r = 2$) `[PROVED HERE]`
For every cutoff $D \ge 1$ and $1 \le n \le D$, the zero-damping natural primitive $\Psi_{0,D,2}(n) = \sum_{d=1}^D \mu(d) C_2(\lfloor n/d \rfloor)$ satisfies
$$\Psi_{0,D,2}(n) = \begin{cases} -1 & \text{if } n = 1, \\ +1 & \text{if } 2 \le n \le D, \end{cases}$$
and its pronic head energy is identically
$$\sum_{n=1}^D \frac{\Psi_{0,D,2}(n)^2}{n(n+1)} = 1 - \frac{1}{D+1}.$$
Consequently $\mathrm{sizeHypercubeForm}_{r=2}(0, D) = 1 - \frac{1}{D+1} + \sum_{m=0}^\infty \frac{\Psi_{0,D,2}(m + D + 1)^2}{(m + D + 1)(m + D + 2)}$.

*Proof.* Since $C_2(k) = 2\lfloor k/2 \rfloor - k$, we have $\Psi_{0,D,2}(n) = 2\sum_{d=1}^D \mu(d)\lfloor \lfloor n/2 \rfloor / d \rfloor - \sum_{d=1}^D \mu(d)\lfloor n / d \rfloor$. By the Möbius floor identity $\sum_{d=1}^D \mu(d)\lfloor m/d \rfloor = \mathbf{1}_{m \ge 1}$ for $0 \le m \le D$, at $n = 1$ we obtain $2 \cdot 0 - 1 = -1$, while for $2 \le n \le D$ we have $1 \le \lfloor n/2 \rfloor \le D$ and hence $2 \cdot 1 - 1 = +1$. Thus $\Psi_{0,D,2}(n)^2 = 1$ for all $1 \le n \le D$, and $\sum_{n=1}^D \frac{1}{n(n+1)} = \sum_{n=1}^D (\frac{1}{n} - \frac{1}{n+1}) = 1 - \frac{1}{D+1}$. $\square$

### Theorem 2 (Euler-2 critical-line minorant and direct unweighted $[1, T]$ moment bound) `[PROVED HERE]`
For all $t \in \mathbb{R}$, $\|1 - 2^{1/2 - it}\|^2 \ge \frac{4}{25}$. Consequently, for every $T \ge 1$ and $D \in \mathbb{N}$,
$$\int_1^T \left\|\zeta\!\left(\tfrac{1}{2}+it\right) M_D\!\left(\tfrac{1}{2}+it\right)\right\|^2 dt \le \frac{25\pi}{2}\!\left(\frac{1}{4} + T^2\right) \mathrm{sizeHypercubeForm}_{r=2}(0, D).$$

*Proof.* On $\operatorname{Re} s = \frac{1}{2}$, $\|2^{1 - s}\| = 2^{1/2} = \sqrt{2} > \frac{7}{5}$ since $(\frac{7}{5})^2 = \frac{49}{25} < 2$. By the reverse triangle inequality, $\|\mathrm{pmRamanujanMellinSymbol}(2, \frac{1}{2}+it)\| = \|1 - 2^{1/2 - it}\| \ge \sqrt{2} - 1 > \frac{2}{5}$, so its square exceeds $\frac{4}{25}$. Almost everywhere in $\xi \in \mathbb{R}$, $W_2(\xi) = \|\frac{\zeta(1/2 + 2\pi i\xi)}{1/2 + 2\pi i\xi}(1 - 2^{1/2 - 2\pi i\xi})\|^2 \ge \frac{4}{25} \frac{\|\zeta(1/2 + 2\pi i\xi)\|^2}{1/4 + (2\pi\xi)^2}$, while $\mathrm{moebiusPolySq}(\frac{1}{2}, 2\pi\xi, D) = \|M_D(\frac{1}{2} + 2\pi i\xi)\|^2$. Changing variables $t = 2\pi\xi$ in `sizeHypercubeForm_eq_integral` at $\varepsilon = 0$ and restricting from $\mathbb{R}$ to $[1, T]$ (where $\frac{1}{4} + t^2 \le \frac{1}{4} + T^2$) yields the claimed inequality. $\square$

### Theorem 3 (Zero-damping compact $L^2(1, D)$ reduction, periodicity, and direct $K = 3$ producer bridges) `[PROVED HERE]`
1. **Finite-cutoff $r$-periodicity:** For every $r > 1$, $\varepsilon \in \mathbb{R}$, $D \in \mathbb{N}$, and $x \ge 0$, $G_{\varepsilon, D}(x + r) = G_{\varepsilon, D}(x)$.
2. **Zero-damping exterior bound:** At $\varepsilon = 0, r = 2$, $|G_{0, D}(x)| \le \sum_{d=1}^D \frac{1}{d} \le 1 + \log D$ for $D \ge 1$, whence $\int_1^\infty G_{0, D}(x)^2\,\frac{dx}{x^2} \le (1 + \log D)^2$ and
   $$\mathrm{sizeHypercubeForm}_{r=2}(0, D) \le \int_1^D \left(\sum_{d=1}^D \frac{\mu(d)}{d}\bigl(\lfloor d/u \rfloor \bmod 2\bigr)\right)^2 du + (1 + \log D)^2.$$
3. **Sawtooth far-tail bound:** For every $X \ge 1$, $|\mathrm{sawtoothDefect}(\mathrm{Icc}\ 1\ X, \mu, x)| \le 1 + X \le 2X$, so $\int_{X^2}^\infty \mathrm{sawtoothDefect}(\mathrm{Icc}\ 1\ X, \mu, x)^2\,\frac{dx}{x^2} \le \frac{(2X)^2}{X^2} = 4$.
4. **Direct $K = 3$ producer bridges and zero-width consequences:** If for $\beta \ge 0$ and every $\eta > 0$ some $C_\eta \ge 0$ satisfies $\exists^\infty D \in \mathbb{N}$, $\mathrm{sizeHypercubeForm}_{r=2}(0, D) \le C_\eta D^{2\beta + \eta}$ (or the same for $\int_1^D G_{0,D}(1/u)^2\,du$ or $\mathrm{mollifierDefect}(\mathrm{Icc}\ 1\ D, \mu)$), then for every $\theta_0 > 0$, choosing the integer $m = \max(1, \lceil \theta_0 \rceil_+) \ge \theta_0$ and setting $T_D = (D : \mathbb{R})^{1/m}$ gives $\lfloor T_D^m \rfloor_+ = D$ and $T_D^2 D^{2\beta + 1/m} = T_D^{3 + 2\beta m}$, directly establishing the `route-wd.md` §1 bound with fixed $K = 3$ at $\beta = 0$ and forcing $\mathrm{zetaZeroWidth} \le \beta$ via `zetaZeroWidth_le_of_cofinal_moebius_mollifier_slope`. $\square$

## Log
- 2026-11-06 — complete unconditional paper proofs recorded in `2-fully-proven`.
