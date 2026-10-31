# Level of distribution, conductor-average positivity, and sublinear negative index for the complete Weil form at RH-complete resolution

- **ID:** complete-weil-conductor-level-of-distribution
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-3110/obstacles-summary.md (Q3, §2.5.1)
- **Statement:** For every level of distribution $0 < \theta < 1/2$, every $C^2$ profile $\varphi$ supported in $[0,1]$ with $\int \varphi^2 > 0$, and every overlap schedule $c_N$ with $c_N \ge 1$ eventually and $c_N^2 / \log N \to 0$ (covering the entire RH-complete window $c_N = 2(\log N)^\alpha$, $1/4 < \alpha < 1/2$, for `tiltedUnitSpline`), the normalized Ramanujan conductor prefix $\{v_1,\dots,v_M\}$ ($M = \lfloor N^\theta \rfloor$) forms a two-sided Riesz frame with constants $1 - 2\theta$ and $6$, satisfies the collective residual law $\sum_{m=1}^M \|(W_{N,c_N} - E_m(c_N)) v_m\|^2 / \sum_{m=1}^M E_m(c_N)^2 \to 0$, has strictly positive diverging conductor-average Weil energy with $o(M)$ nonpositive conductors, and restricts on $V_M = \operatorname{span}\{v_1,\dots,v_M\}$ ($\dim V_M = M$) to a quadratic form whose maximal nonpositive subspace dimension satisfies $\kappa(W_{N,c_N}|_{V_M}) / M \to 0$.

## Goal

Resolves Question Q3 and §2.5.1 of `obstacles-summary.md` affirmatively and unconditionally across the full Bombieri–Vinogradov exponent range $0 < \theta < 1/2$ up to the zero-log-loss overlap threshold $c_N^2 / \log N \to 0$, simultaneously establishing the whole-prefix upper Riesz frame and exact prime-power Gram locality for normalized Ramanujan horizon vectors.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, unconditional attack
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof (`[PROVED HERE]`)
- [x] 2 → 3  formalized: unconditional Lean 4 modules in `formal/GaloisForLFunctions/CompletedArithmeticForms/`, zero `sorry`, standard axioms `[propext, Classical.choice, Quot.sound]`

## Lean Formalization

All declarations reside in namespace `GaloisForLFunctions.CompletedArithmeticForms` and are wired into `formal/GaloisForLFunctions/CompletedArithmeticForms.lean`:

1. `formal/GaloisForLFunctions/CompletedArithmeticForms/RamanujanConductorFrames.lean`
   - `conductorSubspace`
   - `ramanujanConductor_lower_riesz` (`(1 - 2 * θ) * ∑ a_m^2 ≤ ‖∑ a_m • v_m‖^2`)
   - `finrank_conductorSubspace_eq` (`Module.finrank ℝ (conductorSubspace M N) = M`)
   - `normalizedRamanujanHorizonVector_gram_exact` (exact finite-horizon Gram expansion with prime-power off-diagonal coupling)
   - `ramanujanConductor_upper_riesz` (`‖∑ a_m • v_m‖^2 ≤ 6 * ∑ a_m^2`)
   - `sum_inner_normalizedRamanujanHorizonVector_sq_le` (dual Bessel bound `≤ 6 * ‖y‖^2`)
   - `sum_normalizedRamanujanMode_sq_le` (`∑_{m=1}^M c̃_m(n)^2 ≤ n * (1 + log M)^4`)
2. `formal/GaloisForLFunctions/CompletedArithmeticForms/PrimeResidualLevelOfDistribution.lean`
   - `exists_fullPrimeMatrix_levelOfDistribution` (`∑_{m=1}^M ‖P_N v_m - (log N - E_arith(m)) • v_m‖^2 ≤ C_p * M * log N` for `M * M ≤ N`)
3. `formal/GaloisForLFunctions/CompletedArithmeticForms/CompleteWeilResidualLevelOfDistribution.lean`
   - `exists_completeWeil_collective_residual_bound` (`∑_{m=1}^M ‖W_{N,c} v_m - E_m(c) • v_m‖^2 ≤ K_φ * (M * (log N + c^2 * log N + c^4) + c^3 * (log N)^5)`)
   - `tendsto_completeWeil_residual_div_mul_log_sq_zero`
   - `tendsto_completeWeil_residual_levelOfDistribution` (unconditional affirmative resolution of Q3)
   - `tendsto_tiltedUnitSpline_completeWeil_residual_rhComplete` (RH-complete specialization at `c_N = 2 * (log N)^α`, `0 < α < 1/2`)
4. `formal/GaloisForLFunctions/CompletedArithmeticForms/CompleteWeilConductorAveragePositivity.lean`
   - `tendsto_completeWeil_conductorAverage_atTop` and `eventually_completeWeil_conductorAverage_pos`
   - `tendsto_nonpositive_conductor_fraction_zero`
   - `finrank_nonpos_highConductor_subspace_le` and `tendsto_completeWeil_conductorSubspace_negIndex_div_zero`
   - `tendsto_tiltedUnitSpline_completeWeil_conductorAverage_atTop`, `tendsto_tiltedUnitSpline_nonpositive_conductor_fraction_zero`, `tendsto_tiltedUnitSpline_conductorSubspace_negIndex_div_zero`

## Complete Proof (`[PROVED HERE]`)

Fix $0 < \theta < 1/2$ and set $M = M_N := \lfloor N^\theta \rfloor$. For $N$ sufficiently large, $2 \le M$ and $M^2 \le N$. Write $\tilde{c}_m(n) := c_m(n)/\sqrt{\varphi(m)}$ and $v_m(n) := \tilde{c}_m(n)/\sqrt{n \log N}$ on $\{1,\dots,N\}$.

### 1. Exact prime-power Gram locality and two-sided whole-prefix Riesz frame (`0 < θ < 1/2`)

1. **Lower Riesz frame.** By `ramanujanPoleProfile_family_squareRoot_lower`, for $M \ge 2$ and $N \ge 2$,
   $$\sum_{n=1}^N \left(\sum_{m=1}^M a_m \frac{\tilde{c}_m(n)}{\sqrt{n}}\right)^2 \ge \bigl(\log(N+1) - 2\log M\bigr)\sum_{m=1}^M a_m^2 \ge (1 - 2\theta)(\log N)\sum_{m=1}^M a_m^2,$$
   and at $M = 1$, $\|v_1\|^2 = H_N / \log N \ge 1 \ge 1 - 2\theta$. Hence $\|\sum_{m=1}^M a_m v_m\|^2 \ge (1 - 2\theta)\sum_{m=1}^M a_m^2$, $\{v_1,\dots,v_M\}$ is linearly independent over $\mathbb{R}$, and $\dim_{\mathbb{R}} V_M = M$.

2. **Exact Gram decomposition and upper Riesz frame.** Using Kluyver's identity $c_m(n) = \sum_{d\mid\gcd(m,n)} d\,\mu(m/d)$, for $1 \le m,l \le M$ with $ml \le M^2 \le N$, every pair $d\mid m$, $e\mid l$ satisfies $L := \operatorname{lcm}(d,e) \le ml \le N$ and $de/L = \gcd(d,e)$, so
   $$\sum_{n=1}^N \frac{c_m(n)c_l(n)}{n} = \sum_{d\mid m}\sum_{e\mid l} \gcd(d,e)\,\mu(m/d)\,\mu(l/e)\,H_{\lfloor N/\operatorname{lcm}(d,e)\rfloor}.$$
   Expanding $H_{\lfloor N/L\rfloor} = (\log N + \gamma) - \log L + \eta(N,L)$ with $|\eta(N,L)| \le 4 L / N$, together with $\gcd(d,e) = \sum_{g\mid\gcd(d,e)} \varphi(g)$ and $\log\operatorname{lcm}(d,e) = \log d + \log e - \log\gcd(d,e)$, gives
   $$\langle v_m, v_l \rangle = \delta_{m,l}\left(1 + \frac{\gamma - \log m + \operatorname{tameDifferent}(m)}{\log N}\right) - \frac{K(m,l)}{\log N} + E_{m,l},$$
   where $K(m,l)$ vanishes unless $l\mid m$ ($l < m$, value $\sqrt{\varphi(l)/\varphi(m)}\Lambda(m/l)$) or $m\mid l$ ($m < l$, value $\sqrt{\varphi(m)/\varphi(l)}\Lambda(l/m)$).
   - **Diagonal:** $\operatorname{tameDifferent}(m) \le \log m$ and $\gamma \le 1 \le \log N$ give diagonal $\le 2$.
   - **Prime-power off-diagonal:** Weighted Schur with $w_m = m^{-1/2}$ bounds the upward sum ($l = mp^k \le M$) via $\sum_{t\le M} \Lambda(t)/t \le 2\log M$ by $2\sqrt{2}\log M$, and the downward sum ($l \mid m$) by $\sqrt{2}\log m \le \sqrt{2}\log M$, giving $\le (3\sqrt{2}\log M / \log N)\sum a_m^2 \le 3\sum a_m^2$ since $2\log M \le \log N$ and $3\sqrt{2} \le 6$.
   - **Floor-harmonic remainder:** $|E_{m,l}| \le \frac{4}{N\log N} f(m)f(l)$ with $f(m) = \varphi(m)^{-1/2}\sum_{d\mid m} d|\mu(m/d)|$. Multiplicativity over prime-power factors and $(p+1)^2/(p(p-1)) \le 1 + 7/p$ yield $\sum_{m=1}^M f(m)^2 \le e^7 M^2$, so $\sum_{m,l} a_m a_l E_{m,l} \le \frac{4 e^7 M^2}{N\log N}\sum a_m^2 \le \sum a_m^2$ once $\log N \ge 4 e^7$.
   Combining the three pieces yields $\|\sum_{m=1}^M a_m v_m\|^2 \le 6\sum_{m=1}^M a_m^2$, $\|v_m\|^2 \le 6$, and dual Bessel $\sum_{m=1}^M \langle y, v_m\rangle^2 \le 6\|y\|^2$.

3. **Divisor-totient packet envelope.** Writing $d = \gcd(m,n)$ and $r = m/d$, Hölder's identity gives $\tilde{c}_m(n)^2 = \mu(r)^2 \varphi(m)/\varphi(r)^2 \le \varphi(d)\,\mu(r)^2 r/\varphi(r)^2$. For squarefree $r$, $p/(p-1)^2 \le 4/p$ gives $r/\varphi(r)^2 \le \tau(r)^2/r$, while divisor-convolution submultiplicativity gives $\sum_{r=1}^M \tau(r)^2/r \le (1 + \log M)^4$. Summing over $d\mid n$ via $\sum_{d\mid n}\varphi(d) = n$ yields $\sum_{m=1}^M \tilde{c}_m(n)^2 \le n(1 + \log M)^4$.

### 2. Unconditional level of distribution for `fullPrimeMatrix` (`0 < θ < 1/2`)

Splitting `ramanujanPrimeResidual m N n` pointwise into the Mertens remainder profile and `normalizedPrimeCorrection`:
- **Mertens piece:** On $1 \le n \le M$, $1 + \log\lfloor N/n\rfloor \ge \frac{1}{3}\log N$, and §1.3 bounds the sum over $m \le M$ by $O(M\log N)$. On $M < n \le N$, comparing each period-$m$ block $[km+1, \min((k+1)m, N)]$ ($k \ge 2$) against the disjoint preceding full period $[(k-1)m+1, km]$ where $\sum_u \tilde{c}_m(u)^2 = m$ reduces to $\sum_{u=1}^N \frac{1}{u(1+\log\lfloor N/u\rfloor)^2} = O(1)$ (`wiener_constant_kernel_sum_le`), giving $O(M/\log N)$.
- **Prime-tower correction:** On $1 \le n \le \lfloor N/m\rfloor$, `abs_normalizedRamanujan_correction_le` gives $O((\log m)^2/\log N)$ per $m$. On $\lfloor N/m\rfloor < n \le N$ ($y = \lfloor N/n\rfloor < m$), periodic dilation $\sum_{r=0}^{m-1} \tilde{c}_m(rt)^2 \le \gcd(m,t)m$ and $\sum_{t\ge 1}\mu_m(t)\gcd(m,t) \le 2\log m$ yield period mean square $\le (8\log m)\sum_{t>y}\mu_m(t)$; covering $(\lfloor N/(y+1)\rfloor, \lfloor N/y\rfloor]$ by period-$m$ blocks and summing $1 \le y < m$ gives $O((\log m)^2/\log N) \le 192\log N$ per $m$.
Together, $\sum_{m=1}^M \|P_N v_m - (\log N - E_{\mathrm{arith}}(m))v_m\|^2 \le C_p M\log N$.

### 3. Complete-Weil collective residual and Q3 up to `c_N^2 / log N → 0`

Expanding $W_{N,c} v_m - E_m(c)v_m$ into its eight exact blocks (`completeWeilMatrix_ramanujan_residual_eq_at_every_overlap`):
- **Prime residual:** $O(M\log N)$ (§2).
- **Self error & pole moment error:** $O(M c^2)$ and $O(M c^4)$.
- **Center matrix:** Rank-1 pole shifts, $(n+j)^{-1}$ collar, and Toeplitz Hilbert kernel $|n-j|^{-1}$ acting on periodic unweighted Ramanujan modes ($\|u_m\|^2 \le 2/\log N$, Toeplitz norm $O(c\log N)$) give $O(M c^2\log N)$.
- **Separated cross error & near-center vector:** Offset triangle inequalities give $O(M c^4)$.
- **Upward prime residual:** Linear shell-correction bound $|\operatorname{shellCorrection}\,\varphi\,c\,m| \le 2 L_4 c$ (`completedShellCorrectionBudget` bounded via $|u|^{-1}|\operatorname{shellAutocorr}\,\varphi\,u| \le 2 L_4$) and weighted Schur on `upwardPrimeVector` (both row and column sums $O(c)$ after exact factorization $\sum_{k\mid T}\Lambda(k) = \log T$ canceled against $(\log N)^{-1}$ in the kernel) give $O(M c^2)$.
- **Near-Gamma downward vector:** Interior near-row terms have offset width $O(c)$ and entry $O(1)$; on $[N/(2e^2 c), N]$, the number of period-$m$ blocks is $O(c N / (c m)) = O(N/m)$ with harmonic slice weight $\sum_{k=\lfloor N/(4e^2 cm)\rfloor}^{\lceil N/m\rceil} k^{-1} = O(1 + \log c)$ — in fact, bounding $j^{-1} \le 2 e^2 c / N$ uniformly across the $O(N/(c m))$ blocks of $[N - \lceil 2e^2 c\rceil \dots]$ and exact shell support `|log(j/n)| ≤ c/N` gives zero $\log c$ loss, yielding $O(M c^2\log N)$ for the interior divisor-jet piece and $O(c^3(\log N)^5)$ for the exterior piece via §1.3.

Summing all eight blocks gives
$$\sum_{m=1}^M \|W_{N,c} v_m - E_m(c)v_m\|^2 \le K_\varphi \bigl(M(\log N + c^2\log N + c^4) + c^3(\log N)^5\bigr).$$
Since $M = \lfloor N^\theta\rfloor$ grows faster than $(\log N)^6$, whenever $c_N \ge 1$ eventually and $c_N^2 / \log N \to 0$, the RHS is $o(M(\log N)^2)$, whereas on $m \in (\lfloor M/2\rfloor, M]$ eventually $E_m(c_N) \ge \frac{\theta}{2}\log N$, so $\sum_{m=1}^M E_m(c_N)^2 \ge \frac{\theta^2}{8} M(\log N)^2$. Thus the Q3 ratio tends to $0$.

### 4. Conductor-average positivity, census, and `κ(W_{N,c_N}|_{V_M}) = o(M)`

1. **Diverging conductor average:** Every completed conductor energy is nonnegative (`completedConductorEnergy_nonneg`), and on $m \in (\lfloor M/2\rfloor, M]$ both $E_m(c_N) \ge \frac{\theta}{2}\log N$ and $\|v_m\|^2 \ge 1 - 2\theta$ hold eventually, while Cauchy–Schwarz and $\|v_m\|^2 \le 6$ bound $\sum_{m=1}^M |\langle r_m, v_m\rangle|$ by $o(M\log N)$. Hence $\frac{1}{M}\sum_{m=1}^M \operatorname{completeWeilEnergy}\,\varphi\,c_N\,N\,v_m \ge \frac{(1-2\theta)\theta}{8}\log N \to +\infty$.
2. **Census:** For any $\delta \in (0, 1/2]$, conductors $m \le \lfloor\delta M\rfloor$ contribute at most $\delta M$, while each nonpositive conductor $m \in (\lfloor\delta M\rfloor, M]$ forces $\bigl(\frac{(1-2\theta)\theta}{2}\log N\bigr)^2 \le 6\|r_m\|^2$, so at most $o(M)$ high conductors are nonpositive.
3. **Sublinear negative index:** For $U_N \le V_M$ nonpositive and $M_{\mathrm{low}} = \lfloor\delta M\rfloor$, Grassmann's formula gives $\dim U_N \le \dim(U_N \cap V_{(M_{\mathrm{low}}, M]}) + M_{\mathrm{low}}$. Prime-divisor splitting of $\operatorname{tameDifferent}(m)$ (`tameDifferent_le_split`) and the linear shell-correction bound concentrate $E_m(c_N)$ within $\frac{1-2\theta}{6}\theta\log N$ of $E_0 = \theta\log N$ across $(\lfloor\delta M\rfloor, M]$. Expanding an orthonormal basis $\{b_i\}_{i=1}^d$ of $W = U_N \cap V_{(M_{\mathrm{low}}, M]}$ in $\{v_m\}$, upper Riesz (`≤ 6`) bounds the energy-shift error by $E_0/2$, lower Riesz bounds $\sum_m A_{i,m}^2 \le (1-2\theta)^{-1}$, and weighted Young's inequality with Bessel's inequality $\sum_{i=1}^d \langle r_m, b_i\rangle^2 \le \|r_m\|^2$ yields
   $$d \le \frac{4}{(1 - 2\theta)\theta^2}\,\frac{\sum_{m=1}^M \|r_m\|^2}{(\log N)^2} = o(M),$$
   whence $\dim U_N / M \to 0$.

## Log
- 2026-10-31 — Paper proof and unconditional Lean 4 formalization completed in `CompletedArithmeticForms/`.
