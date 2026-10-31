# Prime-Side Hecke-Defect Multiplicity Bounds and Quantitative Heat–Collision Charge Bridges

- **ID:** hecke-defect-multiplicity-and-heat-collision-bridge
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ConjugateDiagonalGeometry · CollisionChargeIncrements follow-up
- **Statement:** Unconditional prime-polynomial plus Hecke-defect upper bounds on horizontal fibre multiplicity $H(\gamma)$ and unit-window collision increments $\Delta O(T)$ at scales $1 \le L \le 4\log(1+|\gamma|)$ (yielding $\Delta O(T) \ll \log T$ from bounded prime polynomial and Hecke defect at $L \asymp \log T$, and $H(\gamma) \ll \frac{\log T}{\log\log T} + \operatorname{heckeDefect}$ unconditionally in primes at $L = \frac{1}{4}\log\log T$), together with exact parity and Calogero–Moser inward-drift falsifications of literal $N(t) \le O(2\pi e^{40/t} + C)$ and unconditional moving-barrier, global, and dyadic quantitative bridges between $O(T)$ and $N(t)$.

## Goal
1. Upgrade the trivial quadratic unit-window bound $\Delta O(T) \ll (\log T)^2$ by expressing horizontal fibre multiplicity $H(\gamma)$ and $\Delta O(T)$ in terms of the prime polynomial $\operatorname{Re}\Pi_{F_L}$ and the conjugate-diagonal symmetric Hecke defect $\operatorname{heckeDefect}(\operatorname{twist}_\gamma h, L)$ at $L \asymp \log T$ and $L \asymp \log\log T$.
2. Test and resolve the conjectured heat-to-charge inequality $N(t) \le O(2\pi e^{40/t} + C)$: isolate the exact factor-of-2 four-quadrant parity obstruction and the cubic Calogero–Moser inward-drift obstruction to zero-buffer descent ($C = 0$), and establish unconditional two-sided quantitative bridges between $N(t)$ and $O(T)$.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `HeckeDefectHorizontalMultiplicity` and `CollisionChargeHeatCountBridge`, `lake --old env lean` green, `#print axioms` PASS

## Approach

### Part I: Prime-Side + Hecke-Defect Bounds on $H(\gamma)$ and $\Delta O(T)$ `[PROVED HERE]`
1. **Off-line Fibre Reduction of $\Delta O(T)$:**
   On the unit window $W(T) = \{\rho : \xi(\rho) = 0,\, 0 < \operatorname{Re}\rho < 1,\, T \le \operatorname{Im}\rho < T+1\}$, $\Delta O(T) = \sum_{\rho \in W(T)} m_\rho(H(\operatorname{Im}\rho) - m_\rho)$. Every critical zero $\rho = \frac{1}{2} + i\gamma$ whose ordinate carries no off-line zero has $H(\gamma) = m_\rho$ and contributes $0$; on any ordinate carrying off-line zeros, splitting into critical and off-line parts yields
   $$\Delta O(T) \le 2 \Big(\max_{\rho \in W_{\mathrm{off}}(T)} H(\operatorname{Im}\rho)\Big) \, n_{\mathrm{off}}(T), \qquad \Delta O(T) \le \Big(\max_{\rho \in W(T)} (H(\operatorname{Im}\rho) - 1)\Big) \, n(T).$$
   Since $n_{\mathrm{off}}(T) \le n(T) \ll \log T$, any bound $H(\gamma) \le B$ on off-line ordinates in $[T, T+1)$ yields $\Delta O(T) \le 2 B \, n_{\mathrm{off}}(T) \ll B \log T$.

2. **Continuous Hecke-Averaged Bump and Hyperbolic $\cosh$ Coercivity:**
   Let $h \in C_c^\infty([-1/4, 1/4])$ be real, even, nonnegative with $\int_{\mathbb{R}} h = 1$, and define for $L > 0$:
   $$F_L(u) := \frac{1}{2L} \int_{u-L}^{u+L} h(v)\,dv.$$
   Then $F_L \in C_c^\infty([-(L + 1/4), L + 1/4])$ is real, even, nonnegative, satisfies $0 \le F_L(u) \le \frac{1}{2L}$, $\int_{\mathbb{R}} F_L = 1$, $\int_{\mathbb{R}} \|F_L\|^2 \le \frac{1}{2L}$, and $F_L''(u) = \frac{h'(u+L) - h'(u-L)}{2L}$, so $B_{F_L} = 4(\|F_L\|_1 + \|F_L''\|_1) \le 4(1 + \|h'\|_1 / L)$ is uniformly bounded for $L \ge 1$.
   At any $\zeta$-zero $\rho = \frac{1}{2} + \delta_\rho + i\gamma$ on the horizontal line $\operatorname{Im}\rho = \gamma$, evenness and $F_L \ge 0$ give
   $$\operatorname{tr}(\operatorname{twist}_\gamma F_L)(\rho) = \int_{\mathbb{R}} F_L(u) \cosh(\delta_\rho u)\,du \ge \int_{\mathbb{R}} F_L(u)\,du = 1.$$
   Summing $m_\rho |\operatorname{tr}(\operatorname{twist}_\gamma F_L)(\rho)|^2$ over the horizontal fibre gives $H(\gamma) \le D(\operatorname{twist}_\gamma F_L) = \operatorname{Re} W_\zeta(\operatorname{twist}_\gamma F_L, \operatorname{twist}_\gamma F_L) + \Delta(\operatorname{twist}_\gamma F_L)$.

3. **Sinc-Cancelled Off-Line Defect Decomposition:**
   By Fubini, $\operatorname{tr}(\operatorname{twist}_\gamma F_L)(\rho) = \frac{1}{2L}\int_{-L}^L e^{\ell(\delta_\rho + i\omega_\rho)} u_\rho\,d\ell$, where $\omega_\rho = \operatorname{Im}\rho - \gamma$, $u_\rho = \operatorname{tr}(\operatorname{twist}_\gamma h)(\rho)$, and $v_\rho = \operatorname{tr}(\operatorname{twist}_\gamma h)(1 - \bar{\rho})$. Splitting $e^{\ell\delta_\rho} u_\rho - e^{-\ell\delta_\rho} v_\rho = (u_\rho - v_\rho) + ((e^{\ell\delta_\rho} - 1)u_\rho - (e^{-\ell\delta_\rho} - 1)v_\rho)$:
   - By Cauchy–Schwarz on $[-L, L]$, $(e^x - 1)^2 \le (e^x - e^{-x})^2 = \operatorname{depthKernel}(1, x)$, scale monotonicity $|\ell| \le L \implies \operatorname{depthKernel}(\ell, \delta) \le \operatorname{depthKernel}(L, \delta)$, and reflection symmetry of $\zeta$'s divisor, the second term sums to at most $4\,\operatorname{heckeDefect}(\operatorname{twist}_\gamma h, L)$.
   - For the first term, $u_\rho - v_\rho = 2i \int_{-1/4}^{1/4} h(x)\sinh(\delta_\rho x)\sin(\omega_\rho x)\,dx$ satisfies $|u_\rho - v_\rho| \le C_1 |\omega_\rho|$ for $|\omega_\rho| \le 1$ and $|u_\rho - v_\rho| \le \frac{C_2}{(1 + |\omega_\rho|)^2}$ for $|\omega_\rho| > 1$, while $\big|\frac{1}{2L}\int_{-L}^L e^{i\ell\omega_\rho}\,d\ell\big| \le \min(1, \frac{1}{L|\omega_\rho|})$. Hence $\big|\frac{1}{2L}\int_{-L}^L e^{i\ell\omega_\rho}(u_\rho - v_\rho)\,d\ell\big|^2 \le \frac{C_3}{L^2(1 + \omega_\rho^2)}$, which sums via `lorentzMass_le_log` to $\frac{C_4(1 + \log(|\gamma| + 4))}{L^2}$.

4. **Master Inequality and Scale Specializations:**
   Combining `re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial` and `re_archPart_le_decay` at $\xi = -\gamma/(2\pi)$ and aperture $a = L + 1/4$ gives, for all $\gamma \in \mathbb{R}$ and $1 \le L \le 4\log(1 + |\gamma|)$:
   $$H(\gamma) \le C_*\!\left(1 + \frac{\log(2 + |\gamma|)}{L}\right) - \operatorname{Re}\Pi_{F_L}\!\left(\lfloor e^{2L + 1/2}\rfloor, -\frac{\gamma}{2\pi}\right) + 4\,\operatorname{heckeDefect}(\operatorname{twist}_\gamma h, L).$$
   - At $L = c \log T$ ($0 < c \le 4$): $\frac{\log(2 + |\gamma|)}{L} = O(1)$, so boundedness of $-\operatorname{Re}\Pi_{F_{c\log T}}$ and $\operatorname{heckeDefect}(\operatorname{twist}_\gamma h, c\log T)$ across $\gamma \in [T, T+1)$ yields $H(\gamma) = O(1)$ and $\Delta O(T) \ll n_{\mathrm{off}}(T) \ll \log T$.
   - At $L = \frac{1}{4}\log\log T$: $\Lambda(n)/\sqrt{n} \le 2$ and $\|k_{F_L}\|_\infty \le \frac{1}{2L}$ give $|\operatorname{Re}\Pi_{F_L}| \le \frac{2 e^{2L+1/2}}{L} = \frac{8 e^{1/2}\sqrt{\log T}}{\log\log T}$, discharging the prime polynomial unconditionally and proving $H(\gamma) \ll \frac{\log T}{\log\log T} + \operatorname{heckeDefect}(\operatorname{twist}_\gamma h, \frac{1}{4}\log\log T)$.

### Part II: Testing $N(t) \le O(2\pi e^{40/t} + C)$ and Quantitative Bridges `[PROVED HERE]`
1. **Quadrant Accounting and Parity Obstruction:**
   $H_t(-z) = H_t(z)$ and $H_t(\bar{z}) = \overline{H_t(z)}$ partition nonreal zeros into upper/lower half-planes: $N(t) = 2 N_\uparrow(t)$ (`upperHalfNonrealZeroCount t`). At $t = 0$, $\xi(\sigma) \ne 0$ for all $\sigma \in \mathbb{R}$ (`xi_ne_zero_of_ofReal`) implies that the unheated window count `xiWindowNonrealZeroCount T` ($\sum_{H_0(z)=0,\, z.\mathrm{im}\ne 0,\, |z.\mathrm{re}| < T} \operatorname{zeroMult}(H_0, z)$) equals $2 \cdot \operatorname{xiStripWindowOffLineOrder}(T) \le 2\, O(T)$. If $\xi$ had $k \ge 1$ simple off-line pairs on distinct ordinates with no critical zero on those ordinates, then $\sup_T O(T) = 2k$ whereas $N(t) = 4k$ for small $t > 0$ (`exists_pos_collision_free_below_of_finite_nonrealCopies`), violating $N(t) \le O(f(t))$ for every height function $f$.

2. **Cubic Calogero–Moser Inward-Drift Obstruction ($C = 0$):**
   For $P(z) = ((z - A)^2 + y_0^2)(z - (A + r))$ with $0 < r < A$, $y_0 > 0$, $0 < t < y_0^2/6$, and $r^2 < 3(y_0^2 - 6t)$, every nonreal root of $P$ has $|\operatorname{Re} z| = A$, so open $(-A, A)$ contains $0$ nonreal roots at $t = 0$. Under `polyHeat t`, $Q_t(A + w) = w^3 - r w^2 + (y_0^2 - 6t)w - r(y_0^2 - 2t)$ satisfies $Q_t'(A + w) > 0$ on $\mathbb{R}$ and $Q_t(A + r) = -4rt < 0$, forcing its unique real root $A + w_1$ to satisfy $w_1 > r$. By Vieta ($w_1 + 2u = r$), the conjugate nonreal pair $A + u \pm iv$ of $Q_t$ has $u = (r - w_1)/2 < 0$ and $|A + u| < A$, strictly inside $(-A, A)$.

3. **Moving-Barrier, Global, and Dyadic Quantitative Bridges:**
   - **Forward real-zero stability at $t = 0$:** Extending `exists_ball_real_zeros_forward` from $t > 0$ to $t \ge 0$ via one-sided time-Taylor locally uniform convergence `riemannHeat (max s 0) → riemannHeat 0` on $\mathcal{N}[>] 0$ and `exists_real_zeros_forward` at $t = 0$, any continuous barrier $R : \mathbb{R} \to \mathbb{R}$ with $R > 0$ on $[0, t]$ ($0 < t \le 1/8$), $2\pi e^{40/t} \le R(t)$, and no nonreal zeros of $H_s$ on $|\operatorname{Re} z| = R(s)$ for $s \in [0, t]$ yields right-local nonincrease and left-local lower semicontinuity of the windowed nonreal count $N_{\mathrm{in}}(s)$ on $[0, t]$, proving $N(t) \le \operatorname{xiWindowNonrealZeroCount}(R(0)) = 2\,\operatorname{xiStripWindowOffLineOrder}(R(0)) \le 2\,O(R(0))$ and $N_\uparrow(t) \le O(R(0))$.
   - **Global bound and finiteness equivalence:** Unconditionally, $(\forall T \ge 0,\, O(T) \le M) \implies \forall t > 0,\, N(t) \le 2M$ and $N_\uparrow(t) \le M$, closing $(\exists B,\, \forall t > 0,\, N(t) \le B) \iff (\exists M,\, \forall T \ge 0,\, O(T) \le M)$.
   - **Reverse dyadic finite-height bound:** Summing `xiCollisionIncrement_le_two_mul` over unit windows covering $[X, 2X]$ and bounding deep off-line copies via `exists_card_deep_le_heat_count_at_uniform_depth_scale` yields $O(2X) - O(X) \le C_1 (\log X)^2 N(t) + C_2 (\log X) \, n_{\mathrm{off}, < d}([X, 2X])$ for $X \ge X_0$, $0 < d \le 1/2$, and $0 < t \le c d^2 / \log X$.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:**
  1. *Height-uniform $\ell^1$ prime majorant at $L \asymp \log T$:* At $L = c\log T$, the height-uniform prime envelope scales as $O(T^{2c}/\log T) \gg \log T$ (`not_exists_eventually_atTop_PX_power_saving`), so bounding $\Delta O(T) \ll \log T$ at $L \asymp \log T$ requires single-height cancellation of $\operatorname{Re}\Pi_{F_L}$ together with $\operatorname{heckeDefect}$.
  2. *Literal unnormalized $N(t) \le O(2\pi e^{40/t} + C)$ and unbuffered $C = 0$ descent:* $N(t)$ counts all four quadrants ($4k$ for $k$ minimal off-line quartets) while $O(T)$ counts ordered pairs in the upper strip ($2k$), making literal $N(t) \le O(f(t))$ false by a factor of $2$ in the minimal-collision regime; independently, `polyHeat t` on $((z - A)^2 + y_0^2)(z - (A + r))$ pushes the nonreal pair at $|\operatorname{Re} z| = A$ strictly inward to $|\operatorname{Re} z| < A$, killing unbuffered ($C = 0$) horizontal window monotonicity.
- **Strongest positive survivor:**
  1. Single-height prime-polynomial + Hecke-defect inequality $H(\gamma) \le C_*(1 + \frac{\log(2+|\gamma|)}{L}) - \operatorname{Re}\Pi_{F_L} + 4\,\operatorname{heckeDefect}(\operatorname{twist}_\gamma h, L)$, yielding $\Delta O(T) \ll \log T$ from bounded prime polynomial + Hecke defect at $L = c\log T$ and unconditional-in-primes $H(\gamma) \ll \frac{\log T}{\log\log T} + \operatorname{heckeDefect}$ at $L = \frac{1}{4}\log\log T$.
  2. Normalized moving-barrier descent $N(t) \le 2\,O(R(0))$ (and $N_\uparrow(t) \le O(R(0))$) along any continuous zero-free barrier $R$ on $[0, t]$ above the Ki–Kim–Lee horizon, global $N(t) \le 2 \sup_T O(T)$, and reverse dyadic $O(2X) - O(X) \ll (\log X)^2 N(c d^2 / \log X) + (\log X)\, n_{\mathrm{off}, < d}([X, 2X])$.
- **New insight:**
  1. Continuous Hecke averaging $F_L = \frac{1}{2L}\mathbf{1}_{[-L, L]} * h$ simultaneously achieves $\cosh(\delta u) \ge 1$ lower coercivity on the full fibre $\operatorname{Im}\rho = \gamma$, $O(1/L)$ $L^2$-norm reduction of the archimedean density, and $O((\log T)/L^2)$ sinc suppression of local reflection mismatch, isolating `heckeDefect` and `primePolynomial` as the sole obstructions to $H(\gamma) = O(1)$ and $\Delta O(T) \ll \log T$.
  2. Linking $N(t)$ to $O(T)$ at finite height requires both the factor-of-2 upper-half-plane normalization ($N = 2 N_\uparrow$) and a horizontal barrier buffer absorbing outward real-zero repulsion.
- **Status:** Dependency-closed paper proofs complete; Lean 4 formalization in `GaloisForLFunctions.ConjugateDiagonalGeometry.HeckeDefectHorizontalMultiplicity` and `GaloisForLFunctions.ConjugateDiagonalGeometry.CollisionChargeHeatCountBridge` next.

## Log
- 2026-10-31 — created and proved in `2-fully-proven`
