# Prime-Side Hecke-Defect Multiplicity Bounds and Quantitative Heat–Collision Charge Bridges

- **ID:** hecke-defect-multiplicity-and-heat-collision-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ConjugateDiagonalGeometry` · `CollisionChargeIncrements` follow-up
- **Statement:**
  1. **Off-line fibre reduction and prime + Hecke-defect bounds on $H(\gamma)$ and $\Delta O(T)$:**
     With $F_L(u) = \frac{1}{2L}\int_{u-L}^{u+L} h_0(v)\,dv$ (`heckeAvgBump L`) and $h_0$ an even normalized bump supported in $[-1/4, 1/4]$, there exists $C_* > 0$ such that for all $\gamma \in \mathbb{R}$ and $1 \le L \le 4\log(1 + |\gamma|)$,
     $$H(\gamma) \le C_*\!\left(1 + \frac{\log(2 + |\gamma|)}{L}\right) - \operatorname{Re}\Pi_{F_L}\!\left(\lfloor e^{2(L + 1/4)}\rfloor, -\frac{\gamma}{2\pi}\right) + 4\,\operatorname{heckeDefect}(\operatorname{baseTwistTest}\,\gamma, L).$$
     At $L = c\log T$ ($0 < c \le 4$), bounded $-\operatorname{Re}\Pi_{F_L} + 4\,\operatorname{heckeDefect} \le M$ on off-line ordinates in $[T, T+1)$ gives $\Delta O(T) \le C(1 + M)\log T$. At $L = \frac{1}{4}\log\log|\gamma|$, the prime polynomial is discharged unconditionally (`primeEnvelope_heckeAvgBump_le`), yielding $H(\gamma) \le C\frac{\log|\gamma|}{\log\log|\gamma|} + 4\,\operatorname{heckeDefect}(\operatorname{baseTwistTest}\,\gamma, \frac{1}{4}\log\log|\gamma|)$.
  2. **Parity and Calogero–Moser inward-drift obstructions and quantitative bridges between $N(t)$ and $O(T)$:**
     - $N(t) = 2 N_\uparrow(t)$ (`upperHalfNonrealZeroCount t`), while `xiWindowNonrealZeroCount T` $= 2\,\operatorname{xiStripWindowOffLineOrder}(T) \le 2\,O(T)$. Under finite off-line count and minimal off-line fibres ($m_\rho = 1$, $H(\operatorname{Im}\rho) = 2$), $\forall^\infty t \in \mathcal{N}[>] 0,\, N(t) \le O(f(t)) \iff \mathrm{RH}$ for every $f : \mathbb{R} \to \mathbb{R}$.
     - For every $A > 1/4$, `inwardDriftCubic A` $= ((X - A)^2 + 4)(X - (A + 1/2))$ has $0$ nonreal roots in $|\operatorname{Re} z| < A$, whereas `polyHeat (1/4) (inwardDriftCubic A)` has $2$ nonreal roots strictly inside $|\operatorname{Re} z| < A$, falsifying unbuffered ($C = 0$) horizontal window monotonicity.
     - Along any continuous barrier $R : \mathbb{R} \to \mathbb{R}$ with $R > 0$ on $[0, t]$ ($0 < t \le 1/8$), $2\pi e^{40/t} \le R(t)$, and no nonreal zeros of $H_s$ on $|\operatorname{Re} z| = R(s)$ for $s \in [0, t]$, $N(t) \le 2\,O(R(0))$ and $N_\uparrow(t) \le O(R(0))$. Globally, $(\forall T \ge 0,\, O(T) \le M) \implies \forall t > 0,\, N(t) \le 2M \land N_\uparrow(t) \le M$, closing $(\exists B,\, \forall t > 0,\, N(t) \le B) \iff (\exists M,\, \forall T \ge 0,\, O(T) \le M)$. Conversely, $O(2X) - O(X) \le C_1 (\log X)^2 N(t) + C_2 (\log X)\, n_{\mathrm{off}, < d}([X, 2X))$ for $X \ge X_0$, $0 < d \le 1/2$, and $0 < t \le c d^2 / \log X$.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `HeckeDefectHorizontalMultiplicity` and `CollisionChargeHeatCountBridge`, `lake --old env lean` green, `#print axioms` PASS

## Proof `[PROVED HERE]`
1. **Off-line fibre reduction:** On $W(T)$, critical zeros on ordinates carrying no off-line zero satisfy $H(\gamma) = m_\rho$ and contribute $0$ to $\Delta O(T)$; splitting off-line-carrying ordinates into critical and off-line parts gives $\Delta O(T) \le 2 (\max_{\rho \in W_{\mathrm{off}}(T)} H(\operatorname{Im}\rho)) \, n_{\mathrm{off}}(T)$ and $\Delta O(T) \le (\max_{\rho \in W(T)} (H(\operatorname{Im}\rho) - 1)) \, n(T)$.
2. **Continuous Hecke averaging and $\cosh$ coercivity:** $F_L \in C_c^\infty([-(L+1/4), L+1/4])$ is even, nonnegative, with $\int F_L = 1$, $\|F_L\|_\infty \le \frac{1}{2L}$, $\|F_L\|_2^2 \le \frac{1}{2L}$, and `envelope` uniformly bounded for $L \ge 1$. On $\operatorname{Im}\rho = \gamma$, $\operatorname{Re}\operatorname{tr}(\operatorname{twist}_\gamma F_L)(\rho) = \int F_L(u)\cosh(\delta_\rho u)\,du \ge 1$, giving $H(\gamma) \le D(\operatorname{twist}_\gamma F_L) = \operatorname{Re} W_\zeta(\operatorname{twist}_\gamma F_L, \operatorname{twist}_\gamma F_L) + \Delta(\operatorname{twist}_\gamma F_L)$.
3. **Sinc-cancelled off-line defect:** Writing $\operatorname{tr}(\operatorname{twist}_\gamma F_L)(\rho) = \frac{1}{2L}\int_{-L}^L e^{\ell(\delta_\rho + i\omega_\rho)} u_\rho\,d\ell$ with $\omega_\rho = \operatorname{Im}\rho - \gamma$ and splitting $e^{\ell\delta_\rho}u_\rho - e^{-\ell\delta_\rho}v_\rho = (u_\rho - v_\rho) + ((e^{\ell\delta_\rho}-1)u_\rho - (e^{-\ell\delta_\rho}-1)v_\rho)$ bounds the second part by $4\,\operatorname{heckeDefect}(\operatorname{baseTwistTest}\,\gamma, L)$ via $(e^x - 1)^2 \le \operatorname{depthKernel}(1, x)$ and reflection symmetry, and bounds the first part by $\frac{C_{\mathrm{sinc}}(1 + \log(|\gamma| + 4))}{L^2}$ via oddness cancellation $\|u_\rho - v_\rho\| \le |\omega_\rho|$ near $\omega_\rho = 0$, sinc decay, and `lorentzMass_le_log`. Combining with the explicit formula `re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial` and `re_archPart_le_decay` yields the master inequality and both scale specializations.
4. **Parity and cubic inward-drift obstructions:** $H_t(-z) = H_t(z)$ and $H_t(\bar{z}) = \overline{H_t(z)}$ yield $N(t) = 2 N_\uparrow(t)$, whereas at $t = 0$, $\xi(\sigma) \ne 0$ on $\mathbb{R}$ maps nonreal zeros of $H_0$ in $|\operatorname{Re} z| < T$ to $2\,\operatorname{xiStripWindowOffLineOrder}(T)$, which equals $2\,O(T)$ under minimal off-line fibres while $N(t) = 2\,\operatorname{xiWindowNonrealZeroCount}(T_0)$ for small $t > 0$. For $P_A(X) = ((X - A)^2 + 4)(X - (A + 1/2))$, $Q = \operatorname{polyHeat}(1/4, P_A)$ satisfies $Q(A + w) = w^3 - \frac{1}{2}w^2 + \frac{5}{2}w - \frac{7}{4}$, has strictly positive derivative on $\mathbb{R}$, unique real root $A + w_1$ with $w_1 > 1/2$, and conjugate nonreal pair $A + u \pm iv$ with $u = \frac{1/2 - w_1}{2} \in (-A, 0)$, so $|A + u| < A$.
5. **Barrier, global, and dyadic bridges:** One-sided locally uniform convergence `riemannHeat (max s 0) → riemannHeat 0` on $\mathcal{N}[>] 0$ combined with `exists_real_zeros_forward` extends `exists_ball_real_zeros_forward` to $t \ge 0$ (`exists_ball_real_zeros_forward_nonneg`), giving right-local nonincrease and left-local lower semicontinuity of `riemannHeatWindowNonrealCount s (R s)` on $[0, t]$ and closing $N(t) \le 2\,O(R(0))$ above the Ki–Kim–Lee horizon $2\pi e^{40/t}$. Taking a fixed zero-free vertical line above all off-line ordinates gives $N(t) \le 2 M$ whenever $O(T) \le M$ for all $T \ge 0$. Summing `xiCollisionIncrement_le_two_mul` over unit steps in $[X, 2X)$ and bounding deep off-line copies via `exists_card_deep_le_heat_count_at_uniform_depth_scale` yields the reverse dyadic inequality.

## No-go closure
- **Exact killing theorem/mechanism:**
  1. Height-uniform $\ell^1$ prime majorants at $L = c\log T$ grow as $O(T^{2c}/\log T) \gg \log T$ (`not_exists_eventually_atTop_PX_power_saving`), so $\Delta O(T) \ll \log T$ at $L \asymp \log T$ requires single-height cancellation of $-\operatorname{Re}\Pi_{F_L} + 4\,\operatorname{heckeDefect}$.
  2. `eventually_nonrealZeroCount_le_collisionCharge_iff_rh_of_minimal_fibres` kills literal unnormalized $N(t) \le O(f(t))$ by a factor of $2$ in the minimal-collision regime; `exists_polyHeat_nonreal_root_inward_drift` kills unbuffered ($C = 0$) horizontal window monotonicity.
- **Strongest positive survivor:**
  1. `exists_horizontalMultiplicity_le_primePolynomial_add_heckeDefect`, `exists_xiCollisionIncrement_le_log_of_prime_and_heckeDefect_at_log_scale`, and `exists_horizontalMultiplicity_le_log_div_log_log_add_heckeDefect`.
  2. `nonrealZeroCount_le_two_mul_collisionCharge_of_barrier`, `nonrealZeroCount_le_two_mul_of_collisionCharge_bdd`, `exists_nonrealZeroCount_le_iff_exists_collisionCharge_le`, and `exists_dyadicCollisionCharge_le_log_sq_mul_nonrealZeroCount_add_shallow`.
- **New insight:** Continuous Hecke averaging $F_L = \frac{1}{2L}\mathbf{1}_{[-L, L]} * h_0$ simultaneously enforces $\cosh(\delta u) \ge 1$ lower coercivity on the horizontal fibre, $O(1/L)$ $L^2$ archimedean decay, and $O((\log T)/L^2)$ sinc suppression of local reflection mismatch; connecting $N(t)$ to $O(T)$ at finite height requires both the factor-of-2 upper-half-plane normalization ($N = 2 N_\uparrow$) and a barrier absorbing real-zero repulsion.

## Lean verification
Modules (wired into `GaloisForLFunctions/ConjugateDiagonalGeometry.lean`):
- `GaloisForLFunctions/ConjugateDiagonalGeometry/HeckeDefectHorizontalMultiplicity.lean`:
  `xiCollisionIncrement_le_max_fibre_mul_unitWindowOrder`,
  `xiCollisionIncrement_le_two_mul_max_offLineFibre_mul_offLineOrder`,
  `baseTwistTest`, `heckeAvgBump`, `envelope_heckeAvgBump_le`,
  `one_le_re_tr_twist_of_im_eq`, `horizontalMultiplicity_le_collidedForm_heckeAvg`,
  `tr_twist_heckeAvgBump_eq`, `offLineDefect_heckeAvg_le_heckeDefect_add_lorentz`,
  `exists_horizontalMultiplicity_le_primePolynomial_add_heckeDefect`,
  `exists_xiCollisionIncrement_le_log_of_prime_and_heckeDefect_at_log_scale`,
  `primeEnvelope_heckeAvgBump_le`,
  `exists_horizontalMultiplicity_le_log_div_log_log_add_heckeDefect`.
- `GaloisForLFunctions/ConjugateDiagonalGeometry/CollisionChargeHeatCountBridge.lean`:
  `upperHalfNonrealZeroCount`, `nonrealZeroCount_eq_two_mul_upperHalfNonrealZeroCount`,
  `xiWindowNonrealZeroCount`, `xiWindowNonrealZeroCount_eq_two_mul_offLineOrder`,
  `xiWindowNonrealZeroCount_le_two_mul_collisionCharge`,
  `eventually_nonrealZeroCount_le_collisionCharge_iff_rh_of_minimal_fibres`,
  `inwardDriftCubic`, `exists_polyHeat_nonreal_root_inward_drift`,
  `exists_ball_real_zeros_forward_nonneg`, `riemannHeatWindowNonrealCount`,
  `nonrealZeroCount_le_two_mul_collisionCharge_of_barrier`,
  `upperHalfNonrealZeroCount_le_collisionCharge_of_barrier`,
  `nonrealZeroCount_le_two_mul_of_collisionCharge_bdd`,
  `upperHalfNonrealZeroCount_le_of_collisionCharge_bdd`,
  `exists_nonrealZeroCount_le_iff_exists_collisionCharge_le`,
  `xiWindowShallowOffLineOrder`, `xiHorizontalCollisionCharge_sub_le_two_mul_offLine`,
  `exists_dyadicCollisionCharge_le_log_sq_mul_nonrealZeroCount_add_shallow`.

Both modules pass `lake --old env lean` with exit code `0`, default limits, and zero warnings; all `#print axioms` checks report only `[propext, Classical.choice, Quot.sound]`.
