# The heat-deformed archimedean state as a Pontryagin homotopy

- **ID:** heat-deformed-archimedean-state
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3110/obstacles-summary.md` §2.5.2 (Route SC)
- **Statement:** From the Gaussian-weighted theta kernel $\Phi_t(x) = \Phi(x) e^{t x^2}$ of $H_t$ alone (source data only), construct a family of Hermitian states $\varphi_c^{(t)} : \mathrm{Aff}(\mathbb{Q}) \to \mathbb{C}$ ($c > 0$, $t > 0$) continuous in $t$ on $(0, \infty)$ such that $\kappa(\varphi_c^{(t)}) < \infty$ for every $t > 0$, $\kappa(\varphi_c^{(t)})$ equals the number of nonreal right zeros of $H_t$ (counted with multiplicity) plus one, is lower semicontinuous and nonincreasing on $(0, \infty)$, and changes if and only if $H_t$ has a real multiple zero, jumping by one per collided conjugate pair.

## Goal

Realize Route SC along the de Bruijn–Newman heat flow $H_t$ as a continuous source-defined homotopy of finite-index Pontryagin kernels on $\mathrm{Aff}(\mathbb{Q})$ whose negative index $\kappa(\varphi_c^{(t)})$ tracks the off-line zero count of $H_t$ with multiplicity, obeys lower semicontinuity directly from pointwise time continuity and finite-dimensional Hermitian eigenvalue persistence, descends monotonically solely through real-axis pair collisions, equals $1$ on $[1/8, \infty)$, characterizes $\mathrm{RH}$ by unit/constant index on $(0, \infty)$, and dominates Weil's $t = 0$ archimedean state $\varphi_c$ via $\kappa(\varphi_c) \le \liminf_{t \to 0^+} \kappa(\varphi_c^{(t)})$.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `negIndex_heatArchState_eq` (and full homotopy theorem suite), `lake --old env lean` green, `#print axioms` PASS (`[propext, Classical.choice, Quot.sound]`)

## Lean 4 Formalization (`formal/GaloisForLFunctions/AdelicKreinGeometry/`)

| Module | Principal Declarations |
| :--- | :--- |
| `JordanPairKernelsOnDilations.lean` | `jordanForward`, `jordanPairKernel`, `negIndex_sum_jordanPairKernel_le`, `det_expPolyJetMatrix_ne_zero`, `le_negIndex_sum_jordanPairKernel`, `negIndex_sum_jordanPairKernel_eq`, `negIndex_finset_sum_jordanPairKernel_eq`, `sum_jordanPairKernel_subBoost`, `negIndex_archGlue_finset_sum_jordanPairKernel_eq` |
| `HeatTangentBlaschkeExtraction.lean` | `heatThetaKernel`, `heatSourceEntire`, `heatSourceEntire_eq_riemannHeat`, `riemannHeat_eq_zero_and_im_neg_iff`, `heatRightZeroSet`, `heatRightZeroMultiplicity`, `two_mul_heatRightZeroMultiplicity`, `heatTangentPJ`, `heatLowerBlaschkeLogDeriv`, `heatLowerBlaschkeBoundary`, `heatUpperBlaschkeBoundary`, `heatLowerBlaschkeBoundary_eq`, `heatUpperBlaschkeBoundary_eq`, `tendsto_heatBlaschkeMeromorphic_nhds`, `tendsto_heatLowerBlaschkeBoundary_nhds`, `tendsto_heatUpperBlaschkeBoundary_nhds` |
| `HeatGaussianResidueKernel.lean` | `heatGaussianWave`, `heatContourIntegrand`, `heatForwardDilation`, `heatDilationKernel`, `isHermKernel_heatDilationKernel`, `continuousOn_heatDilationKernel`, `heatResiduePoly`, `heatResiduePoly_ne_zero`, `natDegree_heatResiduePoly_add_one`, `heatForwardDilation_eq_sum_laurentCoeff`, `heatDilationKernel_eq_sum_jordanPairKernel`, `heatDilationKernel_eq_zero_of_eighth_le` |
| `TheHeatDeformedArchimedeanState.lean` | `heatArchState`, `isHermKernel_heatArchState`, `continuousOn_heatArchState`, `negIndex_heatDilationKernel_eq`, `negIndex_heatArchState_eq`, `negIndex_heatArchState_eq_nonrealZeroCount`, `negIndex_heatArchState_lt_top`, `negIndex_heatArchState_eq_card_of_simple`, `lowerSemicontinuousAt_negIndex_heatArchState`, `lowerSemicontinuousOn_negIndex_heatArchState`, `antitoneOn_negIndex_heatArchState`, `heatCollisionPairs`, `two_mul_heatCollisionPairs`, `exists_right_negIndex_heatArchState_eq`, `exists_left_negIndex_heatArchState_eq_add_collisionPairs`, `eventually_negIndex_heatArchState_eq_iff_realMultipleZeros_eq_empty`, `negIndex_heatArchState_eq_add_interval_collisionPairs`, `negIndex_heatArchState_eq_iff_forall_realMultipleZeros_eq_empty`, `heatArchState_eq_archGlue_zero_of_eighth_le`, `negIndex_heatArchState_eq_one_of_eighth_le`, `riemannHypothesis_iff_forall_negIndex_heatArchState_eq_one`, `riemannHypothesis_iff_negIndex_heatArchState_const`, `negIndex_weilArchState_le_liminf_heatArchState`, `negIndex_weilArchState_lt_top_iff_bdd` |

## Complete Paper Proof (`[PROVED HERE]`)

### 1. Source-only construction of $\varphi_c^{(t)}$

Fix $c > 0$ and $t \in \mathbb{R}$. Let $\Phi(x) = \mathtt{riemannKernelReal}(x)$ be Riemann's positive super-exponential theta kernel, and define from source data alone:

1. **Gaussian-weighted theta kernel and entire transform:**
   $$\Phi_t(x) := \Phi(x) e^{t x^2}, \qquad H_t(z) := \int_{-\infty}^{\infty} \Phi_t(x) \cos(z x)\,dx = \mathtt{riemannHeat}(t, z).$$
2. **Tangent-disc Poisson–Jensen extraction of the lower-half-plane Blaschke logarithmic derivative:**
   On the discs $\overline{D}(-i R, R) \subset \{w \in \mathbb{C} : \operatorname{Im} w \le 0\}$ tangent to $\mathbb{R}$ at $0$ ($R > 0$), set
   $$\mathcal{P}_{t, R}(z) := \frac{1}{2\pi} \int_0^{2\pi} \frac{2(\zeta_R(\theta) + i R)}{(\zeta_R(\theta) - z)^2} \log\|H_t(\zeta_R(\theta))\|\,d\theta - \frac{H_t'(z)}{H_t(z)}, \qquad \zeta_R(\theta) = -i R + R e^{i\theta},$$
   $$\mathcal{L}_t(z) := \lim_{R \to +\infty} \mathcal{P}_{t, R}(z) \quad (\mathtt{limUnder}\ \mathtt{atTop}).$$
3. **Horizontal boundary reconstruction and Schwarz mate:**
   For $r \in \mathbb{R}$, set
   $$\mathcal{B}_t^-(r) := \exp\!\left(-\int_r^{+\infty} \mathcal{L}_t(\sigma - i)\,d\sigma\right), \qquad \mathcal{B}_t^+(r) := \bigl(\overline{\mathcal{B}_t^-(r)}\bigr)^{-1}.$$
4. **Gaussian-damped strip correlation and archimedean gluing:**
   For $v \in \mathbb{Q}_{>0}^\times$ with $y = \log v$, define
   $$F_t(v) := \frac{1}{2\pi i} \int_{-\infty}^{\infty} \Bigl(\mathcal{B}_t^-(r) e^{-(r - i)^2 - i(r - i)y} - \mathcal{B}_t^+(r) e^{-(r + i)^2 - i(r + i)y}\Bigr)\,dr,$$
   $$K_t(v) := F_t(v) + \overline{F_t(v^{-1})}, \qquad \varphi_c^{(t)}(x \mapsto a x + b) := K_t(|a|) - c |a|^{-1/2} |b| = \mathtt{archGlue}(K_t, c).$$

Every step depends exclusively on $\Phi_t$, standard complex contour/circle integration, limits, and the archimedean successor $-c|b|$; no zero set or multiplicity enters the definition.

### 2. Why naive candidates fail (and why tangent-disc Blaschke + Jordan residues succeed)

- A single-test logarithmic-derivative correlation $\sum_{H_t(z)=0} m_t(z) \widehat{\psi}(z)^2 e^{-i z y}$ produces pure exponentials without polynomial prefactors, so its negative index counts *distinct* nonreal right zeros $D(t)$ rather than multiplicity $M(t) = \sum_{\operatorname{Im} u < 0} m_t(u)$. At any hypothetical off-axis collision of multiplicity $k \ge 2$ at $t_1 > 0$, forward heat splitting (`exists_ball_simple_riemannHeat_zeros_forward`) yields $k$ distinct simple zeros on $(t_1, t_1 + \delta)$, making $D(t_1) < D(t_1 + \varepsilon)$ and violating monotonicity away from real-axis collisions.
- A Cayley quotient $(H_t + i H_t')/(H_t - i H_t')$ cancels $\gcd(H_t, H_t')$ at nonreal multiple zeros as well as real ones, again dropping multiplicity to $1$.
- By contrast, the tangent discs $\overline{D}(-i R, R)$ satisfy $\|u + i R\|^2 - R^2 = |u|^2 + 2 R \operatorname{Im} u$. Since $H_t(0) \neq 0$ (`riemannHeat_zero_ne`), *no* real zero (simple or multiple) and *no* upper-half-plane zero of $H_t$ ever enters $\overline{D}(-i R, R)$ for any $R > 0$, while every lower-half-plane zero $u$ ($\operatorname{Im} u < 0$) enters $D(-i R, R)$ for $R > |u|^2 / (-2 \operatorname{Im} u)$ with its full multiplicity $m_t(u)$.

### 3. Identification of $\mathcal{L}_t$, $\mathcal{B}_t^\pm$, and $K_t$ for $t > 0$

Fix $t > 0$. By Ki–Kim–Lee finiteness (`riemannHeat_nonreal_zeros_finite`), $Z_-(t) := \{u \in \mathbb{C} : H_t(u) = 0,\ \operatorname{Im} u < 0\}$ is finite. Under $s = 1/2 + i z$, $\operatorname{Re} s = 1/2 - \operatorname{Im} z > 1/2 \iff \operatorname{Im} z < 0$, and for every $y \in \mathbb{R}$, $\operatorname{Re} H_t(i y) = \int \Phi(x) e^{t x^2 - y x}\,dx > 0$, so $Z_-(t)$ contains no purely imaginary point and corresponds bijectively (preserving multiplicity) to the nonreal right zeros of $s \mapsto H_t(-i(s - 1/2))$. By conjugation symmetry $H_t(\bar{z}) = \overline{H_t(z)}$, $M(t) := \sum_{u \in Z_-(t)} m_t(u) = N(t)/2$ where $N(t) = \mathtt{nonrealZeroCount}(t)$.

1. **Pointwise limit $R \to +\infty$:** For any $z$ with $\operatorname{Im} z < 0$ and $H_t(z) \neq 0$, once $R > \max(\{|z|^2/(-2\operatorname{Im} z)\} \cup \{|u|^2/(-2\operatorname{Im} u) : u \in Z_-(t)\})$, both $z$ and all of $Z_-(t)$ lie in $D(-i R, R)$, and $\partial D(-i R, R)$ is zero-free for $H_t$. By differentiated Poisson–Jensen (`logDeriv_poissonJensen`),
   $$\mathcal{P}_{t, R}(z) = -\sum_{u \in Z_-(t)} m_t(u)\left(\frac{1}{z - u} + \frac{\overline{u + i R}}{R^2 - \overline{(u + i R)}(z + i R)}\right).$$
   Since $\frac{\overline{u + i R}}{R^2 - \overline{(u + i R)}(z + i R)} = \frac{-i + \bar{u}/R}{i(z - \bar{u}) - \bar{u} z / R} \to -\frac{1}{z - \bar{u}}$ as $R \to +\infty$, passing to the limit termwise in this fixed finite sum (requiring *no* growth bound on $\log\|H_t\|$) gives
   $$\mathcal{L}_t(z) = \sum_{u \in Z_-(t)} m_t(u)\left(\frac{1}{z - \bar{u}} - \frac{1}{z - u}\right) = \frac{B_t'(z)}{B_t(z)}, \qquad B_t(z) := \prod_{u \in Z_-(t)} \left(\frac{z - \bar{u}}{z - u}\right)^{m_t(u)}.$$
2. **Line integral on $\operatorname{Im} z = -1$:** By `riemannHeat_zeros_im_sq_le`, every zero of $H_t$ satisfies $|\operatorname{Im} u| \le \sqrt{\max(1/4 - 2t, 0)} < 1/2$. On $z = \sigma - i$ ($\sigma \in \mathbb{R}$), $H_t(\sigma - i) \neq 0$, and for every $u = \alpha - i\gamma \in Z_-(t)$ ($0 < \gamma < 1/2$),
   $$\operatorname{Re}\bigl((\sigma - i - \bar{u})\overline{(\sigma - i - u)}\bigr) = (\sigma - \alpha)^2 + (1 - \gamma^2) > \frac{3}{4} > 0,$$
   so $q_u(\sigma) := (\sigma - i - \bar{u})/(\sigma - i - u)$ lies strictly in the open right half-plane $\{\operatorname{Re} w > 0\} \subset \mathbb{C} \setminus (-\infty, 0]$ for all $\sigma \in \mathbb{R}$, with $q_u(\sigma) \to 1$ as $\sigma \to +\infty$ and $\frac{d}{d\sigma}\log q_u(\sigma) = \frac{1}{\sigma - i - \bar{u}} - \frac{1}{\sigma - i - u} = O(\sigma^{-2})$. By the fundamental theorem of calculus on $[r, \infty)$, $-\int_r^\infty \mathcal{L}_t(\sigma - i)\,d\sigma = \sum_{u \in Z_-(t)} m_t(u)\log q_u(r)$, so $\mathcal{B}_t^-(r) = B_t(r - i)$, and Schwarz reflection $\overline{B_t(\bar{z})} = B_t(z)^{-1}$ gives $\mathcal{B}_t^+(r) = B_t(r + i)$.
3. **Rectangle residue evaluation of $F_t(v)$:** Applying the arbitrary-order rectangle residue theorem (`rectangleIntegral'_eq_sum_laurentCoeff`) to $G_{t, y}(z) := B_t(z) e^{-z^2 - i z y}$ on $[-R, R] \times [-1, 1]$ and sending $R \to +\infty$ (the vertical edges vanish by Gaussian decay $e^{-R^2 + 1 + |y|}$ since $\|B_t(\pm R + i\tau)\| \le 3^{M(t)}$ on $|\tau| \le 1$) gives
   $$F_t(v) = \sum_{u \in Z_-(t)} \operatorname{laurentCoeff}(G_{t, y}, u, -1).$$
   At each $u \in Z_-(t)$ of order $m = m_t(u) \ge 1$, $G_u(\tau) := (u + \tau - \bar{u})^m \bigl(\prod_{w \in Z_-(t) \setminus \{u\}} (\frac{u + \tau - \bar{w}}{u + \tau - w})^{m_w}\bigr) e^{-(u + \tau)^2}$ is analytic at $\tau = 0$ with $G_u(0) \neq 0$. Expanding $G_u(\tau) e^{-i y \tau}$ to order $m - 1$ (`laurentCoeff_eq_taylorCoeffZero`) yields
   $$\operatorname{laurentCoeff}(G_{t, y}, u, -1) = P_u(y) e^{-i u y}, \qquad P_u(Y) := \sum_{r=0}^{m-1} \frac{G_u^{(m-1-r)}(0)}{(m-1-r)!} \frac{(-i)^r}{r!} Y^r,$$
   where $\deg P_u = m - 1$ since the $Y^{m-1}$ coefficient is $G_u(0)(-i)^{m-1}/(m-1)! \neq 0$. Thus
   $$K_t(v) = \sum_{u \in Z_-(t)} \Bigl(P_u(\log v) e^{-i u \log v} + \overline{P_u(-\log v)} e^{-i \bar{u} \log v}\Bigr).$$

### 4. Exact signature of polynomial-exponential Jordan pair kernels

Let $u_1, \dots, u_\kappa \in \mathbb{C}$ be distinct with $\operatorname{Im} u_i < 0$, and let $P_1, \dots, P_\kappa \in \mathbb{C}[X]$ be nonzero of degrees $d_i$, with $M = \sum_{i=1}^\kappa (d_i + 1)$. For $K(v) = \sum_{i=1}^\kappa \bigl(P_i(\log v)e^{-i u_i \log v} + \overline{P_i(-\log v)}e^{-i\bar{u}_i \log v}\bigr)$:

- **Upper bound ($\kappa(K) \le M$):** On any finite family $x : \mathrm{Fin}\,n \to \mathbb{Q}_{>0}^\times$, expanding $(y_b - y_a)^r = \sum_{j=0}^r \binom{r}{j}(-y_a)^{r-j} y_b^j$ ($y_a = \log x_a$) expresses the Gram quadratic form of $K$ as
  $$2 \operatorname{Re} \sum_{i=1}^\kappa \sum_{0 \le j + l \le d_i} p_{i, j+l} (-1)^l \binom{j+l}{j} \overline{L_{\bar{u}_i, l}(c)}\, L_{u_i, j}(c), \qquad L_{w, j}(c) := \sum_b c_b y_b^j e^{-i w y_b}.$$
  On the common kernel of the $M$ linear functionals $\{L_{u_i, j} : 1 \le i \le \kappa,\ 0 \le j \le d_i\}$, the quadratic form is identically $0$. By `negIndex_le_card_of_nonneg_on_ker`, $\kappa(K) \le M$.
- **Lower bound ($M \le \kappa(K)$):** The $2\kappa$ frequencies $\{u_1, \dots, u_\kappa, \bar{u}_1, \dots, \bar{u}_\kappa\}$ are pairwise distinct since $\operatorname{Im} u_i < 0 < \operatorname{Im} \bar{u}_j$. Choose $u_0 = \frac{n+2}{n+1} \in \mathbb{Q}_{>0}^\times$ with $s_0 = \log u_0 > 0$ small enough that $s_0 |w - w'| < 2\pi$ for all distinct pairs, so the $2\kappa$ nonzero nodes $\lambda_w = e^{-i w s_0}$ are pairwise distinct. On the cyclic family $x_k = u_0^k$ ($0 \le k < 2M$), the $2M \times 2M$ matrix $W$ of functionals $(k s_0)^j \lambda_w^k$ ($0 \le j \le d_w$) satisfies $W^\top = \Gamma^\top D^A$ where $\Gamma$ is block-lower-triangular invertible by Stirling inversion (`triangular_matrix_isUnit_det`) and $D^A$ is the transposed confluent polynomial jet matrix with $\det D \neq 0$ (`det_confluentPolynomialJetMatrix`). Hence $\det W \neq 0$. Prescribing $L_{u_i, j}(c) = (N+1)^j v_{i, j}$ and $L_{\bar{u}_i, l}(c) = -(N+1)^{l - d_i} \frac{\overline{h_{i, l}}}{\|h_{i, l}\|} v_{i, d_i - l}$ where $h_{i, l} = p_{i, d_i}(-1)^l \binom{d_i}{d_i - l} \neq 0$, the compressed $M \times M$ Gram matrix converges entrywise as $N \to \infty$ to $\operatorname{diag}(-2\|h_{i, d_i - j}\|)$. By `eventually_le_hermNegIndex`, $M \le \kappa(K)$.

### 5. Archimedean gluing, continuity, monotonicity, and collision jump law

1. **Gluing (`negIndex_heatArchState_eq`):** Every $u \in Z_-(t)$ satisfies $|\operatorname{Im} u| < 1/2$, so along $2^N v$ each term $(N \log 2 + \log v)^j e^{-i w (N \log 2 + \log v)} 2^{-N/2}$ has norm $O(N^j e^{-N \log 2 (1/2 \pm \operatorname{Im} u)}) \to 0$. By `negIndex_archGlue_eq_of_subBoost`, $\kappa(\varphi_c^{(t)}) = \kappa(K_t) + 1 = M(t) + 1 = N(t)/2 + 1 < \infty$.
2. **Continuity and lower semicontinuity:** Fix $t_1 > 0$. By uniform large-height reality (`exists_riemannHeat_zeros_real_uniform`) and Hurwitz disc-count stability (`eventually_zeroSumBall_riemannHeat_eq`), as $s \to t_1$ every zero of $H_s$ with $\operatorname{Im} w < 0$ clusters in arbitrarily small discs around zeros $e$ of $H_{t_1}$ with $\operatorname{Im} e \le 0$ (where $(r - i - \bar{e})/(r - i - e) = 1$ for real $e$, and total multiplicity in $B(e, \varepsilon)$ equals $m_{t_1}(e)$ for $\operatorname{Im} e < 0$). Hence $\mathcal{B}_s^-(r) \to \mathcal{B}_{t_1}^-(r)$ and $\mathcal{B}_s^+(r) \to \mathcal{B}_{t_1}^+(r)$ for every $r \in \mathbb{R}$, with uniform bound $\|\mathcal{B}_s^\pm(r)\| \le 3^{N(s)/2}$ ($N(s)$ locally bounded near $t_1$). Dominated convergence against $e^{-r^2 + 1 + |\log v|}$ gives continuity of $t \mapsto \varphi_c^{(t)}(g)$ on $(0, \infty)$ for every $g \in \mathrm{Aff}(\mathbb{Q})$. Lower semicontinuity of $t \mapsto \kappa(\varphi_c^{(t)})$ on $(0, \infty)$ follows directly from `eventually_le_hermNegIndex`.
3. **Monotonicity and collision jumps:** Since $N(t) = 2 M(t)$ is nonincreasing on $(0, \infty)$ (`nonrealZeroCount_antitoneOn`), $\kappa(\varphi_c^{(t)}) = N(t)/2 + 1$ is `AntitoneOn` $(0, \infty)$. By `exists_right_nonrealZeroCount`, `exists_left_nonrealZeroCount`, and `nonrealZeroCount_eq_zero_of_le`, $\kappa(\varphi_c^{(t)})$ is right-constant at every $t > 0$, satisfies $\kappa(\varphi_c^{(s)}) = \kappa(\varphi_c^{(t)}) + \sum_{x \in \mathrm{realMultipleZeros}(t)} \lfloor m_t(x)/2 \rfloor$ for $s \in (t - \delta, t)$, and equals $1$ for $t \ge 1/8$. Hence on any $0 < t_1 \le t_2$, $\kappa(\varphi_c^{(t_1)}) = \kappa(\varphi_c^{(t_2)}) + \sum_{s \in (t_1, t_2]} \mathtt{heatCollisionPairs}(s)$, $\kappa(\varphi_c^{(t)})$ changes iff $H_t$ has a real multiple zero, $\mathrm{RH} \iff \forall t > 0,\ \kappa(\varphi_c^{(t)}) = 1 \iff \forall s, t > 0,\ \kappa(\varphi_c^{(s)}) = \kappa(\varphi_c^{(t)})$, $\kappa(\varphi_c) \le \liminf_{t \to 0^+} \kappa(\varphi_c^{(t)})$, and $\kappa(\varphi_c) < \infty \iff \exists M \in \mathbb{N},\ \forall t > 0,\ \kappa(\varphi_c^{(t)}) \le M$.

## Log
- 2026-10-31 — completed dependency-closed paper proof and full unconditional Lean 4 formalization across 4 modules in `formal/GaloisForLFunctions/AdelicKreinGeometry/`; all modules compile green under `lake --old env lean` and pass `#print axioms` (`[propext, Classical.choice, Quot.sound]`).
