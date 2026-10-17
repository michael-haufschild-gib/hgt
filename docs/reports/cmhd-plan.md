# PHASE 1

our Lean corpus, the terminal receiver for the CHMD causal-wave route is already 100% formalized and unconditional in [CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean) and [CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean).

Here is the exact architecture of what is already wired in Lean, what we just proved, why one apparent continuation is a dead end, and what the genuine remaining bridge to `RiemannHypothesis` is.

---

### 1. The Terminal Receiver Already in the Corpus

In [CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean#L18-L48) and [CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L32-L61), the entire infinite Toeplitz hierarchy has already been collapsed to a **single one-sided bound** on either the causal wave $\varphi_\Lambda = \operatorname{chmdWave}$ or the prime wave $\operatorname{chmdPrimeWave}$:

1. **Exact Three-Part Decomposition** ([`chmdWave_eq_pole_add_arch_sub_prime`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L120-L125)):
   $$\varphi_\Lambda(y) = \operatorname{chmdPoleWave}(y) + \frac{1}{2\pi}\operatorname{chmdArchWave}(y) - \operatorname{chmdPrimeWave}(y),$$
   where $\operatorname{chmdPoleWave}(y) + \frac{1}{2\pi}\operatorname{chmdArchWave}(y)$ is **uniformly bounded on all of $\mathbb{R}$** ([`abs_chmdPoleWave_add_archWave_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L18-L22)).
2. **One-Sided Prime-Wave Collapse** ([`riemannHypothesis_iff_chmdPrimeWave_bddBelow`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L40-L44), [`chmdPrimeWave_growth_law`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L36-L39)):
   $$\text{`RiemannHypothesis`} \iff \exists M \in \mathbb{R},\; \forall y \ge 0,\; \operatorname{chmdPrimeWave}(y) \ge -M$$
   $$\iff \forall a \in (0, 1/2),\; \exists M_a,\; \forall y \ge 0,\; \operatorname{chmdPrimeWave}(y) \ge -M_a e^{a y}.$$
   Equivalently, on the causal wave itself ([`riemannHypothesis_iff_forall_chmdWave_le_zero_value`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean#L37-L44)):
   $$\text{`RiemannHypothesis`} \iff \forall y \in \mathbb{R},\; \varphi_\Lambda(y) \le \varphi_\Lambda(0) \iff \exists M \in \mathbb{R},\; \forall y \ge 0,\; \varphi_\Lambda(y) \le M.$$

In other words, **to prove `RiemannHypothesis` in Lean, we do not need to prove Bochner positivity on all $N$-point Toeplitz packets at all scales**: Landau's theorem on the Klein–Gordon pole series ([`abs_im_kgFreq_le_of_chmdWave_le_exp`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean#L30-L35)) already proves that if $\operatorname{chmdPrimeWave}(y)$ is bounded below (or even grows slower than $e^{a y}$ for every $a > 0$), then $|\operatorname{Im}\rho_\rho| = 0$ for every zero $\rho$, which is `RiemannHypothesis`.

---

### 2. Why the Small-Scale Moment / Taylor Track Cannot Close the Global Gap Alone

In [CHMDQuarticMomentAndSecondOrderPacketPositivity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDQuarticMomentAndSecondOrderPacketPositivity.lean), we proved:
- $M_2, M_3, M_4 > 0$ unconditionally across the entire strip $|\operatorname{Im} z| < 1/2$ via the universal strip-sector law $7 V^2 < U^2$ ([`seven_mul_im_sq_lt_re_sq`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDQuarticMomentAndSecondOrderPacketPositivity.lean#L86-L100)),
- Utilizing the verified height bound $\operatorname{Re}(\gamma_\rho)^2 \ge 431/2$ from [PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance.lean), the off-line sector ratio at actual zeros improves from $7 V^2 < U^2$ to $219 V^2 < U^2$, which pushes positivity of $M_k$ up to $k \approx 33$.

**However, pushing $M_k > 0$ to higher $k$ is not how RH will be closed:**
- Every Taylor expansion of $\varphi_\Lambda(\lambda(t_j - t_i))$ around $\lambda = 0$ produces a positivity radius $\lambda_0(t, c) > 0$ that **shrinks with the packet and moment order** (because the high-frequency tail $Q_{2k+2} = \sum_\rho m_\rho \|w_\rho\| \|\rho_\rho\|^{2k+2}$ grows factorially like $(2k+2)!$).
- Conversely, an off-line zero $\rho$ with $\beta_\rho = \operatorname{Im}\rho_\rho \ne 0$ has positive first few moments $\operatorname{Re}(\rho_\rho^{2k} w_\rho) > 0$, so small-scale positivity at $y \to 0$ is **consistent** with an off-line zero; an off-line zero only betrays itself at **large hyperbolic time $y \to \infty$** where $\cosh(y \beta_\rho) \sim \frac{1}{2} e^{|y \beta_\rho|}$ blows up!

This is the single most important lesson from the corpus: **small-scale ($y \to 0$) positivity is unconditional because of the Klein–Gordon mass shift $+2$; the RH obstruction lives exclusively in the large-time ($y \to \infty$) behavior of `chmdPrimeWave`**.

---

### 3. The True Bridge from Here to `RiemannHypothesis`: De-Inverting the Positive Volterra Light-Cone Equation at Large $y$

Look at the two dual light-cone equations we now have in Lean between the **unknown-sign Klein–Gordon prime wave** $P(y) := \operatorname{chmdPrimeWave}(y)$ and the **strictly positive massless d'Alembert prime wave** $P_0(y) := \operatorname{masslessPrimeWave}(y) = \sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt{n}}\bigl(D(\log n + y) + D(\log n - y)\bigr) > 0$:

1. **Forward Light-Cone Equation** ([`chmdPrimeWave_eq_lightConeTransmute`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDLightConePrimeKernelDecomposition.lean#L343-L392)):
   $$P(y) = L[P_0](y) = P_0(y) - \frac{y^2}{2}\int_{-1}^1 B\bigl(2 y^2 (1 - t^2)\bigr) P_0(y t)\,dt.$$
2. **Inverse Light-Cone Equation** ([`inverseLightConeTransmute_chmdPrimeWave`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDQuarticMomentAndSecondOrderPacketPositivity.lean#L1125-L1178)):
   $$P_0(y) = L^{-1}[P](y) = P(y) + \frac{y^2}{2}\int_{-1}^1 \underbrace{B\bigl(-2 y^2 (1 - t^2)\bigr)}_{\ge 1 > 0} P(y t)\,dt > 0.$$

Why is this pair of equations the heart of the CHMD route?
- In (2), the Volterra operator $L^{-1} = I + K_+$ has a **strictly positive kernel** $B(-2y^2(1-t^2)) = \frac{I_1(\sqrt{2y^2(1-t^2)})}{\frac{1}{2}\sqrt{2y^2(1-t^2)}} \ge 1$, and maps $P = \operatorname{chmdPrimeWave}$ to $P_0 > 0$.
- In (1), its exact inverse $L = (I + K_+)^{-1} = I - K_-$ expresses $P(y)$ purely in terms of the known positive function $P_0(s) = \sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt{n}}(D(\log n + s) + D(\log n - s))$ on $[-y, y]$ integrated against the **oscillatory Bessel kernel** $B(2y^2(1-t^2)) = \frac{J_1(\sqrt{2y^2(1-t^2)})}{\frac{1}{2}\sqrt{2y^2(1-t^2)}}$.
- Notice that $P_0(s)$ is **completely explicit and positive**: each prime power $n$ contributes a smooth positive bump $D(s - \log n) = \frac{2(s - \log n)}{\sinh(\pi(s - \log n))}$ centered at $s = \log n$ of width $O(1)$ and height $\frac{2}{\pi}\frac{\Lambda(n)}{\sqrt{n}}$.
- Using only the triangle inequality $|B(2y^2(1-t^2))| \le 1$ on the real axis gives $|P(y)| \le P_0(y) + y \int_0^y P_0(s)\,ds$. Because $\int_0^y P_0(s)\,ds \sim \sum_{\log n \le y} \frac{\Lambda(n)}{\sqrt{n}} \sim 2 e^{y/2}$ (by PNT / Chebyshev), the crude bound gives $O(y e^{y/2})$ (matching the unconditional $O(e^{y/2})$ bound in [`abs_chmdPrimeWave_le_exp_half`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L23-L26)).
- **Why does the $e^{y/2}$ growth cancel in truth?**
  Because in $P_0(s)$, the prime-counting density $\sum_{\log n \le s} \frac{\Lambda(n)}{\sqrt{n}}$ has smooth main term $e^{s/2}$, and for the smooth exponential $A(s) = \cosh(s/2)$, our theorem [`cos_mul_sqrt_seven_fourths_eq_lightCone`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDLightConePrimeKernelDecomposition.lean#L398-L421) ALREADY PROVED the exact identity:
  $$L\bigl[\cosh(\cdot / 2)\bigr](y) = \cos\bigl(y \sqrt{7/4}\bigr),$$
  which is **bounded by $1$ on all of $\mathbb{R}$**!
  Look at what [`cos_mul_sqrt_seven_fourths_eq_lightCone`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDLightConePrimeKernelDecomposition.lean#L398-L421) is saying:
  > **The light-cone operator $L$ annihilates the $e^{y/2}$ exponential growth of $\cosh(y/2)$ and turns it into the purely oscillatory bounded wave $\cos(y\sqrt{7/4})$!**

---

### 4. Concrete Step-by-Step Roadmap to the Final Proof

That identity — $L[\cosh(\cdot/2)](y) = \cos(y\sqrt{7/4})$ — is what all the CHMD light-cone files in our corpus are pointing at:

1. **Step 1 — Subtract the Pole Counterterm Inside the Light Cone (`L[P_0 - Pole_0]`)**:
   Combine [`chmdPoleWave_eq_lightConeTransmute`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDLightConePrimeKernelDecomposition.lean#L424-L433) and [`chmdPrimeWave_eq_lightConeTransmute`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDLightConePrimeKernelDecomposition.lean#L343-L392):
   $$\operatorname{chmdPoleWave}(y) - \operatorname{chmdPrimeWave}(y) = L\Bigl[\frac{2}{\cos^2(1/4)}\cosh(\cdot/2) - P_0\Bigr](y).$$
   In the massless world (before applying $L$), both $\frac{2}{\cos^2(1/4)}\cosh(v/2)$ and $P_0(v)$ grow like $e^{|v|/2}$ because the pole of $\zeta(s)$ at $s=1$ ($z = \pm i/2$) has the same exponent $1/2$ as the Chebyshev prime sum $\sum_{n \le e^v} \frac{\Lambda(n)}{\sqrt{n}}$.
2. **Step 2 — Integration by Parts on the Light-Cone Bessel Kernel**:
   The Bessel kernel $B(2(y^2 - s^2))$ satisfies $\frac{d}{ds}\bigl[J_0(\sqrt{2(y^2 - s^2)})\bigr] = \frac{s}{2} B(2(y^2 - s^2))$.
   Integrating $L[P_0](y)$ by parts in $s = y t$ replaces the raw prime-sum $P_0(s)$ times the order-1 Bessel kernel $B$ by the **integrated prime discrepancy**
   $$\Delta_0(v) := \int_0^v \Bigl(P_0(s) - \frac{2}{\cos^2(1/4)}\cosh(s/2)\Bigr)\,ds$$
   against the bounded order-0 Bessel kernel $J_0(\sqrt{2(y^2 - s^2)})$.
3. **Step 3 — Exponential Lower-Order Bound on $L[P_0](y)$ $\implies$ `RiemannHypothesis`**:
   By [`chmdPrimeWave_growth_law`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L36-L39), any reduction of the growth exponent of $\operatorname{chmdPrimeWave}(y) = L[P_0](y)$ from $1/2$ to $a < 1/2$ forces $|\operatorname{Im}\rho_\rho| \le a$ for all zeros $\rho$, and bounding $\operatorname{chmdPrimeWave}(y)$ below on $[0, \infty)$ triggers [`riemannHypothesis_iff_chmdPrimeWave_bddBelow`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L40-L44) to conclude `RiemannHypothesis`.

### done: formal/GaloisForLFunctions/RHTower/CHMDLightConeBesselZeroAndIntegrationByParts.lean

**Light-Cone Pole-Prime Cancellation & $J_0$ Integration-by-Parts Identity**:
- Formalize the linearity identity $\operatorname{chmdWave}(y) = L\bigl[\frac{2}{\cos^2(1/4)}\cosh(\cdot/2) + \frac{1}{2\pi}\operatorname{masslessArchWave} - P_0\bigr](y)$,
- Formalize the exact Bessel derivative law $\frac{d}{dt}\bigl[\operatorname{lightConeBesselZero}(c y^2(1-t^2))\bigr] = \frac{c y^2 t}{2}\operatorname{lightConeBesselReal}(c y^2(1-t^2))$ (where $\operatorname{lightConeBesselZero}(w) = \sum_k \frac{(-w/4)^k}{(k!)^2} = J_0(\sqrt{w})$), and
- Integrate `lightConeTransmute` by parts to express $\operatorname{chmdPrimeWave}(y)$ in terms of the cumulative d'Alembert prime wave $\int_0^{yt} P_0(s)\,ds$ and the bounded kernel $J_0$.

### done: formal/GaloisForLFunctions/RHTower/CHMDPoleDensityLawAndChebyshevDiscrepancyTransport.lean

**Pole-Density Law & Chebyshev-Discrepancy Transport (Steps 1–2 made exact at the level of the arithmetic discrepancy measure)**:
- The pole constant $\int_{\mathbb R} D(u)\,e^{u/2}\,du = \sec^2(1/4)$ (`integral_dAlembertReal_mul_exp_half`), via $1/\sinh(\pi u) = 2\sum_k e^{-(2k+1)\pi u}$, $\int_0^\infty u e^{-bu}du = b^{-2}$ and the cosecant-square partial fractions at $x_0 = \tfrac12 + \tfrac{1}{4\pi}$ (`pi_sq_div_sin_sq_eq_tsum`).
- The massless pole law $\int (D(s+v) + D(s-v))e^{s/2}ds = \frac{2}{\cos^2(1/4)}\cosh(v/2)$ and the **Klein–Gordon pole law** $\int_{\mathbb R} K_y(s)\,e^{s/2}\,ds = \operatorname{chmdPoleWave}(y)$ (`integral_chmdPrimeKernel_mul_exp_half`), spatial form $\int K_y(s-u)e^{s/2}ds = e^{u/2}\operatorname{chmdPoleWave}(y)$: the ζ-pole is the $e^{u/2}$ spatial mode of the prime field, oscillating in time at $\sqrt{7/4}$.
- **Transport law** (`chmdPrimeWave_eq_chmdPoleWave_add_transport`): $\operatorname{chmdPrimeWave}(y) = \operatorname{chmdPoleWave}(y) + T(y) - S(y)$ with $T(y) = \sum_n \frac{\Lambda(n)}{\sqrt n}K_y(\log n) - \int_0^\infty K_y(s)e^{s/2}ds$ the KG transport of the exact discrepancy measure $\sum_n \frac{\Lambda(n)}{\sqrt n}\delta_{\log n} - e^{s/2}ds$, and $|S(y)| \le 8/\pi$. Hence `RiemannHypothesis ↔ T bounded below on [0,∞) ↔ T bounded above` (`riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow/bddAbove`).
- Consequence for Step 3: after the exact transport no object of exact growth $e^{y/2}$ remains; the one-sided bound is a statement about the arithmetic discrepancy measure against the bounded kernel $|K_y| \le 4/\pi$, i.e. Wall 1 (one-sided $\sqrt x$ prime counting) in Klein–Gordon coordinates, with the pole density removed exactly rather than asymptotically.


### done: formal/GaloisForLFunctions/RHTower/CHMDChebyshevDiscrepancyDerivativeTransportLaw.lean

**Function form of the transport law (Step 2 completed with the exact Chebyshev discrepancy function against the derivative kernel)**:
- The real derivative $D'$ of the d'Alembert kernel is continuous with $|D'(v)| \le C(1+|v|)e^{-\pi|v|}$; the space derivative of the prime kernel is $\partial_s K_y(s) = D'(s+y) + D'(s-y) - \tfrac{y^2}{2}\int_{-1}^1 B(2y^2(1-t^2))\,(D'(s+yt) + D'(s-yt))\,dt$ (`hasDerivAt_chmdPrimeKernel_right`), and both $K_y$, $\partial_sK_y$ decay like $e^{-(\pi-1)|s|}$.
- Stieltjes integration by parts over the prime powers (`tsum_chmdPrimeWeight_mul_kernel_eq`): $\sum_n \frac{\Lambda(n)}{\sqrt n}K_y(\log n) = -\int_0^\infty \partial_sK_y(s)\,\Psi(s)\,ds$ with $\Psi(s) = \sum_{\log n < s}\Lambda(n)/\sqrt n$ (Chebyshev bound $\Psi(s) \le (2\log 4 + 16)e^{s/2}$ from Zeta23).
- **Function form** (`chmdPrimeWave_eq_pole_add_derivative_transport`): $\operatorname{chmdPrimeWave}(y) = \operatorname{chmdPoleWave}(y) + 2K_y(0) - S(y) - \int_0^\infty \partial_sK_y(s)\,\Delta(s)\,ds$, $\Delta(s) = \Psi(s) - 2e^{s/2}$, $|2K_y(0) - S(y)| \le 16/\pi$. Hence `RiemannHypothesis ↔ ∫_0^∞ ∂_sK_y Δ bounded above on [0,∞) ↔ bounded below` (`riemannHypothesis_iff_integral_kernelDeriv_mul_discrepancy_bddAbove/bddBelow`).
- Step 3 now reads: a one-sided bound, uniform in $y \ge 0$, on the pairing of the classical $\sqrt{\cdot}$-weighted Chebyshev discrepancy $\Delta$ with the exponentially localized odd kernel $\partial_sK_y$.


### done: formal/GaloisForLFunctions/RHTower/CHMDPrimeKernelDerivativeUniformBound.lean

**Uniform bound on the derivative kernel (the Step-3 pairing is against a kernel bounded in both variables)**:
- Fourier form (`kernelDeriv_eq_kernelDerivFourier`): $\partial_sK_y(s) = -\frac1\pi\int\cos(y\sqrt{r^2+2})\,\mathrm{sech}^2(r/2)\,r\sin(rs)\,dr$; odd in $s$.
- Exact first moment (`integral_abs_mul_sechSqHalf`): $\int|r|\,\mathrm{sech}^2(r/2)\,dr = 8\log 2$.
- **Uniform bound** (`abs_kernelDeriv_le`): $|\partial_sK_y(s)| \le 8\log 2/\pi$ for all $y, s$, removing the $e^{\pi|y|}e^{y^2/2}$ factor of the light-cone estimates; uniform Lipschitz bound for $K_y$ (`abs_chmdPrimeKernel_sub_le`).
- Window estimate (`abs_setIntegral_kernelDeriv_mul_discrepancy_le`): $\bigl|\int_{(0,L]}\partial_sK_y\,\Delta\bigr| \le \frac{8\log 2}{\pi}\int_{(0,L]}|\Delta|$ uniformly in $y$.
- What it does not give: under RH, $\Delta(s) = O(s^2)$ only, so $\int_0^L|\Delta|$ grows with $L$; the uniform bound controls each finite window, while the one-sided bound of Step 3 still needs cancellation in the pairing as $y\to\infty$.


Note: Even under RH, Δ(s) only satisfies Δ(s) = O(s²), so the window bound grows with L. The one-sided bound on ∫₀^∞ ∂_sK_y Δ, uniform in y, still needs cancellation in the pairing as y grows. That is Wall 1, now posed against a kernel bounded in both variables.



# PHASE 2
### 1. Why We Are Stuck: The Exact Mathematical Diagnosis

In the three modules just completed — [CHMDPoleDensityLawAndChebyshevDiscrepancyTransport.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPoleDensityLawAndChebyshevDiscrepancyTransport.lean), [CHMDChebyshevDiscrepancyDerivativeTransportLaw.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDChebyshevDiscrepancyDerivativeTransportLaw.lean), and [CHMDPrimeKernelDerivativeUniformBound.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeKernelDerivativeUniformBound.lean) — the causal Klein–Gordon wave was reduced to the exact transport identity ([`chmdPrimeWave_eq_pole_add_derivative_transport`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDChebyshevDiscrepancyDerivativeTransportLaw.lean#L688-L702)):
$$\operatorname{chmdPrimeWave}(y) = \operatorname{chmdPoleWave}(y) + 2K_y(0) - S(y) - \int_0^\infty \partial_s K_y(s)\,\Delta(s)\,ds, \qquad \Delta(s) = \Psi(s) - 2e^{s/2},$$
with $|2K_y(0) - S(y)| \le 16/\pi$ and $|\partial_s K_y(s)| \le \frac{8\log 2}{\pi}$ uniformly in $(y,s)$ ([`abs_kernelDeriv_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeKernelDerivativeUniformBound.lean#L244-L250)).

Why does the route stall right here? There are **two structural obstructions** — one analytic and one arithmetic — that explain why **no further bound on the kernel $K_y$ or $\partial_s K_y$ alone** can ever close Step 3:

#### Obstruction A: $K_y(s)$ is a faithful mode propagator with a non-oscillatory wave front
By [`chmdPrimeKernel_eq_lightCone`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPoleDensityLawAndChebyshevDiscrepancyTransport.lean#L685-L703), the prime–pole transport is the light-cone transmutation $L[T_0](y)$ of the **massless discrepancy transport**
$$T_0(v) = \sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\bigl(D(\log n+v)+D(\log n-v)\bigr) - \int_{\mathbb{R}}\bigl(D(s+v)+D(s-v)\bigr)e^{s/2}\,ds = -\int_0^\infty \bigl(D'(s+v)+D'(s-v)\bigr)\Delta(s)\,ds + O(e^{-v/2}).$$
1. **No oscillation at the wave front $s = y$:** For $v > 0$, $D(s-v) = \frac{2(s-v)}{\sinh(\pi(s-v))}$ is a **strictly positive** bump of fixed width $O(1)$ and mass $1/\pi$ centered at $s = v$. Thus $T_0(v)$ simply reads off the local average of the discrepancy measure $d\Delta(s)$ in a unit window around $s = v$.
2. **No oscillation inside the light cone that kills off-line modes:** In Fourier space,
   $$\int_{\mathbb{R}} K_y(s)\,e^{i\gamma s}\,ds = \cos\bigl(y\sqrt{\gamma^2+2}\bigr)\operatorname{sech}^2(\gamma/2).$$
   If $\Delta(s)$ contains an explicit-formula mode $e^{i\gamma_\rho s}$ from a zero $\rho = \tfrac12 + i\gamma_\rho$, the pairing $-\int_0^\infty \partial_s K_y(s)\,\Delta(s)\,ds$ transports it directly to $\cos\bigl(y\sqrt{\gamma_\rho^2+2}\bigr)\operatorname{sech}^2(\gamma_\rho/2)$, which grows exponentially in $y$ whenever $\operatorname{Im}\gamma_\rho \ne 0$.
3. **Why integrating by parts in $s$ again does not help:** Even under RH, $\Delta(s) = O(s^2)$ and $\Omega_\pm(1)$, while its primitives in $s$ still oscillate with $O(1)$ amplitude over the light cone $[0,y]$ of length $y$. Meanwhile, $\int_0^y |\partial_s^k K_y(s)|\,ds$ grows at least linearly with the light-cone length $y$ (because the Bessel profile $J_1(\sqrt{2y^2(1-t^2)})/\sqrt{1-t^2}$ has $L^1$-norm $\asymp y$ on $t \in [-1,1]$).

#### Obstruction B (The Countermodel Barrier): The chain so far is arithmetic-blind beyond Chebyshev's bound
Look at what properties of $\Lambda(n)$ were actually used in `MUST-1566`–`MUST-1568`:
1. $\Lambda(n) \ge 0$, and
2. Chebyshev's elementary upper bound $\Psi(s) \le (2\log 4 + 16)e^{s/2}$ ([`chebyshevStep_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDChebyshevDiscrepancyDerivativeTransportLaw.lean#L533-L547)).

Nothing else about the primes was used! Now suppose $\widetilde{\Lambda}(n) \ge 0$ is **any fake non-negative weight system** (such as a Beurling prime system or the two-shift / Diamond–Montgomery–Vorhauer countermodels recorded in [STATUS.md](file:///Users/michael/Documents/code/hgt/docs/reports/STATUS.md#L11-L26)) that has PNT density $\widetilde{\Psi}(s) \sim 2e^{s/2}$, satisfies $\widetilde{\Psi}(s) \le C e^{s/2}$, and has an **off-line zero** $\rho_0 = \tfrac12 + \delta + i\gamma_0$ ($\delta > 0$).
- Every single theorem in `MUST-1566`, `MUST-1567`, and `MUST-1568` holds verbatim for $\widetilde{\Lambda}$ and $\widetilde{\Delta}(s) = \widetilde{\Psi}(s) - 2e^{s/2}$ against the **exact same kernel** $\partial_s K_y(s)$.
- Yet for $\widetilde{\Lambda}$, the integral $\int_0^\infty \partial_s K_y(s)\,\widetilde{\Delta}(s)\,ds$ blows up like $e^{\delta y}$!

**Conclusion:** To bound $\int_0^\infty \partial_s K_y(s)\,\Delta(s)\,ds$, we **must** eliminate $\Delta(s)$ (or constrain it) using the **defining arithmetic equation of $\Lambda(n)$** that separates the true von Mangoldt function from fake non-negative weights:
$$\sum_{d \mid n} \Lambda(d) = \log n \qquad (\Lambda * 1 = \log \iff \Lambda = \mu * \log).$$

---

### 2. How to Resolve It: The New Path in Our Lean Corpus

We do **not** need to invent the arithmetic elimination of $\Lambda$ from scratch — our Lean corpus has already built three exact, unconditional arithmetic mechanisms that inject $\Lambda * 1 = \log$ (and the Euler product/Dirichlet series identity $-\zeta'/\zeta = \Lambda$). The missing link is **welding the CHMD Klein–Gordon transport law to these arithmetic conservation laws**.

Here are the three concrete ways to resolve the obstruction, ranked by how directly they plug into `MUST-1566`–`MUST-1568`:

---

#### Path 1 (Direct Multiplicative-Delay Conservation & Möbius Reconstruction of the CHMD Discrepancy)
Look at what the corpus already proved for the unweighted logarithmic Chebyshev deficit primitive in:
- [CCMPrimeDeficitDilationConservation.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitDilationConservation.lean) ([`ccmLogChebyshevDeficitPrimitive_dilation_conservation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitDilationConservation.lean#L73-L90))
- [CCMPrimeDeficitDilationUniformBound.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitDilationUniformBound.lean) ([`abs_ccmPrimeDeficitDilationRemainder_le_uniform`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitDilationUniformBound.lean#L142-L144))
- [CCMPrimeDeficitDilationInversion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitDilationInversion.lean) ([`ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitDilationInversion.lean#L20-L31))
- [CCMPrimeDeficitMobiusCenteredEnergy.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitMobiusCenteredEnergy.lean) ([`ccmPrimeDeficitMobiusCenteredDiagonal_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitMobiusCenteredEnergy.lean#L64-L92))
- [CCMPrimeDeficitMobiusTailLocalization.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitMobiusTailLocalization.lean) ([`abs_ccmLogChebyshevDeficitPrimitive_sub_moebius_tail_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitMobiusTailLocalization.lean#L123-L131))

**How this resolves the CHMD obstruction:**
1. **Bridge $\Delta(s) = \Psi(s) - 2e^{s/2}$ to `ccmLogChebyshevDeficitPrimitive`:**
   By Abel summation / integration by parts (already formalized in [`unitRieszChebyshevRayIntegral_eq_deficitPrimitive`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPoleCompressionRHCriterion.lean#L58-L62)), the $\sqrt{\cdot}$-weighted discrepancy $\Delta(s) = \sum_{\log n < s}\frac{\Lambda(n)}{\sqrt{n}} - 2e^{s/2}$ is expressed directly in terms of the ordinary Chebyshev deficit $e^t - \psi(e^t)$ and its primitive `ccmLogChebyshevDeficitPrimitive`.
2. **Apply the Multiplicative-Delay Conservation Law $\sum_{d \mid k} \Lambda(d) = \log k$ Directly to the CHMD Transport $T(y)$:**
   In [CHMDPoleDensityLawAndChebyshevDiscrepancyTransport.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPoleDensityLawAndChebyshevDiscrepancyTransport.lean#L923), the transport is
   $$T(y) = \sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}} K_y(\log n) - \int_0^\infty K_y(s) e^{s/2}\,ds = -\int_0^\infty \partial_s K_y(s)\,\Delta(s)\,ds + 2K_y(0).$$
   If we form the **multiplicative-delay sum** of the prime kernel along the divisor lattice $m \ge 1$,
   $$\sum_{m=1}^\infty \frac{1}{\sqrt{m}} \sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}} K_y(\log n + \log m) = \sum_{k=2}^\infty \frac{\log k}{\sqrt{k}} K_y(\log k),$$
   the unknown prime weights $\Lambda(n)$ **disappear completely** via $\sum_{d \mid k} \Lambda(d) = \log k$ ([`ArithmeticFunction.vonMangoldt_sum`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitDilationConservation.lean#L64))!
3. **Why $\sum_{k=1}^\infty \frac{\log k}{\sqrt{k}} K_y(\log k)$ cancels the pole wave to $O(1)$ unconditionally:**
   Unlike $\sum_n \frac{\Lambda(n)}{\sqrt{n}} K_y(\log n)$, the elementary logarithmic sum $\sum_{k=1}^\infty \frac{\log k}{\sqrt{k}} K_y(\log k)$ has the **exact Euler–Maclaurin / sawtooth decomposition** with leading density $\int_0^\infty s e^{s/2} K_y(s)\,ds + \gamma \int_0^\infty e^{s/2} K_y(s)\,ds$, and its centered remainder is **uniformly bounded** by integration by parts against the bounded derivative $|\partial_s K_y(s)| \le \frac{8\log 2}{\pi}$ from `MUST-1568`!
4. **Invert via Möbius (`moebiusCoeff`):**
   Just as [`ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitDilationInversion.lean#L20-L31) reconstructs the Chebyshev primitive from the bounded elementary dilation source `ccmPrimeDeficitDilationSource`, Möbius inversion in the shift variable reconstructs the CHMD transport $T(y)$ (or its light-cone pre-image $T_0(v)$) as a **folded Möbius–kernel pairing** where the $e^{s/2}$ pole has already been cancelled on every divisor fiber and the elementary source is **uniformly bounded** ($|\text{remainder}| \le 7/2$).

---

#### Path 2 (Replacing the Flat Step $\Delta(s)$ by the Quotient-Block Telescoped Higher-Cesàro / Square-Root Riesz Möbius Kernel)
Why did `abs_setIntegral_kernelDeriv_mul_discrepancy_le` in `MUST-1568` lose control as $L \to \infty$? Because it paired $\partial_s K_y(s)$ with the **0-th Cesàro step discrepancy** $\Delta(s) = \Psi(s) - 2e^{s/2}$, whose divisor-hyperbola error has $O(\sqrt{X})$ boundary variation.

Look at what Modules 31–33 of `RHTower` already proved in:
- [MobiusDivisorCesaroAndSquareGridSqrtRieszBridge.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/MobiusDivisorCesaroAndSquareGridSqrtRieszBridge.lean)
- [HomothetyEigenchannelsAndSecondCesaroDivisorBridge.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/HomothetyEigenchannelsAndSecondCesaroDivisorBridge.lean)
- [QuotientBlockTelescopingAndHigherCesaroHyperbolaKernels.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/QuotientBlockTelescopingAndHigherCesaroHyperbolaKernels.lean)

Specifically:
1. By integrating by parts **once more** (or using the `ccmLogChebyshevDeficitPrimitive` / `chebyshevSqrtRieszAction` bridge), the pairing $-\int_0^\infty \partial_s K_y(s)\,\Delta(s)\,ds$ becomes a pairing of $\partial_s^2 K_y(s)$ (or the light-cone Bessel kernel directly!) against the **First-Cesàro / Square-Root Riesz primitive** of $\Delta$.
2. On the First- and Second-Cesàro / Cell-Integral Square-Root Riesz levels, [`sum_mobius_sub_primitive_dilation_eq_divisorDefect_kernel`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/QuotientBlockTelescopingAndHigherCesaroHyperbolaKernels.lean#L200-L235) and [`divisorUnsignedSecondCesaroDilationChannel_one_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/QuotientBlockTelescopingAndHigherCesaroHyperbolaKernels.lean#L68-L73) prove that:
   - The quotient fibers telescope in closed form;
   - The terminal-band weights factor as **exact non-negative squares** (`((M - q*d)^2 / 2 ≥ 0` and `(1/3)(√M - √(q*d))^2(√M + 2√(q*d)) ≥ 0`);
   - The centered divisor hyperbola $\sum_{k=1}^{j-1} \operatorname{centeredDivisorHyperbola}(k) \le 0$ contributes **unconditionally non-positively** (zero hyperbola loss!).

---

#### Path 3 (Coupling the CHMD Wave Transport to the Pointwise Theta Harmonic Identity & Complete Prime-Chain Variance Factorization)
Look at the other half of the `CHMD` track already in the corpus:
- [CHMDThetaHarmonicIdentity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDThetaHarmonicIdentity.lean) ([`theta_harmonic_identity`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDThetaHarmonicIdentity.lean#L159-L161)):
  $$\sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\bigl(\Theta(x+\log n) + \Theta(x-\log n)\bigr) - \cosh(x/2) = -(\gamma + \log\pi)\Theta(x) + \int_0^\infty \bigl[2\nu(u)\Theta(x) - \omega(u)\bigl(\Theta(x+u)+\Theta(x-u)\bigr)\bigr]\,du.$$
- [CHMDPrimeChainSourceFactorization.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeChainSourceFactorization.lean) ([`doob_source_eq_chain_variances_sub_cosh`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeChainSourceFactorization.lean#L185-L190)):
  For any Doob-transformed test function $\phi = \Theta \cdot v$, the crossing prime quadratic form factors **pointwise at every product index $N = nm$ and logarithmic cut $u$** into a sum of **non-negative conditional chain variances** `chainDensity N p b v u ≥ 0` over prime factors $p \mid N$!

Notice the striking duality between `CHMDThetaHarmonicIdentity` and `CHMDPoleDensityLawAndChebyshevDiscrepancyTransport`:
- In `CHMDPoleDensityLaw`, we replaced the $\cosh(v/2)$ pole wave by the integral $\int_{\mathbb{R}}(D(s+v)+D(s-v))e^{s/2}\,ds$, which left us with a **linear** discrepancy $\Delta(s) = \Psi(s) - 2e^{s/2}$ that ignores multiplicative factorization $N = nm$.
- In [`theta_harmonic_identity`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDThetaHarmonicIdentity.lean#L159-L161), $\cosh(x/2)$ is **already equal** to the symmetric prime shift of Riemann's theta kernel $\Theta(x)$ minus bounded archimedean terms! And when squared into the Doob energy, the multiplicative relation $\log n + \log m = \log(nm)$ on product fibers $N = nm$ turns the prime sum into a sum of **non-negative bipartite prime-chain variances** ([`chainDensity_nonneg`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeChainSourceFactorization.lean#L49-L57)).

---

### 3. Concrete Next Step to Formalize Immediately

To break out of the linear kernel-bound trap of `MUST-1568` and inject the arithmetic identity $\Lambda * 1 = \log$ into the CHMD transport chain, the cleanest, highest-leverage next module is reducing the CHMD RH criterion purely to the Möbius tail (proving that the small-divisor transient contribution to the CHMD transport is unconditionally uniformly bounded in $y \ge 0$ via `abs_kernelDeriv_le` (`MUST-1568`)):

**`CHMDDilationConservationAndMobiusDiscrepancyTransport.lean`** (welding `MUST-1566`–`MUST-1568` to `CCMPrimeDeficitDilationConservation` / `CCMPrimeDeficitMobiusTailLocalization`):
1. **Exact Bridge from $\Delta(s)$ (`chebyshevDiscrepancy`) to `ccmLogChebyshevDeficitPrimitive`:**
   Prove the exact identity relating the CHMD discrepancy $\Delta(s) = \Psi(s) - 2e^{s/2}$ and its integral $\int_0^L \Delta(s)\,ds$ to the unweighted Chebyshev deficit $e^t - \psi(e^t)$ and `ccmLogChebyshevDeficitPrimitive` via Stieltjes/Lebesgue integration by parts:
   $$\int_0^\infty \partial_s K_y(s)\,\Delta(s)\,ds = -\int_0^\infty \bigl(\partial_s^2 K_y(s) - \tfrac12 \partial_s K_y(s)\bigr)\,e^{-s/2}\operatorname{ccmLogChebyshevDeficitPrimitive}(s)\,ds \quad (\text{up to explicit boundary terms}).$$
2. **Inject the Multiplicative-Delay Conservation & Möbius Reconstruction into the CHMD Transport:**
   Substitute the unconditional Möbius-dilation decomposition [`ccmLogChebyshevDeficitPrimitive_eq_moebius_split`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitMobiusTailLocalization.lean#L103-L107) (which came from $\sum_{d \mid k} \Lambda(d) = \log k$ and has **uniformly bounded** centered dilation source $|\operatorname{ccmPrimeDeficitDilationRemainder}(u)| \le 7/2$ and small-divisor head $|\operatorname{ccmPrimeDeficitMobiusTransientHead}(s)| \le (s+14)/4 = O(s) \ll e^{s/2}$) directly into the CHMD derivative transport integral!
3. **Resulting Elimination of $\Lambda(n)$:**
   - The small-divisor transient head ($d \le e^{s/2}$) is $O(s)$, so when multiplied by $e^{-s/2}$ it decays exponentially like $O(s e^{-s/2})$! Paired against the uniformly bounded $|\partial_s K_y(s)| \le \frac{8\log 2}{\pi}$ from `MUST-1568`, its contribution to $\int_0^\infty \partial_s K_y(s)\,\Delta(s)\,ds$ is **unconditionally uniformly bounded in $y$ on $[0,\infty)$**!
   - This kills the entire small-divisor part of the CHMD integral unconditionally using `MUST-1568`, and reduces the CHMD transport $T(y)$ purely to the **explicit Möbius work + large-divisor Möbius tail** (`ccmPrimeDeficitMobiusExplicitWork` + `ccmPrimeDeficitMobiusTransientTail`), where $\Lambda(n)$ has been completely eliminated in favor of $\mu(n)$ and elementary bounded sawtooth remainders.

### done: formal/GaloisForLFunctions/RHTower/CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection.lean

**Conjugated-Laplacian transport of the integrated deficit and the Möbius-dilation injection (Phase 2, concrete next step, with the bridge made exact)**:
- The exact bridge is not the formula written in §3.1 above. With $f_y(s) = e^{-s/2}K_y(s)$ and $D(s) = \int_0^s (e^t - \psi(e^t))\,dt$ (`ccmLogChebyshevDeficitPrimitive`), the identity is
  $$\int_0^\infty \partial_sK_y(s)\,\Delta(s)\,ds = K_y(0) + \int_0^\infty D(s)\,f_y''(s)\,ds,\qquad f_y'' = e^{-s/2}(\partial_s - \tfrac12)^2K_y$$
  (`integral_kernelDeriv_mul_discrepancy_eq_conjugated`): the $\sqrt{\cdot}$ weight of $\Delta$ is the conjugation $e^{-s/2}$ and the two Abel summations are the two derivatives. Proof termwise over prime powers: $D = e^s - 1 - \sum_n \Lambda(n)(s - \log n)_+$, $\int_\ell^\infty (s-\ell) f_y'' = f_y(\ell)$, $\int_0^\infty (e^s - 1) f_y'' = K_y(0) + \int_0^\infty K_y e^{s/2}$, Tonelli with $\sum \Lambda(n) n^{-(\pi - 1/2)} < \infty$.
- Uniform bound (`abs_conjugatedLaplacian_le`): $|f_y''(s)| \le C e^{-s/2}$ for all $y, s$ with $C = \frac1\pi\int r^2\mathrm{sech}^2(r/2)\,dr + \frac{8\log 2}{\pi} + \frac1\pi$, via the Fourier form $\partial_s^2K_y = -\frac1\pi\int \cos(y\sqrt{r^2+2})\,\mathrm{sech}^2(r/2)\,r^2\cos(rs)\,dr$ (`kernelDeriv2_eq_kernelDeriv2Fourier`) and $|D''(v)| \le (64\pi + 264\pi^2)(1+|v|)e^{-\pi|v|}$ for $|v| \ge 1$.
- Möbius injection (`riemannHypothesis_iff_integral_mobiusDeficitRest_mul_conjugatedLaplacian_bddAbove/bddBelow`): with $D = \mathrm{Explicit} + \ell\,M(e^s) + \mathrm{Head} + \mathrm{Tail}$ (`ccmLogChebyshevDeficitPrimitive_eq_moebius_split`), $|\int_0^\infty \mathrm{Head}\,f_y''| \le C\int_0^\infty \frac{s+14}{4}e^{-s/2}\,ds$ uniformly in $y$, so `RiemannHypothesis ↔ ∫₀^∞ (Explicit + ℓ M + Tail) f_y'' bounded above on [0,∞) ↔ bounded below`.
- What it does not give: the Λ-free part is $\sum_n \mu(n)\,\Phi_y(\log n)$ with $\Phi_y(v) = \int_0^\infty S(u) f_y''(u+v)\,du$, a Mertens-type functional. $\Lambda * 1 = \log$ changes the basis of the zero-mode expansion (each piece carries $1/\zeta'(\rho)$-type coefficients summing to $1/\rho^2$); the one-sided bound is Wall 1 in Möbius coordinates.

### done: formal/GaloisForLFunctions/RHTower/CHMDMobiusFoldedTransportOfKleinGordonPrimeWave.lean

**Path 1 completed: the transport as a folded Möbius–kernel pairing (Λ eliminated; the pole cancelled on every divisor fibre; the elementary source enters only through its uniformly bounded centered remainder)**:
- Folded series (`chebyshevDiscrepancyTransport_eq_sub_tsum_mobiusFold`): $T(y) = K_y(0) - \sum_m \mu(m)\,\Phi_y(\log m)$, $\Phi_y(v) = \int_0^\infty S(u)\, f_y''(u+v)\,du$, with $S$ the elementary dilation source (`ccmPrimeDeficitDilationSource`, $|S(u)| \le (7/2 + 5/3 + \tfrac12\log 2\pi)e^u$) and the series absolutely convergent ($|\Phi_y(v)| \le C_y e^{-(\pi-1/2)v}$). Proof: fold $D(s) = \sum_{m \le e^s}\mu(m)S(s-\log m)$ into the conjugated transport identity, Tonelli with indicator terms, $S(0) = 0$ at the lattice points.
- Explicit fold (`mobiusFold_eq`): for $v \ge 0$, $\Phi_y(v) = c_0 f_y(v) + (\gamma+1)e^{-v}\int_v^\infty K_y e^{s/2} + \int_0^\infty R(u) f_y''(u+v)\,du$, $c_0 = \gamma + 1 - \tfrac12\log 2\pi$, $R$ the centered remainder with $|R| \le 7/2$ (tent and pole-density integrations by parts from the base point $v$).
- Three Möbius pieces (`chebyshevDiscrepancyTransport_eq_mobius_pieces`): $T(y) = K_y(0) - c_0 \sum_m \mu(m) m^{-1/2}K_y(\log m) - (\gamma+1)\sum_m \frac{\mu(m)}{m}\int_{\log m}^\infty K_y e^{s/2} - \sum_m \mu(m)\int_0^\infty R(u) f_y''(u+\log m)\,du$; each series absolutely convergent for every $y$; the remainder fold obeys $|\int_0^\infty R f_y''(\cdot+v)| \le 7C e^{-v/2}$ uniformly in $y$ (`abs_remainderFold_le`). `RiemannHypothesis ↔` the sum of the three pieces bounded above on $[0,\infty)$ `↔` bounded below (`riemannHypothesis_iff_mobius_pieces_bddAbove/bddBelow`).
- What it does not give: the uniform remainder bound $7Ce^{-v/2}$ makes $\sum_m |\mu(m)| e^{-\log m/2}$ diverge, so no piece is bounded uniformly in $y$ by absolute values; the one-sided bound is the cancellation in the Möbius Klein–Gordon wave $\sum_m \mu(m)m^{-1/2}K_y(\log m)$ and in the Mertens pairing $\int_0^\infty K_y e^{s/2}\,m_1(e^s)\,ds$ with $m_1(x) = \sum_{m \le x}\mu(m)/m$ (Wall 1 in Möbius coordinates).

### done: formal/GaloisForLFunctions/RHTower/CHMDLatticePoleReplacementAndSignedPrimeWave.lean

**Path 2 assessed and its usable content formalized: the integer lattice replaces the pole density; the hyperbola/Cesàro channels are the Dirichlet-convolution form of Path 1**:
- Lattice pole replacement (`abs_latticeWave_sub_integral_le`): $\bigl|\sum_{n\ge1} n^{-1/2}K_y(\log n) - \int_0^\infty K_y e^{s/2}\bigr| \le 2C_1 \sum_{n\ge1} n^{-3/2}$ uniformly in $y$, $C_1 = (8\log 2 + 2)/\pi$: each cell $[\log n, \log(n+1)]$ carries pole mass exactly $1$, and $f_y = e^{-s/2}K_y$ is $C_1 e^{-s/2}$-Lipschitz (`abs_conjugatedKernelDeriv_le`), so the cell defect is $\le 2C_1 n^{-3/2}$ (`abs_latticeCell_sub_le`); the cells sum to the pole integral (`tsum_latticeCell`).
- Signed prime wave (`chebyshevDiscrepancyTransport_eq_signedPrimeWave_add`, `abs_chebyshevDiscrepancyTransport_sub_signedPrimeWave_le`): $T(y) = \sum_{n\ge1}(\Lambda(n) - 1)\,n^{-1/2}K_y(\log n) + O(1)$ uniformly in $y$; `RiemannHypothesis ↔` the signed prime wave bounded above on $[0,\infty)$ `↔` bounded below (`riemannHypothesis_iff_signedPrimeWave_bddAbove/bddBelow`). The pole of $\zeta$ is cancelled by the lattice measure $\sum_n n^{-1/2}\delta_{\log n}$ itself; the Dirichlet series of the signed measure, $-\zeta'/\zeta - \zeta$, is regular at $s = 1$.
- Why the rest of Path 2 adds no new mechanism: with $g_y(n) = n^{-1/2}K_y(\log n)$ and $\Lambda - 1 = \mu * (\log - d)$, the hyperbola-transposed collapsed kernel $\sum_q (\log q - d(q))\sum_d \mu(d) g_y(qd)$ is the Dirichlet-convolution identity itself; the quotient-block telescoping and the non-positive centered-hyperbola prefix sums bound the **unsigned** divisor channels one-sidedly, but every channel enters with the sign $\mu(d)$, so no one-sided bound on the signed sum follows. The cancellation needed is still $\sum_n (\Lambda(n)-1) n^{-1/2}K_y(\log n) = O(1)$, i.e. Wall 1.

### Phase 2 outcome (state of the route after Paths 1–3)

- **Obstruction B is removed.** The transport has three exact Λ-free forms, all absolutely convergent for every $y$ and all proved in Lean: the conjugated deficit pairing $T(y) = K_y(0) - \int_0^\infty D\,f_y''$ (`CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection`), the folded Möbius series $T(y) = K_y(0) - \sum_m \mu(m)\Phi_y(\log m)$ (`CHMDMobiusFoldedTransportOfKleinGordonPrimeWave`), and the lattice form $T(y) = \sum_{n\ge1}(\Lambda(n)-1)n^{-1/2}K_y(\log n) + O(1)$ (`CHMDLatticePoleReplacementAndSignedPrimeWave`). A bounded $\tilde\mu$ with $\tilde\mu * 1 = \varepsilon$ is $\mu$, and the lattice $N(x) = \lfloor x\rfloor$ determines the prime system, so no Beurling-type countermodel survives these forms.
- **Path 3 (functional equation).** Integrating the theta harmonic identity against $K_y$ rewrites the pole wave as a prime sum of the theta-corrected kernel $K_y - 2K_y\star\Theta$; this is the Weil explicit formula for the even test $K_y$ (Stage 14 zero-side formula) with the zero sum untouched, because $\widehat{\Theta}$ vanishes at the zeros. It injects the functional equation without changing the quantity whose one-sided bound is RH. Pointwise sign conjectures for $K_y - 2K_y\star\Theta$ are false (Bessel oscillation inside the cone for $y > 0$) and would in any case be a pointwise-cone statement (Wall 13).
- **What remains is Obstruction A alone**, now in its sharpest form: $\mathrm{RH} \iff \sup_{y\ge0}\sum_{n\ge1}(\Lambda(n)-1)\,n^{-1/2}K_y(\log n) < \infty$, equivalently bounded below. The measure $\sum_n(\Lambda(n)-1)n^{-1/2}\delta_{\log n}$ is pole-free; $K_y$ has Fourier symbol $\cos(y\sqrt{r^2+2})\,\mathrm{sech}^2(r/2)$, bounded on the real line and of exponential type $|\operatorname{Im} r|$ off it. No kernel estimate, Möbius rearrangement, Cesàro smoothing or lattice bookkeeping changes this: the one-sided bound is the $\sqrt{x}$ cancellation of $\sum_{n \le x}(\Lambda(n) - 1)$ against the Klein–Gordon time orbit of one sech² window (Wall 1). Every stationary point of the light-cone Bessel chirp lies inside the cone at $s = y\gamma/\sqrt{\gamma^2+2}$, so no spatial truncation of the wave is zero-blind.

# Phase 3

### 1. Why Phase 2 Reached the Absolute Limit of Linear (1-Leg) Transport

The three modules you just completed — [CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection.lean) (`MUST-1569`), [CHMDMobiusFoldedTransportOfKleinGordonPrimeWave.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDMobiusFoldedTransportOfKleinGordonPrimeWave.lean) (`MUST-1570`), and [CHMDLatticePoleReplacementAndSignedPrimeWave.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDLatticePoleReplacementAndSignedPrimeWave.lean) (`MUST-1571`) — brought the linear Klein–Gordon transport $T(y)$ to its sharpest possible canonical form:
$$T(y) = \sum_{n=1}^\infty (\Lambda(n) - 1)\,n^{-1/2} K_y(\log n) + O(1) = K_y(0) - \sum_{m=1}^\infty \mu(m)\,\Phi_y(\log m),$$
with
$$\mathrm{RH} \iff \sup_{y \ge 0} \sum_{n=1}^\infty (\Lambda(n) - 1)\,n^{-1/2} K_y(\log n) < \infty \iff \inf_{y \ge 0} \sum_{n=1}^\infty (\Lambda(n) - 1)\,n^{-1/2} K_y(\log n) > -\infty.$$

Why can **no** further linear manipulation of $T(y)$ (integration by parts, higher Cesàro/Riesz kernels, Möbius/hyperbola inversions, or theta convolutions) ever prove this one-sided bound?

Because of a fundamental structural dichotomy recorded in [STATUS.md](file:///Users/michael/Documents/code/hgt/docs/reports/STATUS.md#L455-L536) (**`CANNOT-15`**, **`CANNOT-38`**, **`MUST-08`**):

1. **In `MUST-1529`, Landau's theorem collapsed a 2-leg quadratic form into a 1-leg linear trace:**
   - On the **zero (receiver) side**, Bochner/Toeplitz positivity of all $N \times N$ matrices $\sum_{i,j} c_i c_j \phi_\Lambda(t_j - t_i) \ge 0$ is equivalent to the 2-point bounds $-\phi_\Lambda(0) \le \phi_\Lambda(y) \le \phi_\Lambda(0)$, which by Landau's theorem is equivalent to the one-sided linear bound $\sup_{y \ge 0} \phi_\Lambda(y) < \infty$.
   - **However, on the arithmetic (producer) side, passing from the quadratic form to the single linear function $T(y)$ destroys the square structure!**
2. **Even under RH, $T(y)$ has no sign and no absolute-value bound:**
   - By the explicit formula,
     $$\sum_{n=1}^\infty (\Lambda(n) - 1)\,n^{-1/2} K_y(\log n) = -\sum_\rho m_\rho \cos\bigl(y\sqrt{\gamma_\rho^2+2}\bigr)\operatorname{sech}^2(\gamma_\rho/2) + O(1).$$
   - Even when every $\gamma_\rho$ is real (under RH), $\cos(y\sqrt{\gamma_\rho^2+2})$ oscillates between $-1$ and $+1$. The **only** reason $|\phi_\Lambda(y)| \le \phi_\Lambda(0)$ holds under RH is that the **sum and difference with the origin $y = 0$ are squares on the critical line** ([`CHMDStage13`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage13TwoPointPacketsAndPolarNodeElimination.lean#L199-L230), [`CHMDStage22`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L46-L61)):
     $$\frac{1}{2}\bigl(\phi_\Lambda(0) + \phi_\Lambda(y)\bigr) = \sum_\rho m_\rho \cos^2\Bigl(\frac{y}{2}\sqrt{\gamma_\rho^2+2}\Bigr)\operatorname{sech}^2(\gamma_\rho/2) \ge 0,$$
     $$\frac{1}{2}\bigl(\phi_\Lambda(0) - \phi_\Lambda(y)\bigr) = \sum_\rho m_\rho \sin^2\Bigl(\frac{y}{2}\sqrt{\gamma_\rho^2+2}\Bigr)\operatorname{sech}^2(\gamma_\rho/2) \ge 0.$$
   - When you look at $T(y) = \langle \Lambda - 1, K_y \rangle$ in isolation as a **1-leg linear pairing**, every linear identity ($\Lambda * 1 = \log$, integration by parts, Möbius folding $\langle \mu, \Phi_y \rangle$, hyperbola transposition) simply applies an invertible linear transpose $L^*$ to $K_y$:
     $$\langle \Lambda - 1, K_y \rangle = \langle L(\Lambda - 1), (L^*)^{-1} K_y \rangle.$$
   - Because neither $\Lambda(n) - 1$ nor $\mu(m)$ is one-signed, and $\sum_{m} |\mu(m)|m^{-1/2} = \infty$, **every $L^1 \times L^\infty$ triangle inequality on a 1-leg linear representation of $T(y)$ must diverge as $y \to \infty$**.

**The Lesson:** To produce a one-sided bound without circularly assuming $\sqrt{x}$ cancellation of $\Lambda - 1$ or $\mu$, **the prime weights $\Lambda(n) \ge 0$ must enter inside a 2-leg quadratic form (a sum of squares or one-signed cross-terms) where $\Lambda(n) \ge 0$ has a definite sign**, rather than as the signed difference $\Lambda(n) - 1$ against a 1-leg kernel.

---

### 2. Where the Corpus Already Turns $\Lambda(n) - \text{Pole}$ into Definite-Sign Quadratic Terms

Look across our CHMD corpus at the **two places** where the pole is cancelled **inside a 2-leg quadratic form** so that $\Lambda(n) \ge 0$ has a **favorable, non-negative sign** rather than opposing the pole:

#### Mechanism 1: The Half-Time Convolution-Square factorization of $\frac{1}{2}(\operatorname{chmdWave}(0) + \operatorname{chmdWave}(y))$
Look closely at the 2-point sum criterion [`riemannHypothesis_iff_forall_twoPointSum_nonneg`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean#L46-L51):
$$\mathrm{RH} \iff \forall y \ge 0,\quad \frac{1}{2}\bigl(\operatorname{chmdWave}(0) + \operatorname{chmdWave}(y)\bigr) \ge 0.$$
Why is the **sum** $\frac{1}{2}(\operatorname{chmdWave}(0) + \operatorname{chmdWave}(y))$ structurally superior to $T(y)$ alone and even to the difference $\frac{1}{2}(\operatorname{chmdWave}(0) - \operatorname{chmdWave}(y))$?
1. Its spectral symbol on the complex strip is:
   $$\frac{1 + \cos(y\sqrt{z^2+2})}{2}\operatorname{sech}^2(z/2) = \Bigl[\cos\Bigl(\frac{y}{2}\sqrt{z^2+2}\Bigr)\operatorname{sech}(z/2)\Bigr]^2 = \operatorname{specSq}(\Psi_{y/2})(z),$$
   where
   $$\Psi_{y/2}(z) := \cos\Bigl(\frac{y}{2}\sqrt{z^2+2}\Bigr)\operatorname{sech}(z/2).$$
   Notice that unlike $\sin\bigl(\frac{y}{2}\sqrt{z^2+2}\bigr)$ (which has a square-root branch point at $z = \pm i\sqrt{2}$), $\cos\bigl(\frac{y}{2}\sqrt{z^2+2}\bigr) = \sum_{k=0}^\infty \frac{(-1)^k}{(2k)!}(y/2)^{2k}(z^2+2)^k$ is an **even entire function of $z$ with no branch cut**!
2. Therefore, $\Psi_{y/2} \in \operatorname{EvenStrip}$, and its inverse Fourier transform is a **single real even spatial wave profile** $g_{y/2}(x) = \operatorname{stripTest}(\Psi_{y/2})(x)$, which is the Klein–Gordon evolution at half-time $y/2$ of the strictly positive secant profile $g_0(x) = \operatorname{sech}(\pi x) > 0$:
   $$g_{y/2}(x) = L[\operatorname{sech}(\pi(x + \cdot))](y/2).$$
3. Consequently, the combined kernel $\frac{1}{2}(K_0(s) + K_y(s))$ is the **exact spatial convolution square (autocorrelation)** of $g_{y/2}$:
   $$\frac{1}{2}\bigl(K_0(s) + K_y(s)\bigr) = 2\,(g_{y/2} \star g_{y/2})(s) = 2\int_{\mathbb{R}} g_{y/2}(x)\,g_{y/2}(x+s)\,dx,$$
   and $\frac{1}{2}(\operatorname{chmdWave}(0) + \operatorname{chmdWave}(y))$ is the **complete Weil quadratic form** $\operatorname{Re} W(g_{y/2}, g_{y/2})$ of the single function $g_{y/2}$!
4. Furthermore, at the **polar anti-nodes** $y_k = \frac{\pi(2k+1)}{\sqrt{7/4}}$ ([`polarAntiNodeShift`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage13TwoPointPacketsAndPolarNodeElimination.lean#L278)), $\Psi_{y_k/2}(\pm i/2) = 0$, so **$g_{y_k/2}$ is an exact even pole-free test function** ($\widehat{g}_{y_k/2}(\pm i/2) = 0$) where the $\zeta$-pole vanishes identically before any lattice or Chebyshev subtraction!

---

#### Mechanism 2: The CHMD Doob Odd-Sector & One-Signed Cross-Sign Bonus (`MUST-1541`–`MUST-1565`)
Now look at the other branch of CHMD in our corpus — the **Doob Graph / Odd-Sector Track** ([CHMDOddSectorCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean), [CHMDSinglePrimeWindow.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDSinglePrimeWindow.lean), [CHMDOddWindowCrossSign.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddWindowCrossSign.lean), [CHMDOddCrossSignBonus.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddCrossSignBonus.lean), [CHMDPrimeChainSourceFactorization.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeChainSourceFactorization.lean)) — and compare it with the 1-leg wave track:

1. **How the Doob gauge eliminates the pole without creating a signed weight $\Lambda(n) - 1$:**
   Instead of subtracting the continuous density $e^{s/2}$ or the lattice $\sum_n n^{-1/2}\delta_{\log n}$ from $\sum_n \Lambda(n)n^{-1/2}\delta_{\log n}$ (which turns $\Lambda(n) \ge 0$ into the sign-indefinite weight $\Lambda(n) - 1$), [CHMDThetaHarmonicIdentity.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDThetaHarmonicIdentity.lean#L159-L161) (`MUST-1543`) uses the pointwise harmonic identity of Riemann's theta kernel $\Theta(x)$:
   $$\sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\bigl(\Theta(x+\log n) + \Theta(x-\log n)\bigr) = \cosh(x/2) - (\gamma + \log\pi)\Theta(x) + \int_0^\infty \bigl[2\nu(u)\Theta(x) - \omega(u)(\Theta(x+u)+\Theta(x-u))\bigr]\,du.$$
   When we write a test function in the Doob gauge $f(x) = \Theta(x)v(x)$, this pointwise identity **completes the square** between the $\cosh(x/2)$ mass and the prime shift sum (`MUST-1541`):
   $$E(v) = \int_0^\infty \omega(t)\int_{\mathbb{R}} \Theta(x)\Theta(x+t)\bigl(v(x)-v(x+t)\bigr)^2\,dx\,dt + \sum_{n=2}^\infty \frac{\Lambda(n)}{\sqrt{n}}\int_{\mathbb{R}} \Theta(x)\Theta(x+\log n)\bigl(v(x)-v(x+\log n)\bigr)^2\,dx - \int_{\mathbb{R}} v(x)^2\Theta(x)\cosh(x/2)\,dx.$$
2. **In the Odd Sector (`MUST-1555`), the pole vanishes and RH is purely `E(v) ≥ 0` on odd `v`:**
   By [`riemannHypothesis_iff_no_odd_bound_state`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean) (`MUST-1555`),
   $$\mathrm{RH} \iff \forall \text{ odd } v \in C^2_c(\mathbb{R}),\quad E(v) = \Lambda_\infty(\Theta v) - \sum_{n=2}^\infty \frac{2\Lambda(n)}{\sqrt{n}}\int_{\mathbb{R}}\Theta(x)\Theta(x+\log n)v(x)v(x+\log n)\,dx \ge 0.$$
   And by `MUST-1546`–`MUST-1551` ([CHMDNoWeylAboveThreshold.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDNoWeylAboveThreshold.lean), [CHMDPurePointAboveThreshold.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPurePointAboveThreshold.lean)), **there is NO cusp escape at infinity**: all negative energy / spectrum above $1/2$ is confined to a compact window $|x| \le R$!
3. **Why the prime sign flips to FAVORABLE on the one-signed odd cone (`MUST-1562`, `MUST-1565`):**
   Look at what happens for an odd test $v(-x) = -v(x)$ with $v(x) \ge 0$ on $[0, \infty)$:
   - Whenever $x < 0$ and $x + \log n > 0$ (i.e., $x \in (-\log n, 0)$, a jump across the origin), $v(x) \le 0$ and $v(x+\log n) \ge 0$ have **opposite signs**, so
     $$-2v(x)v(x+\log n) = +2|v(x)|\,|v(x+\log n)| \ge 0!$$
   - Thus every prime jump across the origin contributes a **POSITIVE prime cross-sign bonus**
     $$+\frac{4\Lambda(n)}{\sqrt{n}}\int_0^{\log n} \Theta(s)|v(s)|\,\Theta(\log n - s)|v(\log n - s)|\,ds \ge 0,$$
     in exact parallel to the archimedean cross-sign bonus (`MUST-1565`, [`weilLevyForm_eq_abs_add_bonus`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddCrossSignBonus.lean))
     $$+4\iint_{s,t>0} \omega(s+t)\,\Theta(s)|v(s)|\,\Theta(t)|v(t)|\,ds\,dt \ge 0!$$
   - And for jumps on the same side of the origin ($x > 0$), [CHMDPrimeChainSourceFactorization.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDPrimeChainSourceFactorization.lean#L185-L190) factors the entire prime crossing source into a countable sum of **non-negative bipartite conditional chain variances** `chainDensity N p b v u ≥ 0` on every divisor fiber $N = nm$!

---

### 3. The New Path Forward: How to Resolve the Impasse

We should **stop doing 1-leg linear rewrites of $T(y)$** (which are now completely classified and formalized in `MUST-1566`–`MUST-1571`) and move the attack to the **2-leg quadratic / Doob-resolvent / convolution-square** level where positivity and prime-sign flipping actually exist.

Specifically, there are **two concrete, high-impact formalization steps** directly ahead of us:

#### Step A (On the CHMD Doob Odd-Sector Track, extending `MUST-1561`–`MUST-1565`):
**Exact Prime Cross-Sign Bonus & Window Coercivity on the One-Signed Odd Cone (`CHMDOddPrimeCrossSignBonusAndWindowPositivity.lean`)**
1. In `MUST-1562` ([CHMDOddWindowCrossSign.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDOddWindowCrossSign.lean)), the prime cross-terms on the one-signed odd cone ($v$ odd, $v \ge 0$ on $[0,\infty)$, $\operatorname{supp} v \subseteq (-L/2, L/2)$ with $L \le 2\log 2$) were merely dropped via $\operatorname{phiDoobPrimeCross} \le 0$.
2. In fact, for **every** $n \ge 2$ and **any** support length $L$, the prime cross-term $-\int_{\mathbb{R}} \operatorname{phiDoobPrimeCross}\ v\ n\ x\,dx$ on a one-signed odd test $v$ splits **exactly** into:
   $$\underbrace{+\frac{2\Lambda(n)}{\sqrt{n}}\int_0^{\log n} g(s)\,g(\log n - s)\,ds}_{\text{Positive opposite-side prime bonus } B_n(g) \ge 0} \;-\; \underbrace{\frac{4\Lambda(n)}{\sqrt{n}}\int_0^\infty g(s)\,g(s+\log n)\,ds}_{\text{Same-side prime cross term } C_n(g)}, \qquad g(s) := \Theta(s)|v(s)|.$$
3. When $\operatorname{supp} v \subseteq (-L/2, L/2)$ with $L \le 2\log n$, the same-side term $C_n(g)$ **vanishes identically**, while the positive opposite-side bonus $B_n(g) \ge 0$ **remains strictly non-negative**!
   Hence on $L \le 2\log 2$, *every* prime power $n \ge 2$ contributes $+B_n(\Theta|v|) \ge 0$, so:
   $$E(v) = \Lambda_\infty(\Theta|v|) + 4\,\operatorname{crossSignBonus}(\Theta|v|) + \sum_{n=2}^\infty B_n(\Theta|v|)!$$
4. Moreover, combining the Fourier representation of $\Lambda_\infty(g) = \frac{1}{2\pi}\int_{\mathbb{R}} |\widehat{g}(r)|^2 \gamma(r)\,dr$ (`MUST-1547`) with the positive quadrant form $4\iint_{s,t>0} \omega(s+t)g(s)g(t)\,ds\,dt$ (`MUST-1565`) and the positive prime bonuses $B_n(g)$ gives an explicit prime-assisted coercivity lower bound on the one-signed odd cone beyond the bare $4/9$ archimedean window!

#### Step B (On the CHMD Wave Track, upgrading `MUST-1571` from 1-Leg to 2-Leg Convolution Square):
**The Half-TimeSecant Convolution-Square Identity for `chmdWave 0 + chmdWave y` (`CHMDHalfTimeSecantAutocorrelationAndPolarAntiNodeTests.lean`)**
1. Formalize the exact half-time spectral factor
   $$\Psi_{y/2}(z) := \cos\Bigl(\frac{y}{2}\sqrt{z^2+2}\Bigr)\operatorname{sech}(z/2) \in \operatorname{EvenStrip},$$
   proving that $\operatorname{specSq}(\Psi_{y/2})(z) = \frac{1}{2}\bigl(\operatorname{specSq}(\operatorname{sechHalf})(z) + \operatorname{rhoCosShift}(y, \operatorname{sechHalf})(z)\bigr)$ and hence:
   $$\frac{1}{2}\bigl(\operatorname{chmdWave}(0) + \operatorname{chmdWave}(y)\bigr) = \operatorname{evenWeilDensity}\ \Lambda\ (\operatorname{specSq}\ \Psi_{y/2}) = \operatorname{Re} W(g_{y/2}, g_{y/2}),$$
   where $g_{y/2} = \operatorname{stripTest}(\Psi_{y/2})$ is a **single real even spatial wave**, and $\frac{1}{2}(K_0(s) + K_y(s)) = 2(g_{y/2} \star g_{y/2})(s)$ is its **exact spatial convolution square**.
2. Prove the light-cone transmutation formula for $g_{y/2}(x)$ from the positive initial profile $g_0(x) = \operatorname{sech}(\pi x) > 0$, and show that at every polar anti-node $y_k = \frac{\pi(2k+1)}{\sqrt{7/4}}$, $g_{y_k/2}$ is an **exact pole-free even test function** ($\widehat{g}_{y_k/2}(\pm i/2) = 0$), directly linking the CHMD causal wave to the **Even Pole-Free Cone** of `MUST-1524` (`EvenSectorPolarRigidity.lean`)!


### done: formal/GaloisForLFunctions/RHTower/CHMDOddPrimeCrossSignBonusAndWindowPositivity.lean (Step A, items 1–3)

- Exact split for every `n` and every support (`neg_integral_phiDoobPrimeCross_eq`): $-\int \mathrm{phiDoobPrimeCross}\,v\,n = B_n(g) - C_n(g)$, $g = \Theta|v|$, $B_n(g) = \frac{2\Lambda(n)}{\sqrt n}\int_0^{\log n} g(s)g(\log n - s)\,ds \ge 0$, $C_n(g) = \frac{4\Lambda(n)}{\sqrt n}\int_0^\infty g(s)g(s+\log n)\,ds \ge 0$.
- Window vanishing: $C_n = 0$ for $L \le 2\log n$ (`sameSideCross_eq_zero_of_window`), $B_n = 0$ for $\log n \ge L$ (`oppositeSideBonus_eq_zero_of_le`); on $L \le 2\log 2$ only $B_2, B_3$ survive (`tsum_oppositeSideBonus_eq_two_add_three`).
- Window identity (`sourceEnergy_eq_levy_abs_add_bonus_add_primes`): $E(v) = \Lambda_\infty(\Theta|v|) + 4\,\mathrm{bonus}(\Theta|v|) + B_2(\Theta|v|) + B_3(\Theta|v|)$.
- Item 4 (coercivity beyond $4/9$): not reached. The identity gives $E(v) \ge \Lambda_\infty(\Theta|v|)$ plus explicit nonnegative channels; positivity of the right side on the window is true under RH (odd tests are primitive) but its unconditional proof needs the window programme's sharp kernel analysis extended by the prime channels; crude Fourier/uncertainty bounds (|f̂(r)| ≤ |r|L∫g/2, γ ≥ γ(0)) miss by two orders of magnitude.