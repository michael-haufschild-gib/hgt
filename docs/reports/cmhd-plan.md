Viewed CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean:1-120
Viewed CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean:1-120

In our Lean corpus, the terminal receiver for the CHMD causal-wave route is already 100% formalized and unconditional in [CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDGrowthPositivityCollapseAndTwoPointCriterion.lean) and [CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion.lean).

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
