Viewed FermiNymanWitnessGermRigidity.lean:1-120
Viewed FermiNymanDyadicFoldGeometry.lean:380-495
Viewed FermiNymanWitnessGermLaws.lean:1-120
Viewed FermiNymanBeurlingWitnessSignature.lean:1-120
Viewed FermiNymanWitnessGermLaws.lean:250-511

Exactly. Here is why [`MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean) gave the **equivalence** (`riemannHypothesis_iff_witness_top_octave_energy_le_lower_half`) without the **arithmetic inequality** needed to discharge its right-hand side:

---

### 1. Why the Top-Octave Criterion in §3 Was Purely Kinematic (Prime-$2$ Only)

In §3 of [`MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean#L298-L353), the identity
$$\operatorname{Re}\,\mathcal{Q}_{\mathrm{dyad}}(w, w) = \frac{1}{2}\left(\int_0^{1/2} \|w(t)\|^2\,dt - \int_{1/2}^1 \|w(t)\|^2\,dt\right)$$
is a purely kinematic rearrangement of $2\int_0^{1/2}\|w\|^2 - \int_0^1\|w\|^2$. It uses only the **prime-$2$ dyadic split** $(0, 1] = (0, 1/2] \sqcup (1/2, 1]$.

For a power mode $w_\rho(t) = t^{\bar{\rho}-1}$ with $\sigma = \operatorname{Re}(\rho) \in (1/2, 1)$, the ratio of top-octave energy to lower-half energy is:
$$\frac{\int_{1/2}^1 t^{2\sigma - 2}\,dt}{\int_0^{1/2} t^{2\sigma - 2}\,dt} = 2^{2\sigma - 1} - 1 > 1 \qquad (\sigma > 1/2).$$
And $w_\rho \in \mathcal{W}_{\mathrm{FN}}$ if and only if
$$\int_0^1 \varphi_a(t)\,t^{\rho - 1}\,dt = -a^{-\rho}\,\frac{1 - 2^{1-\rho}}{\rho}\,\zeta(\rho) = 0 \iff \zeta(\rho) = 0.$$
Thus, the inequality $\int_{1/2}^1 \|w(t)\|^2\,dt \le \int_0^{1/2} \|w(t)\|^2\,dt$ holds on $\mathcal{W}_{\mathrm{FN}}$ **if and only if** the arithmetic orthogonality $\langle w, \varphi_a \rangle = 0$ ($a \ge 1$) rules out every $\sigma > 1/2$ mode.

---

### 2. Why §2 (Arithmetic Combinators) and §3 (Top-Octave Inequality) Did Not Close the Loop

In §2 of [`MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean#L265-L290), we built the arithmetic cell-isolating combinator
$$\Delta_{k, N}(t) = R_{k, N}(t) - R_{k+1, N}(t) \in \operatorname{span}\{\varphi_d : 1 \le d \le N\},$$
which satisfies $\Delta_{k, N}(t) = \delta_{n, k}$ on every bulk cell $I_n = (\frac{1}{n+1}, \frac{1}{n}]$ for $1 \le n \le N$.

When applied to a witness $w \in \mathcal{W}_{\mathrm{FN}}$ at $k = 1$ (the top octave $I_1 = (1/2, 1]$), witness orthogonality $\langle \Delta_{1, N}, w \rangle_{L^2(0, 1]} = 0$ gives the exact arithmetic transfer identity:
$$\int_{1/2}^1 w(t)\,dt = -\int_0^{\frac{1}{N+1}} \Delta_{1, N}(t)\,w(t)\,dt,$$
where all intermediate cells $I_2, \dots, I_N \subset (\frac{1}{N+1}, \frac{1}{2}]$ have been **identically cancelled** by Möbius inversion $\sum_{d \mid m} \mu(d) = \delta_{m, 1}$ and binary resolvent telescoping $(I - 2 S_2)^{-1}$.

However, two things prevented this from yielding the required arithmetic inequality on $\int_{1/2}^1 \|w(t)\|^2\,dt$ (or on the linear functional $\operatorname{dyadicLogMean}(w) = \int_{1/2}^1 w(t)\,\frac{dt}{t} = 0$ from [`riemannHypothesis_iff_fermiNymanWitness_dyadicLogMean_eq_zero`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/FermiNymanWitnessGermLaws.lean#L495-L509)):

1. **Integer generators are piecewise constant on $(1/2, 1]$:**
   By [`fermiNymanGen_eq_zero_on_top_octave_of_two_le`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean#L42-L54), $\varphi_d(t) = 0$ on $(1/2, 1]$ for all $d \ge 2$ and $\varphi_1(t) = -1$ on $(1/2, 1]$. Thus integer combinations $\sum_{d=1}^N c_d \varphi_d$ only probe the single scalar $\int_{1/2}^1 w(t)\,dt$ on the top octave, whereas bounding $\int_{1/2}^1 \|w(t)\|^2\,dt$ (or probing $\int_{1/2}^1 w(t)\,\frac{dt}{t}$ via [`riemannHypothesis_iff_fermiNymanWitness_dyadicLogMean_eq_zero`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/FermiNymanWitnessGermLaws.lean#L495-L509)) requires either:
   - the **dyadic dilation invariance** of $\mathcal{W}_{\mathrm{FN}}$ ($w \in \mathcal{W}_{\mathrm{FN}} \implies w(\cdot / m) \in \mathcal{W}_{\mathrm{FN}}$ for all $m \ge 1$, or continuous dilations $\varphi_a$ for $a \in [1, 2]$) to resolve sub-intervals inside $(1/2, 1]$, or
   - directly approximating the fold-free Haar target $\operatorname{dyadicHaar}(t) = \mathbf{1}_{(1/2, 1]}(t)/t - \mathbf{1}_{(0, 1/2]}(t)/t$ in $L^2(0, 1]$.

2. **The Arithmetic Tail Energy Inequality on $(0, \frac{1}{N+1}]$:**
   Applying Cauchy–Schwarz to the transfer identity $\int_{I_k} w(t)\,dt = -\int_0^{\frac{1}{N+1}} \Delta_{k, N}(t)\,w(t)\,dt$ gives
   $$\left|\int_{I_k} w(t)\,dt\right|^2 \le \left(\int_0^{\frac{1}{N+1}} |\Delta_{k, N}(t)|^2\,dt\right) \cdot \underbrace{\left(\int_0^{\frac{1}{N+1}} \|w(t)\|^2\,dt\right)}_{m_w(1/(N+1)) \le \int_0^{1/2} \|w\|^2}.$$
   To turn this into the required upper bound $\int_{1/2}^1 \|w\|^2 \le \int_0^{1/2} \|w\|^2$ (or $\operatorname{dyadicLogMean}(w) = 0$ as $N \to \infty$), one needs an **explicit arithmetic upper bound on the tail $L^2$-norm** $\int_0^{\frac{1}{N+1}} |\Phi_N(t)|^2\,dt$ of the approximant $\Phi_N \in \operatorname{span}\{\varphi_d : d \le N\}$ that stays bounded (or $o(1)$) as $N \to \infty$ rather than growing like $O(N)$.



   Viewed STATUS.md:1-150
Viewed rh-current-frontier-map.md:1-150
Viewed rh-current-frontier-map.md:240-474
Viewed rh-current-frontier-map.md:150-240

To see what is still missing in `BiScaleUncertainty` to deliver the required upper bound and close the proof of the Riemann Hypothesis, look at **why every existing upper bound in `BiScaleUncertainty` scales like $\Theta(N)$ instead of $o(1)$ as $N \to \infty$**:

---

### 1. The Exact Bottleneck in `BiScaleUncertainty`: The $\|c\|_{\ell^1}^2 \asymp N^2$ Triangle-Inequality Barrier

Across all three branches of Route PM (`FZZ-P`, `CTF`/Selberg tail, and `PW-B`/witness combinators), every producer theorem currently in `BiScaleUncertainty` decomposes the $L^2$ error or variance into:
$$\text{Total Energy} = \text{Smooth Main Term} + \text{Discrete Sawtooth / Floor Remainder}.$$

- **The Smooth Main Term is already controlled:**
  - In [`SelbergSieveTailQuadraticFormAndTruncatedDivisorGram.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/SelbergSieveTailQuadraticFormAndTruncatedDivisorGram.lean#L263-L270), the smooth LCM Gram form $\sum_{d_1, d_2 \le N} \frac{c(d_1)c(d_2)}{\operatorname{lcm}(d_1, d_2)}$ is diagonalized into $\sum_{e=1}^N \varphi(e)\bigl(\sum_{e \mid d} \frac{c(d)}{d}\bigr)^2$, whose minimum over $c(1)=1$ is $\bigl(\sum_{e=1}^N \frac{\mu^2(e)}{\varphi(e)}\bigr)^{-1} \sim \frac{1}{\log N} \to 0$.
  - In [`DivisorAverageChebyshevAndDyadicBlockVarianceProducer.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/DivisorAverageChebyshevAndDyadicBlockVarianceProducer.lean#L18-L38), Stirling's formula cancels the leading $K\log K$ term in $\sum_{j=1}^K (\psi(K/j) - K/j) = \log(K!) - K H_K$.
- **Why the Discrete Sawtooth Remainder blows up as $\Theta(N)$:**
  Whenever an integer floor $\lfloor X/d \rfloor$ is compared to its smooth ratio $X/d$, the centered sawtooth discrepancy $\widetilde{B}_1(n/d) = \{n/d\} - \frac{d-1}{2d}$ is bounded in every existing module by the **pointwise triangle inequality**:
  $$\Bigl|\sum_{d=1}^N c_d\,\widetilde{B}_1\!\left(\frac{n}{d}\right)\Bigr| \le \frac{1}{2}\sum_{d=1}^N |c_d| = \frac{1}{2}\|c\|_{\ell^1}.$$
  Because $\|c\|_{\ell^1} \asymp \frac{N}{\log N}$ for Möbius or Selberg sieve weights, squaring $\|c\|_{\ell^1}$ produces an error of size **$\|c\|_{\ell^1}^2 \asymp \frac{N^2}{(\log N)^2}$**:
  1. In [`SelbergSieveTailQuadraticFormAndTruncatedDivisorGram.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/SelbergSieveTailQuadraticFormAndTruncatedDivisorGram.lean#L282-L320), Graham's floor-to-LCM bound `abs_sum_sq_divisorSum_sub_lcm_main_le` adds $+\bigl(\sum_{d=1}^N |c_d|\bigr)^2 \asymp N^2$. When summed against the reciprocal cell weights $\frac{1}{k(k+1)}$ over $k > N$, this $+\|c\|_{\ell^1}^2$ remainder contributes $\frac{\|c\|_{\ell^1}^2}{N+1} \asymp \frac{N}{(\log N)^2} \to \infty$ instead of $o(1)$.
  2. In [`LocalToGlobalTailStabilityAndWitnessIndicatorPairing.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/LocalToGlobalTailStabilityAndWitnessIndicatorPairing.lean) and [`DyadicRenewalStirlingAndLogMobiusTotalEnergyProducer.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/DyadicRenewalStirlingAndLogMobiusTotalEnergyProducer.lean), the tail bound on $(0, \frac{1}{N+1}]$ is $\frac{2(1 + 9\|c\|_{\ell^1}^2)}{N+1} \asymp N \to \infty$.
  3. In [`CenteredRamanujanVarianceAndAbelCofactorCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/CenteredRamanujanVarianceAndAbelCofactorCancellation.lean#L211-L234), bounding $|\widetilde{S}_{\varepsilon, Q}(N)| \le \frac{1}{2}\sum_{d=2}^Q d^{-\varepsilon} \asymp Q^{1-\varepsilon}$ pointwise gives $\sum_{N=1}^\infty \frac{\widetilde{S}_{\varepsilon, Q}(N)^2}{N(N+1)} \ll Q^{2(1-\varepsilon)} \to \infty$ as $Q \to \infty$ for all $\varepsilon < 1$.

---

### 2. What Is Missing in `BiScaleUncertainty` to Beat the $\|c\|_{\ell^1}^2$ Barrier and Close RH

To replace those $\Theta(N)$ triangle-inequality bounds with the $o(1)$ (or uniform-in-$Q$) upper bound that closes the proof route, `BiScaleUncertainty` is missing **three concrete mathematical tools**:

#### Missing Tool 1: Exact Vasyunin / Báez–Duarte Reciprocity Formula for the Global $L^2(0, 1]$ Sawtooth Gram Matrix (Eliminating Graham's $+\|c\|_{\ell^1}^2$ Truncation Error)
- In [`SelbergSieveTailQuadraticFormAndTruncatedDivisorGram.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/SelbergSieveTailQuadraticFormAndTruncatedDivisorGram.lean), the $+\|c\|_{\ell^1}^2$ error arose only because the tail integral on $(0, \frac{1}{N+1}]$ was approximated by truncating at a finite cell $N + K$ and replacing $\lfloor \frac{N+K}{\operatorname{lcm}(d_1, d_2)} \rfloor$ by $\frac{N+K}{\operatorname{lcm}(d_1, d_2)}$.
- Instead of truncating at $N + K$, the exact tail Gram matrix on $(0, \frac{1}{N+1}]$ is the **exact global Gram matrix on $(0, 1]$ minus the finite bulk head $1 \le n \le N$**:
  $$\int_0^{\frac{1}{N+1}} \varphi_{d_1}(t)\,\varphi_{d_2}(t)\,dt = \int_0^1 \varphi_{d_1}(t)\,\varphi_{d_2}(t)\,dt - \sum_{n=1}^N \frac{A_{n, d_1}\,A_{n, d_2}}{n(n+1)}.$$
- And the global Gram entry $\int_0^1 \{1/(d_1 t)\}\{1/(d_2 t)\}\,dt$ is given **exactly** (with zero floor-truncation error!) by **Vasyunin's reciprocity formula**:
  $$\int_0^1 \left\{\frac{1}{d_1 t}\right\}\left\{\frac{1}{d_2 t}\right\} dt = \frac{\gcd(d_1, d_2)}{d_1 d_2}\Bigl(\log(2\pi) - \gamma + \frac{d_1 + d_2}{2\gcd(d_1, d_2)} - 1\Bigr) + V\!\left(\frac{d_1}{\gcd(d_1, d_2)},\, \frac{d_2}{\gcd(d_1, d_2)}\right),$$
  where the Vasyunin cotangent sum $V(a, b) = \frac{1}{a}\sum_{r=1}^{a-1} \{\frac{br}{a}\}\log\sin\frac{\pi r}{a} + \frac{1}{b}\sum_{r=1}^{b-1} \{\frac{ar}{b}\}\log\sin\frac{\pi r}{b}$ obeys exact Euclidean continued-fraction reciprocity $V(a, b) \leftrightarrow V(b \bmod a, a)$.
- **What is needed in `BiScaleUncertainty`:** Formalizing the exact Vasyunin/Báez–Duarte Gram identity on $L^2((0, 1], dt)$ and bounding the off-diagonal Vasyunin reciprocity quadratic form $\sum_{d_1, d_2 \le N} c(d_1)c(d_2) V(d_1', d_2')$ without using the $\ell^1$ triangle inequality.

#### Missing Tool 2: Finite Cotangent / Additive-Character Expansion of `centeredDiscreteSawtooth` + Bilinear Möbius Cancellation on $(0, 1/2)$ (`FZZ-P`)
- In [`CenteredRamanujanVarianceAndAbelCofactorCancellation.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/CenteredRamanujanVarianceAndAbelCofactorCancellation.lean), `centeredDiscreteSawtooth d N` is periodic mod $d$ with mean $0$, so it has the exact finite Fourier expansion:
  $$\widetilde{B}_1\!\left(\frac{N}{d}\right) = -\frac{1}{2d}\sum_{a=1}^{d-1} \Bigl(1 + i\cot\frac{\pi a}{d}\Bigr) e^{2\pi i a N / d}.$$
- Grouping $a/d = r/q$ in lowest terms ($\gcd(r, q) = 1$, $d = m q$) rewrites the centered sawtooth prefix $\widetilde{S}_{\varepsilon, Q}(N)$ as a linear combination of primitive additive harmonics $e^{2\pi i r N / q}$ whose coefficients are **incomplete Möbius sums on arithmetic/multiplicative progressions**:
  $$M_\varepsilon(q; Q) := \sum_{1 \le m \le Q/q} \frac{\mu(m q)}{(m q)^\varepsilon}.$$
- **What is needed in `BiScaleUncertainty`:**
  1. A **Montgomery–Vaughan / Hilbert bilinear inequality** for the reciprocal-weighted inner products of primitive harmonics $\sum_{N=1}^\infty \frac{e^{2\pi i (r_1/q_1 - r_2/q_2) N}}{N(N+1)}$ (controlling the initial segment $N \le \max(q_1, q_2)$ where the $1/(N(N+1))$ weight is concentrated), and
  2. **Sub-linear cancellation of the Möbius coefficients** $|M_\varepsilon(q; Q)| \ll (Q/q)^{1/2 - \varepsilon + \delta}$ (rather than the trivial $\sum_{m \le Q/q} m^{-\varepsilon} \asymp (Q/q)^{1-\varepsilon}$), ** plus** the Dirichlet-series pole bridge $\mathcal{M}[F_\varepsilon](s) = -\frac{1-2^{1-s-\varepsilon}}{(s+\varepsilon-1)\zeta(s+\varepsilon)}$ in [`PMPowerDampedMobiusMellin.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusMellin.lean).

#### Missing Tool 3: Multi-Scale Smoothed / Fejér–Selberg Cell Combinators for the Top-Octave Witness Inequality (`PW-B`)
- In [`MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BiScaleUncertainty/MultiOctaveStepBrickPartitionAndWitnessDyadicPositivity.lean#L265-L290), our exact Kronecker combinator $\Delta_{k, N} = R_{k, N} - R_{k+1, N}$ used **sharp unsmoothed Möbius weights** $\mu(m)$ and **sharp binary resolvent weights** $2^j$, which forced its tail $L^2$-norm on $(0, \frac{1}{N+1}]$ to blow up.
- By [`riemannHypothesis_iff_fermiNymanWitness_dyadicLogMean_eq_zero`](file:///Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/FermiNymanWitnessGermLaws.lean#L495-L509), we do **not** need exact cell Kronecker deltas $\delta_{n, k}$ for every $k$; we only need a sequence of generator combinations $\Phi_N = \sum_{d=1}^N c_{N, d}\,\varphi_d$ that:
  1. Matches the fold-free Haar target $\operatorname{dyadicHaar}(t) = \mathbf{1}_{(1/2, 1]}(t)/t - \mathbf{1}_{(0, 1/2]}(t)/t$ on the bulk $(\frac{1}{N+1}, 1]$ with $L^2$ error $o(1)$, **and**
  2. Has vanishing tail $L^2$-norm $\int_0^{\frac{1}{N+1}} |\Phi_N(t)|^2\,dt \to 0$ as $N \to \infty$.
- **Why this requires the same arithmetic cancellation:**
  On the bulk $(\frac{1}{N+1}, 1]$, $\Phi_N(t) = \sum_{d \mid n} c_{N, d} - 2\sum_{2d \mid n} c_{N, d}$ on cell $I_n$. Approximating $\operatorname{dyadicHaar}(t)$ on $(\frac{1}{N+1}, 1]$ forces the Dirichlet convolution $(1 * c_N)(n) \approx 1$ for $1 \le n \le N$, which forces $c_{N, d} \approx \mu(d)$ (e.g., Selberg/Báez–Duarte weights $c_{N, d} = \mu(d)\frac{\log(N/d)}{\log N}$). Making both the bulk defect $\sum_{n=1}^N \frac{((1 * c_N)(n) - 1)^2}{n(n+1)}$ and the tail norm $\int_0^{\frac{1}{N+1}} |\sum_{d=1}^N c_{N, d}\varphi_d(t)|^2\,dt$ tend to $0$ simultaneously requires **cancellation of the signed Möbius weights $c_{N, d}$ across the off-diagonal terms of the Vasyunin/sawtooth Gram matrix** (Tools 1 & 2 above).