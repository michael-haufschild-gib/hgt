
To bound $E_T(\varepsilon)$ (equivalently $\mathcal{V}_\varepsilon(Q)$) uniformly for $0 < \varepsilon < 1/2$, we have to be completely clear about what that bound is: **even for a single fixed $\varepsilon \in (0, 1/2)$, $\sup_T E_T(\varepsilon) < \infty$ is equivalent to $\zeta(s)$ having no zeros in the half-plane $\operatorname{Re}(s) > \frac{1}{2} + \varepsilon$.** No known method in mathematics has ever proved a zero-free half-plane $\operatorname{Re}(s) > 1 - \delta$ for any $\delta > 0$.

When we look specifically at the formulas for $E_T(\varepsilon)$ and $\mathcal{V}_\varepsilon(Q)$ that we now have in Lean, there are **four concrete mathematical tools** that we are missing—and each one explains why our existing 74 modules hit a wall:

---

### 1. Cross-Depth ($\omega(n)$ vs. $\omega(n)+1$) Cancellation in the Gram Quadratic Form
- **What we have now:**
  Our spectral tools (Modules 60, 63, 70, 72, 73) analyze $\mathcal{G}^{\text{ec}}(p, q)$ by fixing a base modulus $r$ and dilating by one prime at a time ($pr, qr$ with $p, q \nmid r$), giving the exact identity
  $$\mathcal{G}^{\text{ec}}(pr, qr) + \mathcal{G}^{\text{ec}}(pr, r) + \mathcal{G}^{\text{ec}}(qr, r) + \mathcal{G}^{\text{ec}}(r, r) = \sqrt{pq}\,\Phi_r\Bigl(\frac{p}{q}\Bigr).$$
- **Why this cannot bound $\mathcal{V}_\varepsilon(Q)$ by itself:**
  Within a single prime-star $\{p r : p \text{ prime}\}$ (or any fixed number of prime factors $\omega(n) = k$), the Möbius sign $\mu(pr) = -\mu(r)$ is **constant across all primes $p$**. Because $\Phi_r(p/q) \approx \mathcal{G}(r, r) > 0$ for nearby primes $p \approx q$, the terms $Y_\varepsilon(pr) Y_\varepsilon(qr) \mathcal{G}^{\text{ec}}(pr, qr)$ for $p \approx q$ are **all positive**.
  In fact, restricting the Dirichlet series $\zeta(s+\varepsilon)^{-1} = \sum \mu(n) n^{-s-\varepsilon}$ to a fixed prime-factor depth $\omega(n) = k$ gives $\frac{(-1)^k (\log \zeta(s+\varepsilon))^k}{k!}$, which **still has a singularity at $s = 1 - \varepsilon$** and therefore **diverges like $Q^{1-2\varepsilon}$** in $L^2(\operatorname{Re} s = 1/2)$ for every $\varepsilon < 1/2$.
- **The missing tool:**
  The singularity at $s = 1 - \varepsilon$ only cancels when the alternating series $\sum_{k=0}^\infty \frac{(-1)^k (\log \zeta(s+\varepsilon))^k}{k!} = \exp(-\log \zeta(s+\varepsilon)) = \zeta(s+\varepsilon)^{-1}$ is summed **coherently across all multiplicative depths $k = \omega(n)$ simultaneously**. We are missing a multi-depth operator factorization (such as an exact Cholesky / Baxter–Wiener–Hopf factorization of the truncated operator $\sum_{q \le Q} Y_\varepsilon(q) f_q^{\text{ec}}$) that pairs depth $\omega(n) = k$ directly against depth $\omega(n) = k + 1$ instead of bounding one prime layer at a time.

---

### 2. A Coupling Between High-Scale Spectral Dilations ($p, q \sim Q$) and the Additive Successor $n \mapsto n + 1$ (Breaking Beurling Invariance)
- **What we have now:**
  Our library is split into two halves that do not talk to each other at high scales:
  1. **Spectral half (Modules 60, 63, 69, 70, 72, 73, 74):** Uses the Hilbert-space prime-insertion law $f_{pr} = \sqrt{p}\,D_{1/p} f_r - f_r$ on $L^2((1, \infty), dx/x^2)$. Notice that this law uses **only** multiplicative factorization and continuous scaling $x \mapsto x/p$. It holds verbatim for Beurling generalized number systems (`RHTower/BeurlingRegularIntegersOffLineZeros.lean`), where off-line zeros $\operatorname{Re}(\rho) = \beta > 1/2$ **do exist** and $\mathcal{V}_\varepsilon(Q)$ **diverges like $Q^{2\beta - 1 - 2\varepsilon}$**!
  2. **Physical Bézout half (Modules 1–68):** Uses the genuine additive structure of $\mathbb{N}$ ($d_1 \mid (n+1),\, d_2 \mid n \implies \gcd(d_1, d_2) = 1$), which is false for Beurling systems—**but only at fixed finite lags $h \in \{1, \dots, L\}$**, which only annihilate small divisors $d \le L + 1$ and leave all divisors $d > L + 1$ untouched.
- **The missing tool:**
  A theorem that injects the **additive Bézout reciprocity of $\mathbb{N}$** directly into the **high-scale dilation profile $\Phi_r(p/q)$ for large primes $p, q$**. Specifically, $\Phi_r(p/q)$ is an integral of step functions jumping at multiples of $p$ and $q$; the distance between a jump of $pr$ and a jump of $qr$ is governed by the linear Diophantine equation $a p - b q = h$, which is the additive structure of $\mathbb{N}$ that Beurling systems lack. Right now, we treat $\Phi_r(c)$ only as an abstract continuous $L^2$ inner product $\langle f_r, D_c f_r \rangle$, throwing away the Diophantine spacing of its jumps.

---

### 3. Single-Modulus Bilinear Dispersion Beyond the Nyquist Barrier ($\theta = 2$ vs. $\theta = 1$)
- **What we have now:**
  By Cauchy–Schwarz and Montgomery–Vaughan / Large Sieve (`docs/reports/walls/wall1.md`), general $L^2$ orthogonality of Dirichlet polynomials or step functions of length $Q$ only controls the off-diagonal terms up to polynomial length $Q \ll T$ ($\theta = 1$). In our problem, the effective frequency height is $T \sim Q^{1/2}$ ($\theta = 2$), which is why the trivial off-diagonal bound loses a factor of $Q^{1 - 2\varepsilon}$ and only converges for $\varepsilon \ge 1/2$.
- **The missing tool:**
  In analytic number theory, crossing $\theta = 1$ for divisor/sawtooth sums requires **Kloosterman / Voronoi summation and bilinear (Type I / Type II) dispersion** using the fractional-part reciprocity
  $$\left\{\frac{N}{pq}\right\} \longleftrightarrow \frac{\bar{p}}{q} + \frac{\bar{q}}{p} \pmod 1$$
  to convert correlations between moduli $p$ and $q$ into exponential sums with modular inverses $\bar{p} \pmod q$. Classical dispersion theorems only achieve this after averaging over a family of characters or moduli; we are missing an **internal bilinear dispersion estimate** on the sawtooth/Ramanujan bilinear form $\sum_{p \sim P} \sum_{q \sim Q} a_p b_q \mathcal{G}^{\text{ec}}(p, q)$ that harvests cancellation from the modular inverse $\bar{p} \pmod q$ across prime pairs $(p, q)$ without an external character average.

---

### 4. A Coercive Contraction Inequality on $M_T^{\text{int}}(\varepsilon)$ (Instead of Summation-by-Parts Identities)
- **What we have now:**
  In physical space, we decomposed
  $$E_T(\varepsilon) = D_T^{\text{act}}(\varepsilon) + 2 P_T^{\text{pred}}(\varepsilon) + 2 M_T^{\text{int}}(\varepsilon).$$
  When we tried to bound $2 M_T^{\text{int}}(\varepsilon)$ in Module 67 using discrete summation by parts along $n$, we recovered $+1 \cdot E_T(\varepsilon) - \operatorname{Grad}_T(\varepsilon) - 2\,\operatorname{Local}_T(\varepsilon)$, so $E_T(\varepsilon)$ cancelled with coefficient $1 - 1 = 0$.
- **Why this failed:**
  Discrete summation by parts along $n$ is just the product rule $\Delta(I(n)^2) = 2 I(n)\Delta I(n) + (\Delta I(n))^2$ run in reverse; it is an **exact algebraic identity**, so it can never produce a coefficient $\alpha < 1$ in front of $E_T(\varepsilon)$.
- **The missing tool:**
  To bound $E_T(\varepsilon)$ from $E_T = D_T^{\text{act}} + 2 P_T^{\text{pred}} + 2 M_T^{\text{int}}$, we need an inequality of the form
  $$2 M_T^{\text{int}}(\varepsilon) + 2\,\operatorname{pmInteriorLogCounterterm}(\varepsilon)\,H_T^{\text{comp}} \le (1 - \delta)\,E_T(\varepsilon) + C(\varepsilon) \qquad (\delta > 0)$$
  (or $\delta = 1$, a direct $O_\varepsilon(1)$ upper bound on the renormalized martingale). The actual source definition is
  $$M_T^{\text{int}}(\varepsilon)=\sum_{n=1}^{T-1} I_\varepsilon(n)\,a_\varepsilon(n+1)\left(\frac1{n+1}-\frac1{T+1}\right),$$
  where $a_\varepsilon=\operatorname{pmPowerDampedCenteredDivisorCoeff}$ and
  $$a_\varepsilon(n+1)=\Delta I_\varepsilon(n)+\Delta^2 S_\varepsilon(n),\qquad S_\varepsilon=\operatorname{pmActiveSawtoothComponent}.$$
  Replacing the compensated reciprocal weight by $H_T-H_n$, or dropping $\Delta^2S_\varepsilon$, changes the target. One attack is conditional cancellation of the interior sawtooth along $n\equiv-1\pmod d$, with errors controlled after summing the signed modulus pairs. The finite-cutoff interior also differs from $I_\varepsilon$ by the explicit affine correction in `pmBezoutInteriorPrefix_sub_bezoutInteriorSawtoothSum_eq_affine`.
- **Verified conditional-centering tool; contraction remains open:**
  [`InteriorJumpOrbitCenteringAndCompensatedBounds.lean`](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/InteriorJumpOrbitCenteringAndCompensatedBounds.lean) proves that the negative centered sawtooth at interior modulus $e$, with both endpoint residues deleted, has exact conditional mean
  $$\gamma(d,e)=\begin{cases}0,&\gcd(d,e)=1,\\[2pt]\dfrac{e-\gcd(d,e)}{2e^2},&\gcd(d,e)>1.\end{cases}$$
  Zero mean holds exactly when the moduli are coprime or $e\mid d$. Subtracting $\gamma(d,e)$ gives a compensated finite-progression bound $e/(d\gcd(d,e))$, uniform in the observation horizon. The theorem applies to the existing finite-cutoff interior sum with arbitrary signed weights. This isolates proper shared factors of composite interior moduli as the resonant contribution. The remaining error bound is not uniform after summing all moduli, so it does not establish the displayed strict contraction. [Proof and audit](../../drafts/pipeline/3-formalized/bvi-interior-jump-orbit-centering-and-compensated-bounds-2026-10-18.md).
