# Exclusion of the Critical State (ECS)

Namespace `GaloisForLFunctions.ExclusionOfTheCriticalState`; umbrella `ExclusionOfTheCriticalState.lean`.

## 1. Motivation

Weil's form, restricted to real tests on the half-line $u<0$ and confined by the weight $e^{-8u}$, has a
**critical state** exactly when RH fails: either RH holds, or the global window threshold $W_0$ is finite
and a unit profile $F$ attains the confined form's zero at ratio $W_0$
(`riemannHypothesis_or_exists_criticalHalfLineGroundState`, AHD). The state is unique up to sign,
solves the weak Euler–Lagrange equation on the actual energy domain, and its Laplace transform has no
zero on $\operatorname{Re} w\ge0$. RH is the statement that **one explicit function does not exist**.

ECS turns this into a field. It writes the state's equation in coordinates where the arithmetic is
visible, makes every exact property of the state a theorem, and looks for the property that contradicts
the arithmetic of $\zeta$. Each result is a reduction "no function with properties $P_1,\dots,P_k$
exists $\Rightarrow$ RH" with a growing list of properties. At the state every relation is an identity,
so nothing is lost between stages.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Energy domain $\mathcal H$ | `CriticalHalfLineEnergyDomain` (AHD) | $F$ on $u<0$; $F,F^2,F^2e^{-8u}$ integrable; finite Gamma energy |
| Transform | `negativeHalfLineLaplace (cx F)` | $\mathcal LF(w)=\int F(u)e^{wu}du$ |
| Bare / full / mixed form | `bareHalfLineEnergy`, `bareMixedEnergy`, `criticalHalfLineFullEnergy`, `criticalHalfLineMixedEnergy` | Weil's form; $Q_R=B+a(R)W_8$, $W_8=\int F^2e^{-8u}$ |
| State | `IsCriticalHalfLineGroundState` (AHD) | the unit null direction of $Q_{W_0}$ |
| Probes | `probe p` | $e_p(u)=e^{pu}\mathbf 1_{u<0}$; in $\mathcal H$ for $p>4$ |
| Probe symbol | `probeSymbol` | $D(p)=\xi'/\xi(\tfrac12+p)$ written with poles, digamma and $\Lambda$ |
| Holomorphic state equation | `stateEquation`, `stateGamma`, `stateTail` | $\alpha\mathcal LF(p-8)+\Gamma F(p)+\mathcal LF(p)\tfrac{\zeta'}{\zeta}(\tfrac12+p)-TF(p)+\text{pole}(p)$ |
| Cleared equation | `stateEquationCleared` | the same with $\zeta(\tfrac12+p)$ multiplied through |
| Pole-free remainder | `stateRemainder` | the equation minus $\alpha\mathcal LF(p-8)$, written with $(s-1)\zeta(s)$ and a divided difference at $\tfrac12$ |
| Tail measure | `tailMeasure` | $F(-v)\,dv$ on $v>T$, for Landau's theorem |
| Lévy pairing | `levyGamma`, `levyKernel`, `levyTail` | $\Gamma F(p)=2\theta'(0)\mathcal LF(p)+\int_0^\infty\omega(x)\big[\mathcal LF(p)(2-e^{-px})-e^{px}\!\int_{u<-x}Fe^{pu}\big]dx$ |
| Lévy symbol, heads | `levySymbol`, `levyHead`, `levyHeadTerm` | $g(p)=\int\omega(x)(2-e^{-px}-e^{px})dx$; $H_x(p)=\int_{-x}^0Fe^{pu}$; $JF(p)=\int\omega(x)e^{px}H_x(p)dx$ |
| Prime heads | `primeHead` | $\hat SF(p)=\sum\Lambda(n)n^{p-1/2}H_{\log n}(p)$ |
| Wall tail, prime-pole balance | `archimedeanWallTail`, `wallPrimeBalance`, `wallPrimeWaveDatumLp` | $J_{\ge1}F(p)=\sum_{k\ge0}\tfrac{\mathcal LF(2(k+1)+1/2)}{2(k+1)+1/2-p}$; $\Phi_F(p)=\hat SF(p)+\tfrac{\mathcal LF(-1/2)}{p+1/2}$ and its $L^2(0,\infty)$ Hardy datum |
| Beyond-the-wall continuation | `HasBeyondTheWallPrimeContinuation`, `ZetaBeyondTheWallPrimeContinuation`, `PurePrimeHeadContinuation`, `ModelBeyondTheWallPrimeContinuation` | holomorphic continuation of $\Phi_F$ (or $\hat SG$ on $\mathcal LG(-\tfrac12)=0$, or $\Phi_c(F,\cdot)$) from $\operatorname{Re}p<-\tfrac12$ to $\operatorname{Re}p<0$ |
| Three remainders | `levyRemainder`, `stripRemainder`, `leftRemainder`, `globalRemainder` | the remainder right of, on, and left of $\operatorname{Re}p=-\tfrac12$ |
| Continuations | `stateContinuation`, `levyContinuation`, `stateMeromorphic` | $-R(w+8)/a$ on $\operatorname{Re}w>-8$, $>-\tfrac{17}2$, and on $\mathbb C$ |
| Entire state product | `stateXiProduct` | $E(w)=\xi(w+\tfrac{17}2)\mathcal LF(w)$, extended across the shifted zeros |
| Averaged state | `averagedState`, `averageSymbol` | $A(t)$: exponential averages of $F(-\cdot)$ at the rates $9,\dots,12$; $\int_0^\infty A(t)e^{-zt}dt=\mathcal LF(z)/((z+9)(z+10)(z+11)(z+12))$ |
| Heat test, heat kernel | `stateHeatSymbol`, `stateHeatKernel` | $e^{\varepsilon p^2-pT}$; $k_\varepsilon(x)=(4\pi\varepsilon)^{-1/2}e^{-x^2/4\varepsilon}$ |
| Heated state | `heatedState` | $\int k_\varepsilon(u-T)e^{-8u}F(u)\,du$ |
| Profile beyond the wall | `beyondWallProfile`, `heatedBeyondWall` | $F^+$ on $x>0$: archimedean head, prime heads and the two charges, with $\mathcal LF(w)=\int_0^\infty F^+(x)e^{(w+8)x}dx$ for $\operatorname{Re}w<-9$; its heat average |
| Transform of a test, pairings | `laplaceTest`, `statePairing`, `beyondWallPairing` | $\hat\psi(p)=\int\psi(u)e^{-pu}du$; $\int\psi(u)e^{-8u}F(u)\,du$; $\int_0^\infty\psi(x)F^+(x)\,dx$ |
| Correlation, tilted heat kernel | `profileCorrelation`, `tiltedHeatKernel` | $C(s)=\int p(T)q(T+s)\,dT$; $k_\varepsilon(s)e^{\lambda s}$ |
| Centred zeros, zero sum | `centredZero`, `zeroSum` | $z=\rho-\tfrac12$ with multiplicity; $ZF(p)=\sum_z\mathcal LF(z)\big(\tfrac1{p-z}-\tfrac1{1-z}\big)$ |
| Divided-difference sum | `dividedTerm`, `dividedSum` | $\Delta F(p)=\sum_z\big(\tfrac{\mathcal LF(z)-\mathcal LF(p)}{p-z}-\tfrac{\mathcal LF(z)}{1-z}-\tfrac{\mathcal LF(p)}{z}\big)$, holomorphic at the zeros |
| Defect | `explicitDefect`, `rightFormDefect`, `stripFormDefect`, `entireDefect` | $BF(1)-BF(p)+ZF(p)$ with $BF=$ `globalRemainder`, and its pole-free forms |
| Nonpositive cone | `NonpositiveUnitTest`, `confinementBound` | smooth unit half-line tests with $Q_R\le0$ |
| Regular part of $\zeta'/\zeta$ | `zetaRegularLogDeriv`, `gaugedLogDeriv` | $N(s)=\zeta'/\zeta(s)+\tfrac1{s-1}$, the logarithmic derivative of $(s-1)\zeta(s)$ |
| Forward prime-minus-pole wave | `forwardPrimeForm`, `forwardPoleWave`, `forwardPoleForm`, `primeWaveTransform`, `primeWaveHardy` | $A(v)=\sum\Lambda(n)n^{-1/2}F(v+\log n)-e^{-v/2}\int_{u>v}F(u)e^{u/2}du$, with transform $-N(\tfrac12+p)\mathcal LF(p)$; the two forms pair $A$ with $G$ |

## 3. Language

- **Probe identity**: the weak equation tested on $e_p$. **Prime coordinates**: the probe identity with
  the prime part split into the Euler term $\mathcal LF(p)\sum\Lambda(n)n^{-1/2-p}$ and the prime tail
  $TF(p)=\sum\Lambda(n)n^{p-1/2}\int_{u<-\log n}F(u)e^{pu}du$.
- **Seen zero**: a zero $z=\rho-\tfrac12$ with $\mathcal LF(z)\neq0$; all zeros with $\operatorname{Re}z\ge0$ are seen.
- **Decay exponent** $b^*=\sup\{b:\int F^2e^{-bu}<\infty\}$; **holomorphy abscissa** $\kappa^*$ of $\mathcal LF$. By the decay law $b^*=17-2\Theta$ and $\kappa^*=\Theta-\tfrac{17}2$.
- **Critical ratio** of $Q_R$: a ratio where a null direction appears; **index** at $R$: the largest
  orthonormal family in the nonpositive cone.
- **Soft property**: holds for the states of every symmetric configuration. **Arithmetic property**:
  fails on a named model (prime-two deformations, positive Euler twins).

## 4. Mechanisms

1. **Probe calculus.** On probes each part of Weil's form is a function of $p,q$: pole part
   $(\frac1{p\pm1/2},\frac1{q\pm1/2})/(p+q)$, prime part $-(\zeta'/\zeta(\tfrac12+p)+\zeta'/\zeta(\tfrac12+q))/(p+q)$,
   Gamma part the Poisson integral of $\operatorname{Re}\psi(\tfrac14+\tfrac{ir}2)$. Their sum is the Carathéodory
   kernel $\frac{D(p)+D(q)}{p+q}$, and the two-channel resolvent identity makes it the zero sum: the
   explicit formula holds on the probe span.
2. **Prime coordinates suffice.** The probe identity is a closed formula in transforms of $F$; each term
   continues holomorphically in $p$ (Laplace transform from square moments, Gamma pairing from the
   Gamma energy, prime tail from the confinement mass). Replacing $\sum\Lambda(n)n^{-1/2-p}$ by
   $-\zeta'/\zeta(\tfrac12+p)$ continues the whole equation; no zero-side explicit formula on $\mathcal H$ is needed.
3. **Residue transport.** After clearing $\zeta(\tfrac12+p)$ the equation reads
   $\zeta(\tfrac12+p)A(p)+\mathcal LF(p)\zeta'(\tfrac12+p)=0$. At a zero $\rho$ the residue of $\zeta'/\zeta$ forces
   $m_\rho\,\mathcal LF(\rho-\tfrac12)=0$ unless $A$ is singular at $\rho-\tfrac12$, i.e. unless $\mathcal LF$ is
   singular at $\rho-\tfrac{17}2$. The pole of $\zeta'/\zeta$ is transported eight units to the left.
4. **Landau.** A one-signed tail makes the real point of the abscissa singular. The remainder, written
   with $(s-1)\zeta(s)$ and the divided difference of $\mathcal LF$ at $\tfrac12$, is holomorphic near the real
   segment because $\zeta$ has no real zero in $(\tfrac12,1)$; so the abscissa is at most $-8$.
5. **Confinement compactness.** On the nonpositive cone, $Q_R=Q_{2R}+\tfrac{a(R)}2W_8$ and $\lambda(2R)$ bound
   $W_8$; bounded confinement and energy are $L^2$-compact, and orthonormal families are $\sqrt2$-separated.
6. **Lévy continuation.** Polarizing the Lévy–Khintchine form of the Gamma energy and evaluating on a probe
   gives a Gamma pairing whose density $\omega(x)\sim e^{-x/2}$ makes it holomorphic on $\operatorname{Re}p>-\tfrac12$;
   the continuation crosses the critical line without deforming a contour.
7. **The functional equation in Lévy form.** On the imaginary axis $2\theta'(0)+g(ir)=2\theta'(r)$ and
   $\zeta'/\zeta(\tfrac12+ir)+\zeta'/\zeta(\tfrac12-ir)=-2\theta'(r)$; the identity theorem, applied to the product cleared of
   $\zeta(\tfrac12\pm p)$, gives $2\theta'(0)+g(p)=-\big(\zeta'/\zeta(\tfrac12+p)+\zeta'/\zeta(\tfrac12-p)\big)$ on $|\operatorname{Re}p|<\tfrac12$. With
   $\int_{u<-x}=\mathcal LF-H_x$: $\Gamma F(p)=-\mathcal LF(p)\big(\zeta'/\zeta(\tfrac12+p)+\zeta'/\zeta(\tfrac12-p)\big)+JF(p)$.
8. **Euler cancellation left of the strip.** For $\operatorname{Re}p<-\tfrac12$ the prime tail is
   $-\mathcal LF(p)\zeta'/\zeta(\tfrac12-p)-\hat SF(p)$ (Dirichlet series of $\Lambda$ at $\tfrac12-p$). Its Euler part cancels the reflected
   Euler term of the Gamma pairing exactly, and the remainder is $JF+\hat SF+\mathcal LF(\tfrac12)/(p-\tfrac12)+\mathcal LF(-\tfrac12)/(p+\tfrac12)$:
   left of the strip the state is its head term, its prime heads and its two charges.
9. **Pole removal.** $ZF(p)=\Delta F(p)+\mathcal LF(p)\,\xi'/\xi(\tfrac12+p)$, and $\Delta F$ converges absolutely and is
   holomorphic on $\operatorname{Re}p>-2$, zeros included. With $(s-1)\zeta(s)=2\xi(s)/(s\Gamma_{\mathbb R}(s))$ the Euler term of the
   remainder is $\mathcal LF\cdot(\xi'/\xi-1/s-\Gamma_{\mathbb R}'/\Gamma_{\mathbb R})$, so the defect $BF(1)-BF+ZF$ has no pole: one
   pole-free form right of $\operatorname{Re}p=-\tfrac12$, one on $-2<\operatorname{Re}p<\tfrac12$ with the reflected Euler factor.
10. **Liouville on the defect.** The Lévy pairing and the regular part grow linearly on $\operatorname{Re}p\ge0$, heads
   and tails are bounded on their half-planes, $\Gamma_{\mathbb R}'/\Gamma_{\mathbb R}$ is linear, both sums are quadratic. The glued
   defect is entire of order $O(|p|^2)$, vanishes at $1$ and is $o(|p|)$ along the negative axis; its
   divided difference at $1$ is zero. No bound for $\zeta'/\zeta$ inside the strip is used.
   The cleared state product $E$ is entire. At a seen zero $z=\rho-\tfrac12$ of multiplicity $m$,
   $E$ has order exactly $m-1$ at $z-8$: in $\xi R+\mathcal LF\,\xi'$, only the derivative term contributes
   to the leading jet. Conversely, $E$ has order at least $m$ there exactly when $\mathcal LF(z)=0$.
11. **Bounds off the zeros and the averaged line shift.** At distance $\delta$ from the zeros
   $|ZF(p)|\le C(1+|p|)(1+|p|/\delta)$, so the continuation is $O(|w|^2)$ on every vertical line off the
   pole strip. An exponential average of the state at four rates divides the transform by a quartic;
   the inversion line then moves from $\operatorname{Re}w=1$ to $\operatorname{Re}w=\kappa'-8$ for every $\kappa'$ above the
   real parts of the centred zeros. The raw transform does not decay on these lines, so the unaveraged
   $L^2$ law needs more than the width of the zero strip.
12. **Two lines weigh the zero values.** For entire $H$ of fourth-order decay on $a\le\operatorname{Re}p\le b$,
   $a\le-1$, $1\le b$: $\sum_z\mathcal LF(z)H(z)=\frac1{2\pi}\big(\int_{\operatorname{Re}p=b}H\,BF-\int_{\operatorname{Re}p=a}H\,BF\big)$. The zero
   sum integrates term by term and the constant of the explicit formula drops out. For the state the
   right line carries $\mathcal LF$ and the left line its continuation. With $H=e^{\varepsilon p^2-pT}$ each line
   integral is a heat average (Fubini and one Gaussian integral): the series $\sum_z\mathcal LF(z)e^{-zu}$ is
   $-a\,e^{-8u}F(u)$ left of the wall and $a\,F^+(u)$ beyond it. With $H=\hat\psi$, $\hat\psi(p)=\int\psi(u)e^{-pu}du$ for a
   smooth test of compact support, Fourier inversion on each line replaces the Gaussian integral and the
   identity holds against $\psi$ itself, with no singular part at the wall; left of the wall the weak
   equation turns the pairing with $e^{-8u}F$ into Weil's form.
13. **Correlation limit.** $\mathcal LG(-z)=\int G(T)e^{-zT}dT$, so $\sum_z\mathcal LF(z)\mathcal LG(-z)e^{\varepsilon z^2}$ is the integral
   of $G(T)$ against the heated zero series. With the exponential weights moved to the profiles, each
   term is $\int\kappa_\varepsilon(s)C(s)\,ds$ for a tilted heat kernel and the correlation
   $C(s)=\int p(T)q(T+s)\,dT$ of two square-integrable profiles; $C$ is continuous and bounded, and the
   limit is $C(0)$. The term beyond the wall vanishes in the limit because its profiles have disjoint
   supports. No smoothness of $G$ and no bound for the zero values is used.
14. **Agmon localization.** A bounded Lipschitz multiplier maps $\mathcal H$ to itself: a Lipschitz jump
   is paid near the origin of the Lévy density, a bounded one far out. For the truncated tilt
   $\varphi=e^{-c\max(u,-N)}$ the jump of $\varphi F$ squared is the jump of $F$ times the jump of $\varphi^2F$
   plus a commutator $F(u)F(u+x)(\varphi(u)-\varphi(u+x))^2$; the weak equation tested on $\varphi^2F$ bounds the
   first term uniformly in $N$, and Fatou gives $e^{-cu}F\in\mathcal H$ for $0\le c\le1$.
15. **Sampling at unit depth.** A profile of $\mathcal H$ lives on $u<0$, so $\mathcal LH(d+i\gamma)$ is the Poisson
   average of its boundary values. Jensen's inequality and the unit-window count
   $\sum_\rho(1+(t-\gamma_\rho)^2)^{-1}\le8(C_0+\log(|t|+4))$ give
   $\sum_\rho|\mathcal LH(w_\rho)|^2\lesssim\int\log(|t|+4)\,|\mathcal LH(it)|^2dt$ for points at depth
   $\tfrac12\le\operatorname{Re}w_\rho\le\tfrac32$ and heights $\pm\gamma_\rho$: the Gamma energy is the norm that
   controls the values at the zeros. Applied to the unit tilt, the values $\mathcal LF(\pm z)$ of the state
   are square-summable.
16. **Removal of the summation method.** With square-summable values the Gaussian-regularised sums
   converge dominatedly: $\sum_z\mathcal LF(z)\mathcal LG(-z)=B(F,G)$ absolutely for tilt-regular $G$, and
   $\sum_z\mathcal LF(z)/(p-z)$ converges absolutely and tends to $0$ as $p\to-\infty$. The subtraction point of
   $(\star)$ moves to $-\infty$ and $(\star)$ becomes a one-point identity.
17. **Self-duality against an analytic weight.** For a finite Cauchy sum $C=\sum c_z/(p-z)$ and
   $\Lambda(p)=\log(p-\sigma+4)$ on $\operatorname{Re}p\ge\sigma$:
   $X=\int|C|^2\operatorname{Re}(1/\Lambda)=\operatorname{Re}\int\bar C\,(C/\Lambda)$. Each term of $\bar C$ is the Cauchy kernel
   of a reflected zero $2\sigma-\bar z$, the values of $C/\Lambda$ there are Poisson averages, and the
   unit-window count is absorbed by $|\Lambda|^{-2}\log\lesssim\operatorname{Re}(1/\Lambda)$; so
   $X^2\lesssim(\sum|c_z|^2)X$. No separation of the zeros is used; the logarithm is their unit-window count.
18. **Sublogarithmic regular part.** $N=\zeta'/\zeta+1/(s-1)$ is $O(\log|t|)$ on every half-plane right of
   the zeros (partial fractions and the unit-window count) and bounded right of $\operatorname{Re}s=1$.
   Phragmén–Lindelöf with the gauge $e^{(s-iT)^2-c(b-s)}$, $c=\log\log|T|/(b-a)$, interpolates:
   $|N(s_0+iT)|\lesssim\log^{(b-s_0)/(b-a)}|T|$. If the zeros have $\operatorname{Re}\rho\le\tfrac12+\kappa$, then
   $|N|^2\lesssim\log$ on $\operatorname{Re}s>\tfrac34+\tfrac\kappa2$.
19. **Forward cancellation and the Agmon bound past the barrier.** Against the pointwise barrier
   $e^{\beta u}$ the forward prime sum costs $e^{-(\beta+1/2)u}$, which confinement absorbs only for
   $\beta<\tfrac{15}2$. The forward prime sum and the forward half of the pole term carry the same pole
   $1/(p-\tfrac12)$; their difference has transform $-N(\tfrac12+p)\mathcal LF(p)$, a Hardy function on
   $\operatorname{Re}p>\sigma$ (Jensen for the Poisson average with the regulator $1/(1+\varepsilon(p-\sigma))$,
   Paley–Wiener, polarized Plancherel on $\operatorname{Re}p=1$). Pairing it with $G$ costs
   $\lVert e^{-\sigma v}G\rVert_2$ times the mass $M$ of $N\mathcal LF$ on $\operatorname{Re}p=\sigma$; $M$ is finite for
   $\sigma>\tfrac14+\tfrac\kappa2$, where the Gamma energy pays the logarithm of $|N|^2$. In the weak equation
   tested on $\psi_NF$, $\psi_N=e^{-2c\max(u,-N)}$, $c=4-\sigma$, the forward term is absorbed because
   $\psi_Ne^{-2\sigma v}\le e^{-8v}$; the commutator and the backward halves are moments below the barrier.
   So $\int\psi_NF^2e^{-8u}$ is bounded in $N$ and $b^*\ge\tfrac{31}2-\kappa$. The bound uses only the mass of the wave on
   the line and the moment $\int F^2e^{-(16-4\sigma)u}$.
20. **Logarithmic energies interpolate between vertical lines.** For a Hardy function $G$ of the right
   half-plane, $E_k(\sigma)=\int\log^k(|t|+4)|G(\sigma+it)|^2dt$ is finite on convex combinations of
   $(\sigma_0,k_0)$, $(\sigma_1,k_1)$, $0\le k_j\le2$. The window $(w+2+iT)^{-2}$ keeps the Hardy class and
   localizes at height $-T$; for the windowed function Plancherel on a line is $\int_0^\infty|h(x)|^2e^{-2\sigma x}dx$, $h$ its Paley–Wiener datum,
   log-convex in $\sigma$ by Hölder; integrating over $T$ against $\log^k(|T|+4)$ (Hölder in $T$, Tonelli)
   restores the weight, since $\int\log^k(|T|+4)\,|t+T+i(\sigma+2)|^{-4}dT\asymp\log^k(|t|+4)$.
21. **The state equation on the zero-free strip.** If $\int F^2e^{-bu}<\infty$, the continuation equals the
   transform on $\operatorname{Re}w>\max(\kappa-8,-\tfrac b2)$ (identity theorem), and on
   $\kappa<\operatorname{Re}p<\tfrac12$, $16-b<2\operatorname{Re}p$:
   $\mathcal LF(p)\,A(p)=-a\,\mathcal LF(p-8)-J_G(p-2)+T_F(p)-\mathcal LF(-\tfrac12)/(p+\tfrac12)$ with
   $A=2\theta'(0)+g+N(\tfrac12+\cdot)-1/(\cdot-\tfrac12)$, $G=e^{2\min(u,0)}F$ and $T_F$ the prime tail: the first
   mode of the head term cancels the pole of the difference quotient at $\tfrac12$. Under the Lévy measure
   $2-2\cosh(sx)\cos(tx)\ge(2-2\cos tx)+(2-2\cosh sx)$, so
   $\operatorname{Re}(2\theta'(0)+g(s+it))\ge2\theta'(t)+g(s)\ge\log(|t|+4)-C$; $N$ is sublogarithmic; hence
   $|A(s+it)|\ge\tfrac12\log(|t|+4)-K$. Every term on the right is square integrable on the line (Plancherel
   under the decay, the head term as a Hardy function, the prime tail by Cauchy–Schwarz over $n$ and
   Plancherel for the truncated profiles). So $E_2(s)<\infty$ for $b>16-2s$: two logarithms on the lines of
   decay, one more than the Gamma energy.
22. **Descent of the abscissa of decay.** $P(\sigma)$: $\int F^2e^{-bu}<\infty$ for all $b<16-2\sigma$. Given
   $P(\sigma)$ and $\kappa<s<\sigma<\tfrac12$: two logarithms on a line slightly right of $\sigma$, one on
   $\operatorname{Re}p=0$, hence $1+s/\sigma^+$ on $\operatorname{Re}p=s$ by interpolation, against the cost
   $2\theta\to2(\tfrac12-s)/(\tfrac12-\kappa)$ of $|N|^2$. If $(\tfrac12+\kappa)\sigma<s(\tfrac12-\kappa+2\sigma)$ the mass of
   the wave on $\operatorname{Re}p=s$ is finite, and if $\sigma<2s$ the moment $16-4s$ lies below $16-2\sigma$; the Agmon
   bound gives $P(s)$. Admissible $s<\sigma$ exist whenever $\sigma>\kappa$, so the infimum of the abscissae with
   $P(\sigma)$ is $\kappa$: $P(\kappa)$ holds, and with the ruler the decay rate is $17-2\Theta$.
23. **Pole of the moments.** Let $b_\rho=17-2\operatorname{Re}\rho$. If $M(b_\rho-\eta)=\int F^2e^{-(b_\rho-\eta)u}<\infty$, the
   cleared state equation holds at $p=\rho-\tfrac12+\eta$, on the edge of the half-plane of convergence:
   $a\mathcal LF(p-8)=-\mathcal LF(p)\tfrac{\zeta'}{\zeta}(\tfrac12+p)-(\Gamma F-TF+\text{pole})(p)$. Times $\eta$ the right side
   tends to $-m_\rho\mathcal LF(\rho-\tfrac12)\neq0$; on the left Cauchy–Schwarz gives $\eta\lvert\mathcal LF(p-8)\rvert^2\le M(b_\rho-\eta)$.
   So $\eta M(b_\rho-\eta)$ stays above the squared residue of $\mathcal LF$ at the transported zero.
24. **Agmon in the energy norm.** For $\varphi=e^{-c\max(u,-N)}$ the jump energy of $\varphi F$ is the Gamma pairing
   of $F$ with $\varphi^2F$ up to a commutator bounded by the moment $4c$. The weak equation against $\varphi^2F$
   turns the pairing into prime minus pole minus the confinement term $a\int\varphi^2F^2e^{-8u}$, which is dropped.
   The forward halves are the wave on a line $\operatorname{Re}p=s$ just right of the zeros against
   $\int F^2e^{-(4c+2s)u}$. All moments lie below the decay rate exactly when $c<4-\kappa$; Fatou in the lag
   gives $e^{-cu}F\in\mathcal H$. The exponential field of a tilt is the moment $8+2c$, so the pole of the
   moments makes the threshold $\tfrac92-\Theta$ sharp. A tilt whose unit tilt lies in $\mathcal H$ is an
   admissible test with square-summable zero values: the weak equation against it reads
   $\sum_z\mathcal LF(z)\mathcal LF(-z-c)=-a\int F^2e^{-(8+c)u}$.
25. **Translation defect.** For $k\ge0$ the translate $\tau_kF(u)=F(u+k)$ lies in $\mathcal H$ and its zero values
   are $e^{-zk}\mathcal LF(z)$. The heated zero series integrated against $G(T-k)$ gives
   $W(\tau_kF,G)=a\bigl(\int_0^kF^+(x)G(x-k)\,dx-\int e^{-8u}F(u)G(u-k)\,du\bigr)$ for every $G\in\mathcal H$: on the
   collar $-k<u<0$ the translated state fails the weak equation by the prime side. The state is orthogonal to
   $\tau_kF$ for the full form, so $G=F$ leaves the wall law
   $\int_0^kF^+(x)F(x-k)\,dx=-(1-e^{-8k})\int F(u)F(u+k)e^{-8u}du$, with no prime sum.
26. **Logarithmic singularity at the wall.** The collar kernel is $\kappa(t)=-\tfrac1{2t}+O(e^{t/2})$ and the prime
   wave is bounded near the wall, so $aF^+=-\tfrac12\Phi+O(1)$ on $(0,1)$ with the Stieltjes potential
   $\Phi(x)=\int_{v>0}F(-v)\,\frac{dv}{x+v}$; on $0<x\le k$, $\Phi(x)$ is the logarithmic moment
   $L(k)=\int_{v>k}F(-v)\,\frac{dv}v$ up to $C+4C(k/x)^{1/4}$. The wall law becomes $\mu(k)L(k)\to16aM$ for the terminal
   mean $\mu(k)=k^{-1}\int_{-k}^0F$ and $M=\int F^2e^{-8u}$. Fubini gives $L=R-\mu$ with
   $R(k)=\int_{h>k}\bigl(\int_{-h}^0F\bigr)h^{-2}dh$ and $R'=-\mu/k$, so $(R^2+2c\log k)'=-2(R\mu-c)/k$ has a sign near
   $0^+$ for every $c\ne16aM$, and $R^2\sim32aM\log(1/k)$.

## 5. Questions

| # | Question | Status |
|---|---|---|
| Q1 | Probe kernel $B(e_p,e_q)=\frac{D(p)+D(q)}{p+q}$ and its zero side | answered (Lean) |
| Q2 | Zero side of $B$ on all of $\mathcal H$; zero-coordinate form $(\star)$ | answered (Lean): for every pair of profiles of $\mathcal H$ the zero pairing with Gaussian summation is Weil's form, $\lim_{\varepsilon\to0^+}\sum_z\mathcal LF(z)\mathcal LG(-z)e^{\varepsilon z^2}=W(F,G)$ (`tendsto_heatedZeroPairing`); without summation it converges absolutely when both unit tilts lie in $\mathcal H$ (`hasSum_bareMixedEnergy_of_unitTilts`), in particular at the state; $(\star)$ is a one-point identity with square-summable zero values. For a general profile the unsummed series needs one subtraction (Traps) |
| Q3 | State equation, continuation, residues | answered (Lean): global meromorphic continuation, exact residues and uniform left decay |
| Q4 | Decay law | answered (Lean): for $\kappa\ge0$, every centred zero has $\operatorname{Re}z\le\kappa$ iff $\int F^2e^{-bu}<\infty$ for every $b<16-2\kappa$; the decay rate is $b^*=17-2\Theta$, $\Theta$ the supremum of the real parts of the zeros; unconditionally $\int F^2e^{-bu}<\infty$ for $b<15+\tfrac{3001}{12000}$. Also in Lean: left Hardy bounds, averaged/heated decay, and the transform side: $\mathcal LF$ converges exactly on $\operatorname{Re}w>\Theta-\tfrac{17}2$, with $(\star)$ at every point and Plancherel on every line. At the exponent $b_\rho=17-2\operatorname{Re}\rho$ of every zero the moment is infinite, with $\liminf_{\eta\to0^+}\eta\int F^2e^{-(b_\rho-\eta)u}\ge(m_\rho\lvert\mathcal LF(\rho-\tfrac12)\rvert/a)^2$; hence a finite moment at $b$ puts the zeros in $\operatorname{Re}\rho<\tfrac{17-b}2$, and the moment at $b^*$ is infinite when $\Theta$ is attained. In the energy norm: $e^{-cu}F\in\mathcal H$ for every $c<\tfrac92-\Theta$, the supremum of such tilts, with one logarithm on every line $\operatorname{Re}w>\Theta-\tfrac92$; for $c<\tfrac72-\Theta$ the moments are zero pairings, $\sum_z\mathcal LF(z)\mathcal LF(-z-c)=-a\int F^2e^{-(8+c)u}$. Open: the endpoint $b=b^*$ when $\Theta$ is not attained, and pointwise decay |
| Q5 | Sign law | answered (Lean): one sign on no ray |
| Q6 | Index law | answered (Lean): finite index at every ratio; some confined Gram matrix has $n$ negative squares iff $\zeta$ has at least $n$ zeros right of the line (`confinedIndex_law`); the index is bounded over all ratios iff finitely many zeros lie off the line (`confinedIndexBounded_tfae`); under a finite layer the critical ladder has one rung per right zero (`criticalLadder_iff_rightZeros`). Open: the growth of the index in the ratio when infinitely many zeros lie right of the line |
| Q7 | Rigidity: no state for $\zeta$ | open; equivalent to RH. Restricted to a finite off-line layer it is B13 in six equivalent forms (`finiteLayer_ecs_b13_tfae`) |
| Q8 | The arithmetic property that excludes the state | criterion and model separation proved (Lean): beyond-the-wall prime-pole continuation; proof for $\zeta$ open |
| Q9 | Wall, collar, charges $\mathcal LF(\pm\tfrac12)$ | partial (Lean): vanishing average wall mass, uniform right $o(1/\sigma)$ decay and charge cancellation; $F^+$ in prime form almost everywhere (`beyondWallProfile_primeForm`) and the Abel-mean form of the heads left of the strip ([Wall/](Wall/TheWallSeenFromTheLeft.lean)); coercivity of the collar and softness of its weak equation beyond $(\star)$ ([Collar/](Collar/TheCollarWeakEquationIsSoftBeyondStar.lean)); the critical ratio of the charge hyperplane ([Energy/](Energy/TheChargeHyperplaneHasItsOwnCriticalRatio.lean)). The wall law $\int_0^kF^+(x)F(x-k)\,dx=-(1-e^{-8k})\int F(u)F(u+k)e^{-8u}du$ with boundary value $-8\int F^2e^{-8u}$ as $k\to0^+$, and positive mass of $F^+$ on $(0,k)$ for small $k$ (`criticalState_beyondWallPairing_translate`, `criticalState_tendsto_beyondWallPairing_div`, `criticalState_eventually_integral_sq_beyondWallProfile_pos`). The laws of the wall: one sign $s=\pm1$ of the terminal mean $\mu(k)=k^{-1}\int_{-k}^0F$ with $\mu(k)\sqrt{\log(1/k)}\to s\sqrt{8aM}$ and $aF^+(x)/\sqrt{\log(1/x)}\to-s\sqrt{8aM}$ essentially as $x\to0^+$, $M=\int F^2e^{-8u}$ (`criticalState_wall_laws`); $s$ is the sign of the half-charge $\mathcal LF(\tfrac12)$, and $\mathcal LF(\tfrac12)\operatorname{Re}F^+(x)<0$ for almost every small $x$ (`criticalState_eventually_halfCharge_mul_terminalMass_pos`, `criticalState_exists_ae_halfCharge_mul_beyondWall_neg`); the logarithmic gain of the terminal mass is sharp. The $L^2$ modulus of continuity is exact and carried by the wall, $\log(1/k)\,k^{-1}\int(F(u)-F(u+k))^2du\to8aM$, and $\sqrt{\log(1/k)}\,F\to s\sqrt{8aM}$ in mean square on $(-k,0)$, so $F$ has the sign $s$ on a subset of $(-k,0)$ of density tending to one (`criticalState_tendsto_log_div_mul_sq_increment`, `criticalState_meanSquare_wall_law`). At every confinement ratio $R>0$ the ground state has an amplitude $\ell$ at the wall, $\sqrt{\log(1/\lvert u\rvert)}\,F(u)\to\ell$ essentially, with $\ell^2=8a(R)\int F^2e^{-8u}=-8R\lambda'(R)$ (`halfLineEnergyMinimizer_exists_wallAmplitude_sq`). Exclusion open |

**Q8 criterion.** For every $F\in\mathcal H$, require the [prime-pole balance](TheBeyondTheWallPrimeBalanceExcludesTheState.lean)
$\Phi_F(p)=\hat SF(p)+\mathcal LF(-\tfrac12)/(p+\tfrac12)$ to extend holomorphically from
$\operatorname{Re}p<-\tfrac12$ to $\operatorname{Re}p<0$ — equivalently, on the pole-neutral subspace $\mathcal LG(-\tfrac12)=0$, require the bare prime-head series $\hat SG(p)$ alone to extend holomorphically to $\operatorname{Re}p<0$. Because $J_{\ge1}F$ is holomorphic throughout $\operatorname{Re}p<\tfrac52$ and every critical state
[sees a left zero](Zeros/TheCriticalStateSeesALeftZero.lean) ($-\tfrac12<\operatorname{Re}z_0<0$, $\mathcal LF(z_0)\ne0$), which forces a pole in $\Phi_F$ at $z_0$,
the criterion excludes the state directly and is sharp at the boundary $\operatorname{Re}p=0$. It [fails unconditionally on prime-two deformations and positive passive Euler twins](Models/BeyondTheWallContinuationFailsOnTheModels.lean),
including real-axis-positive twins matching any finite $\zeta$ prefix. The heads at all proper prime powers
converge holomorphically on $\operatorname{Re}p<0$. Their only pole on the imaginary axis for a critical state
has residue $-\mathcal LF(0)/2$ at zero. Their absolute wave is $O_{F,\varepsilon}(e^{\varepsilon x})$ for
every $\varepsilon>0$. The open cancellation is between ordinary primes and the polar term.
[Proper prime powers in the prime wave](Wall/TheProperPrimePowersInThePrimeWave.lean).

## 6. Tools

**Developed.** Probe calculus (`probe`, moments, confinement pairings, Fourier transform); probe kernel
and zero side on probes; prime-coordinate state equation; holomorphy of Laplace transforms from
square or absolute moments; holomorphy of the Gamma pairing and the prime tail; the cleared equation
and the residue argument; tail measures with Landau's theorem (via the corpus abscissa calculus and
Cauchy estimates); the pole-free remainder across $p=\tfrac12$; confinement compactness of the
nonpositive cone; the Gamma pairing in Lévy form with near/far dominations of the Lévy kernel; the
prime tail on $\operatorname{Re}p>-4$ from the confinement mass; the Lévy symbol and the head term with their
dominations; the functional equation in Lévy form; prime heads and the Dirichlet series of $\Lambda$ left
of the strip; gluing of three remainders into one continuation; $\zeta\ne0$ on $\operatorname{Re}s=0$; the zero-sum
calculus (one subtraction, absolute convergence off the zeros, divided-difference sum, pole removal);
linear growth of every pairing of a profile with a probe; the pole-free forms of the defect, their
gluing and Liouville. Bounds of the pairing and of the
continuation off the zeros; the Volterra–Laplace calculus of exponential averages; the entire product
and its difference equation; two-line weighing of the zero values against entire tests; Gaussian line
integrals of Laplace integrals as heat averages; Fourier inversion on vertical lines for transforms of
smooth tests and Parseval on a line for Laplace integrals; correlations of square-integrable profiles
against tilted heat kernels (Fubini, continuity of translation in $L^2$, approximate identity).
Stability of $\mathcal H$ under bounded Lipschitz multipliers and the Agmon tilt of the state; Poisson
sampling of transforms at the zeros in the logarithmic energy norm; removal of Gaussian summation for
square-summable sequences; Poisson reproduction, Jensen's inequality and the reflected Cauchy formula on
a right half-plane; the analytic logarithmic weight and the weighted Hilbert inequality for Cauchy sums
over the zeros. The regular part of $\zeta'/\zeta$ with its logarithmic and Phragmén–Lindelöf bounds and the
Euler sum $\sum\Lambda(n)n^{-1/2-p}=1/(p-\tfrac12)-N(\tfrac12+p)$; the Hardy-space calculus of the forward
prime-minus-pole wave; the splitting of the prime and pole forms into forward and backward halves; the
Agmon commutator, the Agmon bound from the mass of the wave on one line and one moment, and its
energy form with the passage from bounded jump energies of truncated tilts to the domain.
Logarithmic energies of Hardy functions on vertical lines and their interpolation (windows
$(w+2+iT)^{-2}$, Plancherel on lines, Hölder); the state equation on the zero-free part of the strip, its
multiplier and the lower bound $\tfrac12\log-K$; square integrability on vertical lines of the head term, of
the prime tail and of the transform under decay; the descent of the abscissa of decay by an infimum.

[Reflection walk on the actual probe span](Pick/ProbeReflectionWalk.lean): with zero reflection $R$
and orthogonal probe projection $Q$, $W=R(2Q-1)$ is a surjective linear isometry and
$QW^nQ=T_n(QRQ)Q$ (`ProbeWalk.walkEquiv`, `ProbeWalk.walk_compression`). The probe matrix
coefficients of $QRQ$ are exactly the bare Weil kernel (`ProbeWalk.signal_inner_probe`).

[Chebyshev leakage](Pick/ChebyshevLeakage.lean): for $x$ in the probe span,
$\|T_n(QRQ)x\|^2+\|(1-Q)W^nx\|^2=\|x\|^2$.
Every order is contractive; equality holds exactly when $W^nx$ returns to that span
(`ProbeWalk.chebyshev_leakage_identity`, `ProbeWalk.chebyshev_norm_eq_iff_return`).

[Reflection-sector Gram decomposition](Pick/ProbeSectorGrams.lean): the actual Weil matrix is
$K=G_+-G_-$, while the ordinary probe Gram matrix is $G=G_++G_-$, with $G_\pm\succeq0$.
Thus $G\pm K\succeq0$ in the original probe coordinates, including dependent families
(`ProbeWalk.probeGram_eq_sector_difference`, `ProbeWalk.hilbertProbeGram_sub_probeGram_posSemidef`).

[Tail-moment forward differences](Wall/TailProbeDifferences.lean): writing $s_k=$ `tailProbeMoment F T k`,
the functional with moments $s_{n+k}-s_k$ integrates each polynomial $P(e^{u+T})$ against
$(e^{n(u+T)}-1)F(u)e^{10(u+T)}$ on $u<-T$ (`momentFunctional_tailProbeDifference`).
The same identity holds for polynomial squares and the actual critical state
(`tailProbeDifference_square`, `riemannHypothesis_or_tailProbeDifferences`).

[Polynomial tail filters](Wall/PolynomialTailFilters.lean): the filtered moments
$\sum_jq_js_{k+j}$ have nonnegative square tests exactly when
$q(e^{u+T})F(u)\ge0$ almost everywhere on $u<-T$
(`filteredTailMoment_square_nonnegative_iff`). Every nonzero real polynomial filter of an
actual critical state retains square tests of both signs on every tail
(`riemannHypothesis_or_indefinite_polynomial_tail_filters`). Finite filtering cannot restore
positivity; the exact density sign criterion describes the surviving positivity cone.

[Translation defect](ThePrimeSideBeyondTheWallIsTheDefectOfTheTranslatedState.lean): two-sided tests against the
heated zero series (`criticalState_hasSum_zeroPairing_heated_translate`), the full form at the translated state
(`criticalState_mixedEnergy_translate`) and its bound as a functional on $\mathcal H$
(`criticalState_sq_mixedEnergy_translate_le`).

[Wall potential](TheStateHasOneSignAtTheWallInTheMean.lean) and
[wall laws](TheStateAndThePrimeSideHaveExactLogarithmicLawsAtTheWall.lean): the Stieltjes potential and the logarithmic
moment of a profile (`wallPotential`, `wallLogMoment`, `abs_wallPotential_sub_wallLogMoment_le`), the collar kernel
at the wall (`abs_collarKernel_add_inv_le`), the bounded prime wave (`ae_norm_primeWave_le`), integration by parts
against a tail weight (`integral_Ioi_mul_integral_Ioi_eq`, `wallLogMoment_eq_wallMeanMoment_sub`,
`hasDerivAt_wallMeanMoment`), the logarithmic growth law (`tendsto_sq_div_log_of_hasDerivAt`) and the
transform as a Laplace average of the terminal mass
([orientation](TheSignOfTheStateAtTheWallIsTheSignOfItsHalfCharge.lean), `integral_mul_exp_eq_laplace_terminalMass`,
`exists_forall_pos_mul_integral_mul_exp`).

[Modulus of continuity](TheModulusOfContinuityOfTheStateIsCarriedByTheWall.lean): the exact energy of an increment
$E(F-\tau_kF)=a(e^{8k}-1)M$ (`criticalState_fullEnergy_increment`), Plancherel for increments
(`integral_one_sub_cos_mul_norm_sq_paperFT`, `integral_one_sub_cos_mul_norm_sq_paperFT_mul_gammaBracket`), and the
spectral lemma `eventually_log_mul_spectralModulus_le`: for densities $\Phi,\Psi\ge0$ with $(\log R-G_0)\Phi\le\Psi$ on
$\lvert r\rvert\ge R$, the inequality $\int(1-\cos kr)\Psi\le Pk+B\int(1-\cos kr)\Phi$ for small $k$ gives
$\log(1/k)\int(1-\cos kr)\Phi\le(P+\varepsilon)k$ for small $k$; Chebyshev on a terminal interval
(`sq_mul_measureReal_terminal_le`).

[Comparison principle](TheStateObeysAComparisonPrincipleAtTheWall.lean) and
[barriers](EveryConfinedGroundStateHasAnAmplitudeAtTheWall.lean), at every confinement ratio: the cutoff Lévy operator
$\mathfrak L_\delta X=2\Omega(\delta)X-K_\delta\star X$, whose pairing with a test is the jump form over the lags
$h>\delta$ (`cutoffLevy`, `integral_cutoffLevy_mul`); its value $\sqrt{\log(1/k)}+O(1)$ on the inverse root logarithm
and its lower bound on a ramp ([profile](TheLevyOperatorIsConstantOnTheInverseRootLogarithm.lean),
`neg_four_le_cutoffLevy_collarRamp`); bounded profiles decreasing towards the wall in the domain
([domain](BoundedProfilesDecreasingTowardsTheWallLieInTheEnergyDomain.lean)); the action of the part of $F$ left of
a collar through its logarithmic moment (`abs_exterior_sub_half_wallLogMoment_le`); the barrier lemma and its
integrated form (`halfLineEnergyMinimizer_exists_wall_barrier`, `wallLogMoment_le_of_ae_le`).
[Cut states](TheEnergyOfAConfinedGroundStateCutAtTheWall.lean): the two pieces of a profile cut at $-k$
(`wallExterior`, `wallCollar`), the energy of a piece of a minimizer as its pairing with the rest
(`halfLineEnergyMinimizer_fullEnergy_eq_sub_mixed`), and the pairing across the cut split by jump length, prime
row and pole row (`neg_mixedEnergy_wallExterior_wallCollar_le`).
[Amplitude](TheWallAmplitudeIsTheDerivativeOfTheGroundEnergy.lean): the predicate `IsWallAmplitude`, the change of
scale of the root logarithm (`abs_mul_sub_le_of_scale`, `abs_terminalMean_mul_wallRootLog_sub_le`), and the energy
of an increment at every ratio ([increments](TheIncrementsOfAConfinedGroundStateAreBoundedByItsConfinementMass.lean),
`halfLineEnergyMinimizer_fullEnergy_increment`).

**To build.** The endpoint moment $b=17-2\Theta$ when $\Theta$ is not attained, and pointwise decay of the state
(both need regularity of $F$ or a Hilbert inequality on the zeros without the logarithm); the shifted zero pairing on
$\tfrac72-\Theta\le c<\tfrac{17}2-2\Theta$ (a logarithm on the lines left of $\Theta-\tfrac92$); the growth of the index in
the ratio; pointwise regularity of $F$ on $u<0$: the wall law holds in mean square on $(-k,0)$; its pointwise form
$F(u)^2\log(1/\lvert u\rvert)\to8aM$ and the bounded order of $aF^+$ at the wall, where the primes enter through
$\sum_n\Lambda(n)n^{-1/2}F(x-\log n)$ at $x\to0^+$, need it; this is stage 5.

## 7. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| RH or a critical state exists | `riemannHypothesis_or_exists_criticalHalfLineGroundState` (AHD) | inherited |
| Probes lie in the domain | `criticalHalfLineEnergyDomain_probe` | unconditional |
| Probe kernel = Carathéodory kernel of $\xi'/\xi$ | `bareMixedEnergy_probe`, `probeSymbol_eq_logDeriv_xiCent`, `criticalHalfLineMixedEnergy_probe` | unconditional |
| Explicit formula on probes | `bareMixedEnergy_probe_eq_zeroSide` | unconditional |
| State equation on probes | `criticalState_probeEquation` | unconditional (for the state) |
| Holomorphic state equation | `stateEquation_ofReal_eq_zero`, `stateEquation_eqOn_zero`, `stateEquationCleared_eqOn_zero` | unconditional |
| Holomorphy reads the zeros | `zero_re_le_of_laplace_holomorphic` | unconditional |
| Decay ruler | `criticalState_not_integrable_of_zero`, `riemannHypothesis_or_criticalState_decay_ruler` | unconditional |
| Sign law | `criticalState_changes_sign_on_every_ray`, `riemannHypothesis_or_criticalState_changes_sign` | unconditional |
| Finite index at every ratio | `exists_bound_orthonormal_nonpositive` | unconditional |
| Poles of the state = zeros right of the line | `riemannHypothesis_or_criticalState_poles_at_zeros` | unconditional |
| Gamma pairing in Lévy form, holomorphic on $\operatorname{Re}p>-\tfrac12$ | `levyGamma_eq_stateGamma`, `differentiableOn_levyGamma` | unconditional |
| Continuation across the line; a pole at every zero with $\operatorname{Re}\rho\ge\tfrac12$ | `riemannHypothesis_or_criticalState_poles_across_line` | unconditional |
| Functional equation in Lévy form | `levySymbol_eq_neg_logDeriv`, `levyGamma_eq_reflected_euler` | unconditional |
| The state is meromorphic in the plane; prime heads left of the strip | `riemannHypothesis_or_criticalState_meromorphic`, `stateMeromorphic_eq_left` | unconditional |
| The zero sum converges after one subtraction; pole removal | `summable_zeroSum_term`, `differentiableAt_dividedSum`, `zeroSum_eq_dividedSum_add` | unconditional |
| Linear growth of the pairings with a probe | `exists_bound_levyGamma`, `exists_bound_levyRegularPart`, `exists_bound_leftRemainder` | unconditional |
| Explicit formula on the domain against probes | `entireDefect_eq_zero`, `globalRemainder_sub_eq_zeroSum`, `globalRemainder_sub_eq_tsum` | unconditional |
| $(\star)$: the state is the Cauchy transform of its values at the zeros | `criticalState_starEquation`, `criticalState_zeroValues_cauchy`, `riemannHypothesis_or_criticalState_starEquation` | unconditional |
| Exact multiplicities of the entire state product; full multiplicity detects unseen zeros | `criticalState_stateXiProduct_order`, `le_analyticOrderAt_stateXiProduct_iff`, `stateXiProduct_first_nonzero_jet` | unconditional (for the state or energy-domain profile) |
| $\xi(w+\tfrac{17}2)\mathcal LF(w)$ is entire | `differentiable_stateXiProduct`, `riemannHypothesis_or_criticalState_xi_mul_entire` | unconditional |
| $(\star)$ normalised at the left end; the Cauchy system of the zero values | `criticalState_starEquation_normalised`, `criticalState_zeroValues_cauchy_normalised` | unconditional |
| The continuation is $O(\lvert w\rvert^2)$ off the zeros | `norm_globalRemainder_le_of_dist`, `norm_stateMeromorphic_le_of_re` | unconditional |
| The averaged state decays at the rate of the zeros, beyond the barrier | `exists_bound_averagedState`, `criticalState_averaged_decay_beyond_barrier`, `riemannHypothesis_or_criticalState_averaged_decay` | unconditional |
| Two vertical lines cut out the zero series | `hasSum_zeroValues_two_lines`, `criticalState_hasSum_zeroValues_two_lines` | unconditional |
| The zero series is the state left of the wall and the prime side beyond it | `criticalState_hasSum_heated_zeroSeries`, `criticalState_heatedState_add_zeroSeries_le` | unconditional |
| The explicit formula at the state against smooth tests: $\sum_z\mathcal LF(z)\hat\psi(z)=a(\langle\psi,F^+\rangle-\langle\psi,e^{-8u}F\rangle)$; Weil's form of the state and a test is its zero side | `criticalState_hasSum_zeroSeries_test`, `criticalState_hasSum_zeroSeries_test_left`, `criticalState_hasSum_zeroSeries_test_right`, `criticalState_hasSum_bareMixedEnergy` | unconditional |
| The explicit formula at the state against the whole domain, Gaussian summation: $\lim_{\varepsilon\to0^+}\sum_z\mathcal LF(z)\mathcal LG(-z)e^{\varepsilon z^2}=B(F,G)$; the zero values are a negative vector: the limit at $G=F$ is $-a\int F^2e^{-8u}<0$, and a zero on the line contributes $\lvert\mathcal LF(z)\rvert^2e^{-\varepsilon(\operatorname{Im}z)^2}\ge0$ | `criticalState_hasSum_zeroPairing_heated`, `criticalState_tendsto_zeroPairing`, `criticalState_tendsto_zeroNorm`, `criticalState_zeroNorm_limit_neg`, `laplace_mul_laplace_neg_of_re_eq_zero` | unconditional |
| Every critical state sees a left zero ($-\tfrac12<\operatorname{Re}z_0<0$, $\mathcal LF(z_0)\ne0$) and has a left-strip pole | `criticalState_exists_seen_left_centredZero`, `criticalState_exists_seen_left_zetaZero`, `criticalState_has_left_strip_pole`, `riemannHypothesis_or_criticalState_sees_left_zero` | unconditional |
| $J_{\ge1}F$ is holomorphic on $\operatorname{Re}p<\tfrac52$; beyond-the-wall prime-pole continuation (and pure prime-head continuation on $\mathcal LG(-\tfrac12)=0$) excludes the critical state and is sharp at $\operatorname{Re}p=0$ | `differentiableOn_archimedeanWallTail`, `criticalState_not_hasBeyondTheWallPrimeContinuation`, `no_criticalState_of_beyondTheWallPrimeContinuation`, `no_criticalState_of_purePrimeHeadContinuation`, `zetaBeyondTheWallPrimeContinuation_iff_no_criticalState`, `not_forall_wallPrimeBalance_continues_past_zero` | unconditional |
| Beyond-the-wall prime-pole continuation fails on every prime-two deformation ($\tfrac12<\theta<1$) and on positive passive real-axis-positive Euler twins beyond every finite prefix | `not_modelBeyondTheWallPrimeContinuation_eulerLogCoeff`, `primeTwo_not_modelBeyondTheWallPrimeContinuation`, `exists_positive_euler_twin_failing_beyondTheWallContinuation` | unconditional |
| $\mathcal H$ is stable under bounded Lipschitz multipliers; the tilted state $e^{-cu}F$, $0\le c\le1$, lies in $\mathcal H$ | `criticalHalfLineEnergyDomain_lipschitz_mul`, `criticalHalfLineEnergyDomain_exp_mul_groundState` | unconditional |
| The energy norm controls the values at the zeros: $\sum_\rho\lvert\mathcal LH(w_\rho)\rvert^2\le\tfrac{16}\pi\int(C_0+\log(\lvert t\rvert+4))\lvert\mathcal LH(it)\rvert^2dt$ at unit depth | `tsum_norm_sq_laplace_zeros_le`, `summable_norm_sq_laplace_centredZero` | unconditional |
| The zero values of the state are square-summable; $\sum_z\mathcal LF(z)\mathcal LG(-z)=B(F,G)$ absolutely for tilt-regular $G$; the zero Parseval identity $\sum_{\mathrm{on}}\lvert\mathcal LF(z)\rvert^2+\sum_{\mathrm{off}}\mathcal LF(z)\mathcal LF(-z)=-a\int F^2e^{-8u}$ without a finiteness hypothesis | `criticalState_summable_norm_sq_zeroValues`, `criticalState_hasSum_zeroPairing`, `criticalState_hasSum_zeroNorm`, `criticalState_zeroParseval` | unconditional |
| One-point $(\star)$: $a\,\mathcal LF(w)=-\sum_z\mathcal LF(z)/(w+8-z)$ absolutely; Mittag-Leffler expansion of the continuation; the Cauchy system $a\,c_{z'}=-\sum_zc_z/(z'+8-z)$ has a nonzero square-summable solution | `criticalState_hasSum_starEquation`, `criticalState_hasSum_stateMeromorphic`, `criticalState_hasSum_zeroValues_cauchy`, `criticalState_exists_zeroValue_ne_zero` | unconditional |
| Weighted Hilbert inequality on the zeros without separation: $\int\lvert\sum_zc_z/(\sigma+it-z)\rvert^2\tfrac{dt}{\log(\lvert t\rvert+4)}\le\tfrac{160\pi D(\lvert C_0\rvert+2)}\delta\sum_z\lvert c_z\rvert^2$ for $\delta\le\sigma-\operatorname{Re}z\le D$; the continuation of the state lies in $L^2(dt/\log)$ on every line right of the transported zeros, unconditionally for $\operatorname{Re}w>-8+\tfrac{8999}{24000}$ | `integrable_and_integral_norm_sq_tsum_zeroCauchy_le`, `criticalState_integral_norm_sq_stateMeromorphic_line_le_of_abscissa`, `criticalState_integral_norm_sq_stateMeromorphic_line_le_seed` | unconditional |
| The regular part of $\zeta'/\zeta$ is sublogarithmic right of the zeros: $\lvert N(s_0+iT)\rvert\le C\log^{(b-s_0)/(b-a)}(\lvert T\rvert+4)$; $\lvert N\rvert^2\lesssim\log$ on $\operatorname{Re}s>\tfrac34+\tfrac\kappa2$, unconditionally on $\operatorname{Re}s>\tfrac{44999}{48000}$ | `exists_norm_zetaRegularLogDeriv_le_rpow`, `exists_norm_sq_zetaRegularLogDeriv_line_le_log`, `exists_norm_sq_zetaRegularLogDeriv_line_le_log_seed`, `tsum_vonMangoldtAtom_mul_cexp_neg` | unconditional |
| The forward prime-minus-pole wave is bounded in mean square: $(\text{forward prime}-\text{forward pole})(F,G)^2\le\tfrac1{2\pi}\int\lvert N(\tfrac12+\sigma+it)\rvert^2\lvert\mathcal LF(\sigma+it)\rvert^2dt\cdot\int G^2e^{-2\sigma v}$ on every line right of the zeros; the mass is finite for $\sigma>\tfrac14+\tfrac\kappa2$ | `isHalfPlaneHardy_primeWaveHardy`, `sq_forwardPrimeForm_sub_forwardPoleForm_le`, `integrable_norm_sq_zetaRegularLogDeriv_mul_laplace` | unconditional |
| The Agmon bound: if the wave has finite mass on $\operatorname{Re}p=\sigma$, $\kappa<\sigma<1$, and $\int F^2e^{-(16-4\sigma)u}<\infty$, then $\int F^2e^{-(16-2\sigma)u}<\infty$; a priori for $\sigma>\tfrac14+\tfrac\kappa2$, so $\int F^2e^{-bu}<\infty$ for $b<\tfrac{31}2-\kappa$ | `integrable_sq_mul_exp_of_line_mass`, `integrable_sq_mul_exp_of_zero_abscissa` | unconditional |
| Logarithmic energies interpolate between vertical lines: for a Hardy function $G$ of the right half-plane, $\int\log^k(\lvert t\rvert+4)\lvert G(\sigma+it)\rvert^2dt<\infty$ at $(\sigma_0,k_0)$ and $(\sigma_1,k_1)$, $0\le k_j\le2$, gives it at every convex combination | `integrable_log_rpow_mul_norm_sq_line_interp`, `lintegral_norm_sq_line_interp` | unconditional |
| The state equation on the zero-free strip: under $\int F^2e^{-bu}<\infty$, $\mathcal LF(p)A(p)=-a\mathcal LF(p-8)-J_G(p-2)+T_F(p)-\mathcal LF(-\tfrac12)/(p+\tfrac12)$ on $\kappa<\operatorname{Re}p<\tfrac12$, $16-b<2\operatorname{Re}p$; $\lvert A(s+it)\rvert\ge\tfrac12\log(\lvert t\rvert+4)-K$; $\int\log^2(\lvert t\rvert+4)\lvert\mathcal LF(s+it)\rvert^2dt<\infty$ for $b>16-2s$ | `laplace_mul_stripMultiplier_eq`, `exists_half_log_sub_le_norm_stripMultiplier`, `integrable_log_sq_mul_norm_sq_laplace_line` | unconditional |
| The decay law: for $\kappa\ge0$, every centred zero has $\operatorname{Re}z\le\kappa$ iff $\int F^2e^{-bu}<\infty$ for every $b<16-2\kappa$; $\sup\{b:\int F^2e^{-bu}<\infty\}=17-2\Theta$; unconditionally $b<15+\tfrac{3001}{12000}$ | `forall_re_centredZero_le_iff_integrable_sq_mul_exp`, `isLUB_integrable_sq_mul_exp`, `integrable_sq_mul_exp_of_zero_abscissa_sharp`, `integrable_sq_mul_exp_seed` | unconditional |
| The transform converges exactly right of the transported zeros: for $0\le\kappa\le1$, the centred zeros lie in $\operatorname{Re}z\le\kappa$ iff $\mathcal LF$ is holomorphic on $\operatorname{Re}w>\kappa-8$; there the continuation is the transform, $a\mathcal LF(w)=-\sum_z\mathcal LF(z)/(w+8-z)$, and $\int\lvert\mathcal LF(\sigma+it)\rvert^2dt=2\pi\int F^2e^{2\sigma u}du$; the state equation and two logarithms hold on all of $\kappa<\operatorname{Re}p<\tfrac12$ | `forall_re_centredZero_le_iff_differentiableOn_laplace`, `stateMeromorphic_eq_laplace_right_of_zeros`, `criticalState_hasSum_starEquation_right_of_zeros`, `integral_norm_sq_stateMeromorphic_line_right_of_zeros`, `laplace_mul_stripMultiplier_eq_right_of_zeros`, `integrable_log_sq_mul_norm_sq_laplace_line_right_of_zeros` | unconditional |
| The moments $M(b)=\int F^2e^{-bu}$ have a pole at the exponent $b_\rho=17-2\operatorname{Re}\rho$ of every zero right of the line: $\liminf_{\eta\to0^+}\eta\,M(b_\rho-\eta)\ge(m_\rho\lvert\mathcal LF(\rho-\tfrac12)\rvert/a)^2>0$ and $M(b_\rho)=\infty$; a finite $M(b)$ puts every zero in $\operatorname{Re}\rho<\tfrac{17-b}2$; if $\Theta$ is attained, $M(b)<\infty$ iff $b<17-2\Theta$ | `criticalState_eventually_le_mul_moment_of_zero`, `criticalState_not_integrable_at_zero_exponent`, `zero_re_lt_of_integrable_sq_mul_exp`, `integrable_sq_mul_exp_iff_of_attained` | unconditional |
| The decay law in the energy norm: for $\kappa\ge0$, every centred zero has $\operatorname{Re}z\le\kappa$ iff $e^{-cu}F\in\mathcal H$ for every $c<4-\kappa$; $\sup\{c:e^{-cu}F\in\mathcal H\}=\tfrac92-\Theta$, and if $\Theta$ is attained the tilt lies in $\mathcal H$ iff $c<\tfrac92-\Theta$; $\int\log(\lvert t\rvert+4)\lvert\mathcal LF(s+it)\rvert^2dt<\infty$ for $s>\Theta-\tfrac92$; for $c<\tfrac72-\Theta$, $\sum_z\lvert\mathcal LF(z-c)\rvert^2<\infty$ and $\sum_z\mathcal LF(z)\mathcal LF(-z-c)=-a\int F^2e^{-(8+c)u}du$ | `forall_re_centredZero_le_iff_tilt_mem_energyDomain`, `isLUB_tilt_mem_energyDomain`, `tilt_mem_energyDomain_iff_of_attained`, `integrable_log_mul_norm_sq_laplace_line_of_lt`, `criticalState_summable_norm_sq_shifted_zeroValues`, `criticalState_hasSum_shifted_zeroPairing` | unconditional |
| The wall law: for $k\ge0$ and $G\in\mathcal H$, $E(\tau_kF,G)=a\bigl(\int_0^kF^+(x)G(x-k)\,dx+(e^{8k}-1)\int e^{-8u}F(u)G(u-k)\,du\bigr)$; for $G=F$, $\int_0^kF^+(x)F(x-k)\,dx=-(1-e^{-8k})\int F(u)F(u+k)e^{-8u}du$ and $k^{-1}\int_0^kF^+(x)F(x-k)\,dx\to-8\int F^2e^{-8u}$; $\bigl((1-e^{-8k})\int F(u)F(u+k)e^{-8u}du\bigr)^2\le\int_0^k\lvert F^+\rvert^2\int_{-k}^0F^2$; for $G$ carried by $[-k,0)$, $a\lvert\int_0^kF^+(x)G(x-k)\,dx\rvert^2\le(e^{8k}-1)\int F^2e^{-8u}\,E(G)$ | `criticalState_mixedEnergy_translate`, `criticalState_beyondWallPairing_translate`, `criticalState_tendsto_beyondWallPairing_div`, `criticalState_wall_uncertainty`, `criticalState_norm_sq_beyondWallPairing_collar_le` | unconditional |
| Sign at the wall: $\lvert aF^+(x)+\tfrac12\Phi(x)\rvert\le B$ for almost every $0<x<1$, $\Phi(x)=\int_{v>0}F(-v)\frac{dv}{x+v}$; $\bigl(k^{-1}\int_{-k}^0F\bigr)\int_{v>k}F(-v)\frac{dv}v\to16a\int F^2e^{-8u}$; one sign $s=\pm1$ with $s\int_{-k}^0F>0$ and $s\int_{v>k}F(-v)\frac{dv}v>0$ for all small $k$; $\int_0^k\lvert F^+\rvert^2\ge ck\log(2/k)$ | `criticalState_exists_ae_norm_beyondWall_add_wallPotential_le`, `criticalState_tendsto_terminalMean_mul_wallLogMoment`, `criticalState_exists_sign_at_wall`, `criticalState_eventually_log_le_integral_sq_beyondWallProfile` | unconditional |
| Laws of the wall, $M=\int F^2e^{-8u}$: $\bigl(k^{-1}\int_{-k}^0F\bigr)^2\log(1/k)\to8aM$; $\bigl(\int_{v>k}F(-v)\frac{dv}v\bigr)^2/\log(1/k)\to32aM$; $\lvert aF^+(x)+\tfrac12\int_{v>x}F(-v)\frac{dv}v\rvert\le B$ for almost every $0<x<1$ and $aF^+(x)/\sqrt{\log(1/x)}\to-s\sqrt{8aM}$ essentially as $x\to0^+$; $\log(2/k)\int_{-k}^0F^2\ge4aMk$ for small $k$ | `criticalState_tendsto_sq_terminalMean_mul_log`, `criticalState_tendsto_sq_wallLogMoment_div_log`, `criticalState_exists_ae_norm_beyondWall_add_wallLogMoment_le`, `criticalState_wall_laws`, `criticalState_eventually_le_log_mul_terminal_square_mass` | unconditional |
| Orientation of the wall: $\mathcal LF(\sigma)=\sigma\int_{h>0}\bigl(\int_{-h}^0F\bigr)e^{-\sigma h}dh$ for $\sigma>0$; $\mathcal LF(\tfrac12)\int_{-k}^0F>0$ and $\mathcal LF(\tfrac12)\int_{v>k}F(-v)\frac{dv}v>0$ for all small $k$; $\mathcal LF(\tfrac12)\operatorname{Re}F^+(x)<0$ for almost every small $x>0$ | `integral_mul_exp_eq_laplace_terminalMass`, `criticalState_eventually_halfCharge_mul_terminalMass_pos`, `criticalState_exists_ae_halfCharge_mul_beyondWall_neg` | unconditional |
| Modulus of continuity: $\frac{\log(1/k)}k\int(F(u)-F(u+k))^2du\to8aM$ and $\frac{\log(1/k)}k\int_{-k}^0F^2\to8aM$, while $\frac{\log(1/k)}k\int_{u\le-k}(F(u)-F(u+k))^2du\to0$; wall law in mean square $k^{-1}\int_{-k}^0\bigl(\sqrt{\log(1/k)}\,F-s\sqrt{8aM}\bigr)^2\to0$, and $\lvert\{u\in(-k,0):sF(u)\le0\}\rvert/k\to0$ | `criticalState_tendsto_log_div_mul_sq_increment`, `criticalState_tendsto_log_div_mul_terminal_sq`, `criticalState_tendsto_log_div_mul_interior_sq_increment`, `criticalState_meanSquare_wall_law` | unconditional |
| Comparison principle at the wall, every ratio: a minimizer lies below every bounded barrier of $\mathcal H$ on a collar $(-k,0)$ on which the cutoff Lévy operators of the barrier exceed the action of the part of $F$ left of the collar by a fixed constant | `halfLineEnergyMinimizer_exists_wall_comparison` | unconditional |
| The cutoff Lévy operators are constant on the inverse root logarithm: $\lvert\mathfrak L_\delta[(\log(1/\lvert u\rvert))^{-1/2}1_{(-k,0)}](-t)-\sqrt{\log(1/k)}\rvert\le9$ for $\delta\le t<k/2$, $k\le\tfrac14$; bounded profiles decreasing towards the wall lie in $\mathcal H$ | `abs_cutoffLevy_wallLogProfile_sub_le`, `criticalHalfLineEnergyDomain_of_antitone_collar` | unconditional |
| Wall amplitude at every ratio: every minimizer $F$ of the confined form at a ratio $R>0$ has an amplitude $\ell$ with $\int_{v>k}F(-v)\frac{dv}v\big/\sqrt{\log(1/k)}\to2\ell$ and $\sqrt{\log(1/\lvert u\rvert)}\,F(u)\to\ell$ essentially as $u\to0^-$ | `halfLineEnergyMinimizer_exists_wallAmplitude` | unconditional |
| Energy of the cut state, every ratio: a profile of $\mathcal H$ vanishing on $[-h,\infty)$ has $Q_R(H)\ge\lambda(R)\int H^2+a(R)(1-e^{-8h})\int H^2e^{-8u}$; sharp cuts of bounded profiles lie in $\mathcal H$; if $\lvert F\rvert\le B$ on $[-2k,0)$ then $a(R)(1-e^{-8k})\int_{u<-k}F^2e^{-8u}\le\tfrac12\int_{v>k}F(-v)\frac{dv}v\int_{-k}^0F+KBk+B^2k$ | `criticalHalfLineFullEnergy_ge_ground_add_terminal_wall`, `criticalHalfLineEnergyDomain_wallExterior`, `halfLineEnergyMinimizer_exists_wall_energy_le` | unconditional |
| The wall amplitude is the derivative of the ground energy: for a minimizer $F$ at a ratio $R>0$ with amplitude $\ell$ at the wall, $\ell^2=8a(R)\int F^2e^{-8u}=-8R\lambda'(R)$; $k^{-1}\int_{-k}^0F\cdot\sqrt{\log(1/k)}\to\ell$; $\ell^2\ge8a(R)>0$ and $\ell F>0$ almost everywhere near the wall; at every ratio $\log(1/k)\int(F(u)-F(u+k))^2du\le(8a(R)M+\varepsilon)k$ for small $k$ | `IsWallAmplitude.sq_eq`, `IsWallAmplitude.hasDerivAt_groundEnergy`, `IsWallAmplitude.tendsto_terminalMean`, `IsWallAmplitude.exists_ae_mul_pos`, `halfLineEnergyMinimizer_eventually_log_mul_sq_increment_le`, `halfLineEnergyMinimizer_exists_wallAmplitude_sq` | unconditional |
| Modulus of continuity at every ratio $R>0$, $M=\int F^2e^{-8u}$: $\frac{\log(1/k)}k\int(F(u)-F(u+k))^2du\to8a(R)M$ and $\frac{\log(1/k)}k\int_{-k}^0F^2\to8a(R)M$, while $\frac{\log(1/k)}k\int_{u\le-k}(F(u)-F(u+k))^2du\to0$; $\bigl(k^{-1}\int_{-k}^0F\bigr)^2\log(1/k)\to8a(R)M$ | `halfLineEnergyMinimizer_tendsto_log_div_mul_sq_increment`, `halfLineEnergyMinimizer_tendsto_log_div_mul_terminal_sq`, `halfLineEnergyMinimizer_tendsto_log_div_mul_interior_sq_increment`, `halfLineEnergyMinimizer_tendsto_sq_terminalMean_mul_log` | unconditional |

## 8. Traps

| Trap | Truth |
|---|---|
| Stability, outerness or cyclicity exclude the state | They hold off RH (killed-route ledger) |
| The state has one sign | It changes sign on every ray (sign law) |
| Continuation of $\mathcal LF$ needs the explicit formula on $\mathcal H$ | Prime coordinates and $\zeta'/\zeta$ suffice |
| Improving the exponential barrier is free | By the decay ruler it is a zero-free half-plane: $b$ yields $\Theta\le\frac{17-b}2$ |
| On-line zeros give a new decay bound $b\le16$ | The state exists only off RH, where off-line zeros already give $b^*<16$ |
| Finite index needs arithmetic | Confinement compactness gives it for every configuration |
| Functional equation + Euler product + positive coefficients exclude | Positive Euler twins retain these and real-axis nonvanishing despite off-line zeros; logarithmic positivity fails |
| The sign law is soft | It uses that $\zeta$ has no real zero in $(\tfrac12,1)$; prime-two deformations can have one |
| The exponent 8 is canonical | Any confinement exponent works; 8 only fixes the shift of the residue transport |
| The Gamma pairing continues only by deforming the Fourier contour | Its Lévy form converges on $\operatorname{Re}p>-\tfrac12$, and its symbol is the functional equation |
| Continuation past the strip needs the explicit formula | Left of the strip the Euler parts cancel; the remainder is head term, prime heads and charges |
| $(\star)$ needs bounds for $\zeta'/\zeta$ on horizontal segments of the strip | Pole removal and Liouville use linear growth of the pairings and $\sum_z\lvert z\rvert^{-2}<\infty$ only |
| $\sum_z\mathcal LG(z)/(p-z)$ converges for $G\in\mathcal H$ | For a general profile the values are bounded and the sum needs one subtraction; for the state and for tilt-regular profiles the values are square-summable and the sum converges absolutely |
| The convergent half of the decay law is a line shift of $(\star)$ | No pointwise decay on vertical lines is known, and the Hilbert inequality on the zeros gives only $L^2(dt/\log)$. The lines right of the transported zeros carry $L^2(dt)$ as a consequence of the decay law, which is proved in time by the Agmon bound |
| A Hilbert inequality for $\sum_zc_z/(w-z)$ needs separated zeros | The unit-window count suffices at the price of one logarithm; a cluster of $N$ zeros loses a factor of order $N$, so the count alone cannot remove the weight |
| The barrier $b=15$ of the comparison argument is the decay rate of the state | It is the price of absolute values in the forward prime sum; the forward prime and pole waves cancel to $-N\mathcal LF$, and $b^*=17-2\Theta$ |
| The growth law of $F^+$ is the mirror of the decay law | On the zero-free strip the multiplier of the state equation is $-\tfrac{\zeta'}{\zeta}(\tfrac12-p)$: logarithmic on $\kappa<\operatorname{Re}p<\tfrac12$, sublogarithmic on $\operatorname{Re}p<-\kappa$. The left lines gain no logarithm, so the descent does not start there; the rate of the zeros is known for the heated profile only |
| One Agmon step reaches the zeros | From the abscissa $\sigma$ a step reaches only $s$ with $(\tfrac12+\kappa)\sigma<s(\tfrac12-\kappa+2\sigma)$ and $\sigma<2s$: the mass of the wave on the new line is paid by interpolating two logarithms at $\sigma$ with one on the critical line; the abscissa reaches $\kappa$ as an infimum |
| $F(u)=-a^{-1}e^{8u}\sum_z\mathcal LF(z)e^{-zu}$ pointwise | The series is a distribution on the line; heated it converges absolutely, and left of the wall it differs from the state by the prime side behind a Gaussian |
| $F^+$ is reached only by tests supported beyond the wall | The translate $\tau_kF$ is a profile of $\mathcal H$, and its full form against $G\in\mathcal H$ is the pairing of $F^+$ on $(0,k)$ with $G(\cdot-k)$ plus a confinement term; against $F$ itself the pairing is the weighted autocorrelation of the state |
| Evaluate the collar pairing $\int_0^kF^+(x)F(x-k)\,dx$ from the prime form of $F^+$ and set it against the wall law | The substitution returns the weak equation $E(F,\tau_kF)=0$, which is the wall law. The information is in the kernel of the collar wave at the wall, $\kappa(t)=-\tfrac1{2t}+O(e^{t/2})$ |
| Exclude the state at the leading order of the wall | The collar kernel is archimedean and the prime wave enters $aF^+$ as a bounded term: the laws of the wall use of $\Lambda$ only $\sum_n\Lambda(n)n^{-2}<\infty$. The wall amplitude is the Weil energy of the state, $8aM=-8\,\mathrm{bare}(F)$ |

## 9. Context

| Neighbour | Interface |
|---|---|
| ArithmeticHodgeTheoryOfDegenerations | stage 0: domain, forms, threshold, state, weak equation, zero-freeness, ground energy, variational compactness |
| CriticalArithmeticCorrelationTheory | Gamma/prime/pole mixed forms, prime-term summability |
| RHTower | $\xi'/\xi$ partial fractions, two-channel resolvent kernel, Poisson–digamma reproduction, Landau abscissa calculus, residues of $\zeta'/\zeta$, $(s-1)\zeta(s)$ |
| HTGeometry | Cauchy estimates and real Taylor coefficients of holomorphic functions, analyticity of $\zeta$ |
| ArithmeticCastelnuovoSeveri | Pontryagin law (negative squares = right zeros) |
| ArithmeticOrientationGeometry | orientation index = seen right zeros |
| FrustratedArithmeticDirichletForms | frustration of the even sector |
| BlackHoleRingdown, SelbergClass, HTGeometry | prime-two deformations, positive twins, Euler-log positivity (O11) |
| MetaplecticMobiusDescent | the seed $\Theta\le20999/24000$: decay rate $17-2\Theta\ge183001/12000$ |

| Subfolder | Content |
|---|---|
| (top level) | probe kernel, state equation and its continuation, $(\star)$, residues, sign law, finite index, decay law and its transform side |
| Zeros/ | zero pairing of two profiles, zero Parseval identity, multiplicities of the entire state product, the seen left zero |
| Index/ | null vectors of the confined form, critical ladder, index law, bounded-index stratum, finite layer and B13 |
| Pick/ | the confined form on probes as Pick matrices: RH and the critical ratio decided on real nodes, Krein form on the zeros |
| Modes/ | mode expansions of the averaged state and of the heated profile beyond the wall; no finite mode set |
| Decay/ | sharp exponential barrier of the comparison argument, thick-lag form of the finite layer |
| Wall/, Collar/, Energy/ | profile beyond the wall in prime form, trivial-zero form of the archimedean tail, the wall seen from the left; collar coercivity and softness; charge hyperplane |
| Models/ | critical states of tempered configurations with a finite off-line layer, of curves over finite fields, of Beurling and twin models; failure of the stage 5 criterion on the models |
| Nonlinear/, Certificates/, Analysis/ | nonlinear tests of the state (modulus, Bregman, flat potentials), finite certificates for probe matrices, Landau's obstruction for measurable tails |

## 10. Success criteria and contributions

**Success.** Stages 1–4 in Lean, unconditional, stated for the actual state of the dichotomy. Stage 5
either proved, or reduced to a named arithmetic property that fails on the prime-two deformations or the
positive Euler twins, with the Lean theorem "property $\Rightarrow$ no state"; or a model on which the properties
of stages 0–4 are realized together, which proves that the missing property lies outside them.

**A contribution** proves a property of the critical state (or of the critical states of model
configurations, with the model's role stated) that is unconditional and either an exact identity or a
restriction that removes candidate states. Restating an RH equivalence, fixed-aperture numerics and
finite computations are not contributions. A claim aimed at stage 5 names the arithmetic it uses and the
model on which it fails.

## 11. Big picture

The state is a single function whose transform is meromorphic in the plane and carries the zeros of
$\zeta$ as poles shifted by the confinement exponent: every zero in the strip is transported to $\rho-\tfrac{17}2$,
with residue $-m_\rho\mathcal LF(\rho-\tfrac12)/a$, nonzero on and right of the line. Right of the strip the equation
is read in prime coordinates; across it the Gamma pairing is the functional equation in Lévy form; left of
it the Euler parts cancel and $-a\mathcal LF(w)$ is the head term, the prime heads and the charges at $w+8$:
the prime side seen from beyond the wall. The explicit formula holds on the whole domain against probes,
so the state is the Cauchy transform of its own values at the zeros: $(\star)$ is a theorem, and stage 5
says that this Cauchy system has no solution in $\mathcal H$. Decay, sign and index laws are theorems and are
compatible with the existence of the state. What remains is the arithmetic contradiction (Q7–Q9): the two descriptions
of one meromorphic function, by its poles at the zeros and by its prime heads left of the strip, must be
shown incompatible. In time this is one series: $\sum_z\mathcal LF(z)e^{-zu}$ is $-a\,e^{-8u}F(u)$ left of the wall
and $a\,F^+(u)$ beyond it. Paired with the state itself the series gives $-a\int F^2e^{-8u}<0$: the zero values
form a negative vector of the zero pairing, and the zeros on the line contribute nonnegative terms.
The zero values are square-summable, so the Cauchy system is an equation in $\ell^2$ of the zeros: $(\star)$
holds at every point right of the transported zeros with an absolutely convergent sum, and on every
vertical line there the continuation is the transform and is square integrable:
$\int|\mathcal LF(\sigma+it)|^2dt=2\pi\int F^2e^{2\sigma u}du$. The state itself decays exactly at the rate of the zeros: the forward prime
sum and the pole wave cancel to the regular part of $\zeta'/\zeta$, the state equation gives the transform
two logarithms on the lines of decay, and the abscissa of decay descends to the zeros:
$\sup\{b:\int F^2e^{-bu}<\infty\}=17-2\Theta$. At the wall both descriptions of the series are explicit to leading order:
with $M=\int F^2e^{-8u}$ and $s$ the sign of the half-charge $\mathcal LF(\tfrac12)$, the terminal mean of the state is
$s\sqrt{8aM/\log(1/k)}$ and the prime side is $-s\,a^{-1}\sqrt{8aM\log(1/x)}$; the primes enter one order below.
