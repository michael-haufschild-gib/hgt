# Bi-Scale / Logarithmic-Grid Uncertainty Theory (`GaloisForLFunctions.BiScaleUncertainty`)

## Current arithmetic applicability (19 October 2026)

The local visibility classification in
[`SieveLocalVisibilityClassification.lean`](SieveLocalVisibilityClassification.lean)
assumes a nonzero highest-dyadic coordinate. It is a valid theorem on that
stratum. It does not cover squarefree-supported arithmetic rows when $N\ge4$:
their coordinate at $2^{\lfloor\log_2N\rfloor}$ is zero.
[`SieveArithmeticSourceAnchors.lean`](SieveArithmeticSourceAnchors.lean) proves
this fact for every squarefree-supported row, hence every Möbius taper.

For a prime $p\in(N/2,N]$, the existing single-multiple identity gives
$Y_{N,c}(p)=c(p)/p$. For $c(d)=\mu(d)w(d)$ this is $-w(p)/p$, nonzero exactly
when $w(p)\ne0$. For the Barban–Vehov cutoff $X$, it is nonzero exactly when
$p<X$; the endpoint $p=X$ and primes beyond $X$ fail. The same module proves
these conditions. A local stability classification with this prime anchor is
still research: the highest-dyadic phase argument cannot be transferred by
changing the anchor's name.

The factors $(N!)^6$ in the local classification's sharpness witnesses are
upper bounds for particular counterexample moments. They are not its local
recovery constant. `normalized_local_cubic` uses
$2+2\sum_{q=1}^N\varphi(q)$ when the reference anchor has magnitude at least $2$.
That constant still depends on $N$, and the observation model still uses
full-period moments. Neither fact supplies polynomial-horizon recovery.

For prime graph clocks, the mass and edge correlation readouts in
[`PrimeGraphClockCorrelationKernels.lean`](PrimeGraphClockCorrelationKernels.lean)
retain cutoff $k$, center $t=\log(N/q)$, and lag $\ell=\log(q/p)$, with prefactor
$N/(pq)$. The literal mass and edge measures are retained. No translation
invariance, lag-only formula, or sign of the complete edge-minus-mass form is
asserted. The next tasks are arithmetic estimates for these kernels and
source-compatible observation bounds, rather than another density or
polarization identity.

The full source graph contains negative constant directions:
`constantLift_energy` in
[`CHMDDoobSourceGraph.lean`](../RHTower/CHMDDoobSourceGraph.lean) gives energy
$-c^2/2$. A positivity target must therefore specify the receiver's odd or
otherwise constrained source family; positivity on the entire source graph
is false.

## 1. What This Field Is & Why It Exists

Classical harmonic analysis is built around the representation theory of a **single** locally
compact abelian group at a time:
- **Additive Fourier analysis** on $(\mathbb{R}, +)$ with uniform lattices $\mathbb{Z} \subset \mathbb{R}$,
  where translation-invariant operators are diagonalized by $e^{i r x}$ and discrete-to-continuum
  comparison is governed by Poisson summation and Euler–Maclaurin quadrature.
- **Multiplicative Mellin analysis** on $(\mathbb{R}_+^\times, \times)$, which becomes additive
  Fourier analysis in logarithmic coordinates $x = \log t$, turning multiplicative dilations
  $t \mapsto \lambda t$ into linear shifts $x \mapsto x + \log \lambda$.

Whenever a mathematical problem is simultaneously governed by **multiplicative dilation** and
**additive translation**, a fundamental structural conflict arises. In logarithmic scale coordinates
$x = \log t$, four competing structures act on the same state $f \in L^2(\mathbb{R})$:
1. **The Positive-Definite Correlation Cone:** Multiplicative correlations become translation
   autocorrelations
   $$h_f(x) = (f \star \tilde{f})(x) = \int_{\mathbb{R}} f(u)\,f(u+x)\,du, \qquad \widehat{h_f}(r) = |\hat{f}(r)|^2 \ge 0,$$
   inducing the **translation chord metric** $d_f(x, y) = \|T_x f - T_y f\|_{L^2} = \sqrt{2(h_f(0) - h_f(x - y))}$.
2. **The Exponentially Compressing Logarithmic Grid:** The uniform additive lattice $\mathbb{N}$
   becomes the non-uniform grid
   $$\Lambda_{\log} = \{\log n : n \ge 2\}, \qquad \delta_n = \log(n+1) - \log n = \log\!\left(1 + \frac{1}{n}\right) \asymp \frac{1}{n} = e^{-x},$$
   whose local spacing is $O(1)$ near the origin ($[0, \log 2]$) and compresses exponentially at
   large scale $x$, where integer nodes pack at Nyquist density $e^x$.
3. **The Hyperbolic Polar Continuum Weight:** The additive measure $dt$ and the arithmetic poles at
   $s = 1, 0$ (spectral frequencies $r = \pm i/2$) become the exponentially growing hyperbolic
   weight $2\cosh(x/2) = e^{x/2} + e^{-x/2}$, imposing the **polar balance law**
   $$\int_0^\infty h_f(x)\,\cosh(x/2)\,dx = 0 \quad\Longleftrightarrow\quad \int_0^\infty h_f^+(x)\,\cosh(x/2)\,dx = \int_0^\infty h_f^-(x)\,\cosh(x/2)\,dx.$$
4. **The Singular Archimedean Lévy–Sinh Jump Functional:** The archimedean scale-dilation generator
   $\Omega(r) = \operatorname{Re}\psi(1/4 + ir/2) - \log\pi$ becomes the non-local increment energy
   $$\mathcal{J}_{\mathrm{arch}}(f) = \int_0^\infty \bigl(h_f(0) - h_f(x)\bigr)\,w_{\mathrm{arch}}(x)\,dx, \qquad w_{\mathrm{arch}}(x) = \frac{e^{x/2}}{\sinh x} = \frac{2}{e^{x/2} - e^{-3x/2}},$$
   which has a **$1/x$ singularity at the origin** ($x \to 0^+$) and decays as **$2 e^{-x/2}$** at
   infinity ($x \to \infty$), matching the critical-line prime weight $2/\sqrt{n}$ at $x = \log n$:
   $$w_{\mathrm{arch}}(\log n) = \frac{2}{\sqrt{n}} + \frac{2}{\sqrt{n}(n^2 - 1)} \qquad (n \ge 2).$$

**Bi-Scale / Logarithmic-Grid Uncertainty Theory** is the mathematical discipline that studies the
geometry, convex sphere duality, multi-node Gram/Schur residuals, non-commutative hyperbolic
multiplier calculus, discrete/continuum coprime shear, and measure-transport inequalities of states
and correlation kernels simultaneously constrained by logarithmic arithmetic grids and hyperbolic
archimedean scale measures.

---

## 2. Core Mathematical Objects & Language

| Concept | Mathematical Definition & Role |
| :--- | :--- |
| **Autocorrelation & Chord Increment** | $h_f(x) = \int_{\mathbb{R}} f(u)f(u+x)\,du$, origin energy $R = h_f(0) = \|f\|_2^2$, increment $\Delta h_f(x) = h_f(0) - h_f(x) = \frac{1}{2}\|T_x f - f\|_2^2 \in [0, 2R]$. |
| **Krein Increment Inequality** | $(h_f(x) - h_f(y))^2 \le 2 h_f(0)(h_f(0) - h_f(x - y))$; controls local variation of $h_f$ across any step $y - x$ solely via the origin increment $\Delta h_f(y - x)$, without derivatives. |
| **Hyperbolic Lobes** | $h_f = h_f^+ - h_f^-$ with $h_f^+(x) = \max(h_f(x), 0)$ and $h_f^-(x) = \max(-h_f(x), 0)$; on the polar hyperplane, positive and negative $\cosh(x/2)$-moments are identically equal. |
| **Difference-Orthogonal Clique & Dyadic Cosets** | Any finite family $\{t_i\}_{i \in s}$ with $h_f(t_i - t_j) = 0$ ($i \ne j$). Because $m \mid n \implies \log n - \log m = \log(n/m)$, every dyadic-odd coset $\mathcal{C}_m = \{\log(m \cdot 2^k)\}$ ($m$ odd) is a clique under grid blindness. |
| **Clique Sphere Duality Factor** | $\mathcal{D}_s(w) = \sum_{i \in s} w_i - \sqrt{\sum_{i \in s} w_i^2} \ge 0$; measures the $\ell^1$-vs-$\ell^2$ amplification of an orthogonal clique on the Bessel sphere $\sum_{i \in s} u_i^2 \le R^2$. |
| **Archimedean Weight Triad** | Forward weight $w_{\mathrm{arch}}(x) = \frac{e^{x/2}}{\sinh x}$, functional-equation dual weight $w_{\mathrm{dual}}(x) = \frac{e^{-x/2}}{\sinh x}$, and smooth positive-definite secant core $w_{\mathrm{sech}}(x) = \frac{1}{\cosh(x/2)}$, related by $w_{\mathrm{arch}} = w_{\mathrm{sech}} + w_{\mathrm{dual}}$. |
| **Reciprocal Archimedean Weight** | $w_{\mathrm{arch}}(y)^{-1} = e^{-y/2}\sinh y = \frac{1}{2}e^{y/2}(1 - e^{-2y}) \le y\,e^{y/2}$; turns the $1/y$ origin singularity of $w_{\mathrm{arch}}$ into a **linearly vanishing factor $O(y)$** in dual transport bounds. |
| **All-Scale Critical-Line Weight** | $\varpi_n = \sqrt{2}\,n\bigl(n^{-1/2} - (n+1)^{-1/2}\bigr) \le \frac{2}{\sqrt{n+1}} \le w_{\mathrm{arch}}(\log(n+1))$; its normalized von Mangoldt companion is $w_\Lambda(n) = \frac{\Lambda(n)}{\log n}\,\varpi_n$. |
| **Hyperbolic Multipliers** | $(C_\alpha f)(u) = \cosh(\alpha u)f(u)$ and $(S_\alpha f)(u) = \sinh(\alpha u)f(u)$; non-commuting scale-moment operators that intertwine even and odd parity sectors. |
| **Coprime Shear & Trace Operators** | Multiplicative shifts $(M_k v)(n) = v(kn)$, additive differences $(\Delta_+ v)(n) = v(n+1) - v(n)$, and continuum logarithmic Sobolev traces linking $(\mathbb{N}, \times)$ to $(\mathbb{N}, +)$. |

---

## 3. How the Theory Works: The Five Core Mechanisms

### 3.1 Origin-Singularity Leverage, Convex Sphere Duality & Signed Collar Completion of Squares
Near any node $t \in \mathbb{R}$ and small collar offset $y > 0$, Krein's increment inequality couples
the node value $h_f(t)$ to the shifted collar increment $h_f(0) - h_f(t \pm y)$ and the origin
increment $h_f(0) - h_f(y)$ via the **Signed Collar-Increment Identity**:
$$\bigl(h_f(0) - h_f(t \pm y)\bigr) + h_f(t) = h_f(0) - \bigl(h_f(t \pm y) - h_f(t)\bigr) \;\ge\; h_f(0) - \sqrt{2 h_f(0)\bigl(h_f(0) - h_f(y)\bigr)}.$$
Applying Young's inequality with an origin weight $W_0 > 0$ and collar weight $w \ge 0$ gives the
universal single-node signed leverage bound—requiring **no blindness hypothesis** on $h_f(t)$:
$$\left(w - \frac{w^2}{2 W_0}\right) h_f(0) \;\le\; W_0\bigl(h_f(0) - h_f(y)\bigr) + w\bigl(h_f(0) - h_f(t \pm y)\bigr) + w\,h_f(t).$$
In an arbitrary real Hilbert space $E$ (`‖x‖² = ‖x_y‖² = R`), this generalizes to the exact
multi-node completion of squares:
$$W_0\bigl(R - \langle x, x_y\rangle\bigr) + \sum_{i \in s} w_i\bigl(R - \langle e_i, x_y\rangle\bigr) + \sum_{i \in s} w_i\langle e_i, x\rangle
  = \left(\sum_{i \in s} w_i\right) R - \frac{1}{2 W_0}\sum_{i, j \in s} w_i w_j \langle e_i, e_j\rangle + \frac{1}{2 W_0}\left\|\sum_{i \in s} w_i e_i - W_0(x_y - x)\right\|^2.$$
Because $w_{\mathrm{arch}}(y) \sim 1/y$ as $y \to 0^+$, the archimedean Lévy functional naturally
supplies a huge origin weight $W_0 \asymp 1/y$ at tiny offsets $y$, paying for the quadratic
penalty $\frac{w^2}{2 W_0}$.

### 3.2 Nyquist Cell Absorption & The All-Scale $O(n^{-3/2})$ Origin-Budget Convergence Law
On the $n$-th logarithmic Nyquist cell $[\log n, \log(n+1)]$ ($n \ge 2$), the cell width is
$\delta_n = \log(n+1) - \log n \le \frac{1}{n} \le \log 2$. For every $y \in (0, \delta_n]$,
$\sinh y < 1/n$ and $e^{y/2} > 1$, so the origin singularity of $w_{\mathrm{arch}}$ absorbs the
Nyquist density factor $n$:
$$n \;\le\; w_{\mathrm{arch}}(y) \quad\Longrightarrow\quad \int_0^{\delta_n} \bigl(h_f(0) - h_f(y)\bigr)\,dy \;\le\; \frac{1}{n}\int_0^{\log 2} \bigl(h_f(0) - h_f(y)\bigr)\,w_{\mathrm{arch}}(y)\,dy.$$
Why can we sum across **infinitely many dyadic shells** $[2, N+2)$ without blowing up the origin
collar $(0, \log 2]$? Because on the critical line $\sigma = 1/2$, the archimedean weight at
$\log(n+1)$ scales as $n^{-1/2}$, while the Nyquist origin-absorption factor is $1/n$, making each
cell's origin-budget share of order **$n^{-1/2} \cdot n^{-1} = n^{-3/2}$**, which is summable!
Specifically, choosing the **Canonical All-Scale Critical-Line Weight**
$$\varpi_n := \sqrt{2}\,n\left(\frac{1}{\sqrt{n}} - \frac{1}{\sqrt{n+1}}\right) \;\le\; \frac{2}{\sqrt{n+1}} \;\le\; w_{\mathrm{arch}}(\log(n+1))$$
makes the origin-budget shares $\varpi_n / n = \sqrt{2}(n^{-1/2} - (n+1)^{-1/2})$ **telescope
exactly** across all $n \in \{2, \dots, N+1\}$ to $1 - \sqrt{2/(N+2)} \le 1$, while the disjoint
origin collar $(0, \log 2]$ and all-scale tail $[\log 2, \log(N+2)]$ combine into **at most one copy
of $\mathcal{J}_{\mathrm{arch}}(f)$**. Multiplying by the normalized von Mangoldt ratio
$\theta_\Lambda(n) = \frac{\Lambda(n)}{\log n} \in [0, 1]$ yields $w_\Lambda(n) = \theta_\Lambda(n)\varpi_n$
with $w_\Lambda(n) - \frac{w_\Lambda(n)^2}{2\varpi_n} \ge \frac{1}{2}w_\Lambda(n)$, giving 100%
unconditional all-scale signed Weil lower bounds supported exclusively on prime powers $n = p^m$.

### 3.3 Krein–Kantorovich Measure Transport & Signed Chebyshev–Polar Coupling
To compare discrete prime-power sums $\sum_{n \ge 2} \frac{\Lambda(n)}{\sqrt{n}} h_f(\log n)$
against the continuum polar integral $\int_0^\infty 2\cosh(x/2) h_f(x)\,dx$ without using
second-derivative spectral moments $S(f) = -h_f''(0)$, the theory uses two derivative-free
transport mechanisms:
- **$S(f)$-Free Euler–Maclaurin Cell Quadrature:** Krein's increment inequality bounds the cell
  quadrature error $\bigl|(\int_t^{t+\delta} \rho)\,h_f(t) - \int_t^{t+\delta} \rho(x)h_f(x)\,dx\bigr|$
  directly by the origin collar integral $W_0\int_0^\delta (h_f(0) - h_f(y))\,dy$ plus
  $\frac{h_f(0)}{2W_0}\int_t^{t+\delta}\rho(x)^2\,dx$.
- **Differentiable Annular Correlation Transport & Signed Packet Gram Energy:** Averaging $h_f(t+y)$
  over an annulus $y \in [e^a, e^a + e^b]$ produces a $C^1$ correlation profile $H(t)$ for any
  continuous compact source, allowing exact Stieltjes integration by parts against the Chebyshev
  discrepancy $E(x) = \psi(e^x) - e^x$. Replacing unsigned mass by the **signed prime–polar packet**
  $P_L(u) = \sum_{n=2}^{N+2}\frac{\Lambda(n)}{\sqrt{n}}f(u+\log n) - \int_0^L 2\cosh(t/2)f(u+t)\,dt$
  retains prime–polar cancellation in the transport cost, paid by $\mathcal{J}_{\mathrm{arch}}(f)$
  and the linearly vanishing reciprocal weight $\int_{e^a}^{e^a+e^b} e^{-y/2}\sinh y\,dy$.

### 3.4 Non-Commutative Hyperbolic Multipliers & Functional-Equation Dual Decomposition
For odd test functions $f(-u) = -f(u)$ (`OWU` / `HF`), $f$ vanishes at the origin in parity sense,
so $(S_\alpha f)(u) = \sinh(\alpha u)f(u)$ (even) and $(C_\alpha f)(u) = \cosh(\alpha u)f(u)$ (odd)
are used to lift odd states into the even sector. Because
$\cosh(\alpha u)\cosh(\alpha(u+x)) - \sinh(\alpha u)\sinh(\alpha(u+x)) = \cosh(\alpha x)$ is
independent of $u$, every compactly supported $f$ satisfies the **Fundamental Hyperbolic
Intertwining Identity**:
$$h_{C_\alpha f}(x) - h_{S_\alpha f}(x) = \cosh(\alpha x)\,h_f(x), \qquad h_{C_\alpha f}(0) = h_f(0) + h_{S_\alpha f}(0),$$
and the **Two-Positive-Term Multiplier Defect Decomposition**:
$$\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(x)\bigr) + 2\sinh(\alpha x / 2)^2 h_f(0)
  = \cosh(\alpha x)\bigl(h_f(0) - h_f(x)\bigr) + \bigl(h_{S_\alpha f}(0) - h_{S_\alpha f}(x)\bigr).$$
Simultaneously, the archimedean weight splits under $s \leftrightarrow 1 - s$ into the smooth
positive-definite secant core and the dual Lévy weight:
$$\frac{e^{x/2}}{\sinh x} = \frac{1}{\cosh(x/2)} + \frac{e^{-x/2}}{\sinh x} \quad\Longrightarrow\quad \mathcal{J}_{\mathrm{arch}}(f) = \mathcal{J}_{\mathrm{sech}}(f) + \mathcal{J}_{\mathrm{dual}}(f),$$
connecting multiplier Gram bounds at $\alpha = 1/2$ directly to the `OWU`/`HF` plastic crossover
functional.

### 3.5 Non-Commutative $(ax+b)$ Coprime Shear & Producer–Consumer Duality
- **Coprime Shear & Mixed-Graph Coercivity:** Pure multiplicative divisibility chains cannot
  distinguish $\mathbb{N}$ from a Beurling generalized number system. The additive ring structure
  enters through $\gcd(n, n+1) = 1$: no divisor $d \ge 2$ divides both $n$ and $n+1$, so a state
  supported on multiples of $d$ has full neighbor Dirichlet energy
  $(v(n) - v(n-1))^2 + (v(n+1) - v(n))^2 = 2 v(n)^2$. In the continuum, rough logarithmic Sobolev
  primitives, path-congestion kernels, modulus velocities, and Markov clamps transfer multiplicative
  and nodal sign-change energies into additive Dirichlet energy.
- **Producer–Consumer Duality & Explicit Producers:** By Hilbert-space orthogonal projection, any
  consumer lower bound on correlations constrained at $\{\log n\}$ is dual to the $L^2$
  approximation error $\|p - \sum_{n \in s} c_n e_n\|^2$ of the polar functional $p$ by translates
  at $\log n$. On each Nyquist cell $[\log n, \log(n+1)]$, the explicit polar producer
  $\operatorname{nyquistPolarConstant}(n) = \cosh((\log n)/2) = \frac{\sqrt{n} + 1/\sqrt{n}}{2}$
  approximates $\cosh(x/2)$ in $L^2$ to within $\frac{1}{16 n^2}$ (and $\frac{1}{16 N}$ across a
  dyadic window). On the arithmetic side, applying dyadic Nyman–Beurling dilation stencils directly
  to the Chebyshev floor summatory $T(N) = \sum_{d \le N} \psi(\lfloor N/d \rfloor) = \sum_{m \le N} \log m$
  produces $T(2N) - 2T(N) = (2\log 2)N + O(\log N)$ and the bi-null producer
  $|T(4N) - 4T(2N) + 4T(N)| \le 5\log(4N+1) + 1$, bypassing $O(\sqrt{N})$ divisor noise completely.

---

## 4. The Five Fundamental Theorems of Bi-Scale Uncertainty Analysis

The foundational laws of the discipline are synthesized in
[`FundamentalTheoremsOfBiScaleUncertainty.lean`](FundamentalTheoremsOfBiScaleUncertainty.lean)
and proved unconditionally across six dedicated structural modules:

1. **First Fundamental Theorem — Universal Ramanujan Multi-Lag Spectral Diagonalization & Bi-Scale Rigidity**
   ([`UniversalRamanujanCovarianceAndBiScaleRigidity.lean`](UniversalRamanujanCovarianceAndBiScaleRigidity.lean),
   `first_fundamental_theorem_ramanujan_and_biscale_rigidity`):
   - For every truncation $N \in \mathbb{N}$, divisor-weight sequence $c : \mathbb{N} \to \mathbb{R}$,
     and additive shift lag $h \in \mathbb{N}$, the complete-period centered covariance on
     $\{1, \dots, N!\}$ is simultaneously diagonalized in Selberg divisor coordinates
     `selbergMultiplesCoord N c e` with eigenvalues equal to Ramanujan's trigonometrical sums
     $$c_e(h) = \operatorname{ramanujanLagWeight}(h, e) = \sum_{d \mid \gcd(e, h)} d\,\mu(e/d),$$
     characterized uniquely by the Dirichlet-ring inversion law $\sum_{e \mid g} c_e(h) = g \mathbf{1}_{g \mid h}$ (`ramanujanLagWeight_divisor_sum`, `ramanujanLagWeight_unique`).
   - Unifies $h = 0$ ($c_e(0) = \varphi(e)$), $h = 1$ ($c_e(1) = \mu(e)$), $h = 2$
     ($c_e(2) = \operatorname{lagTwoEigenvalue}(e)$), and prime lags $h = p$.
   - At unit lag $h = 1$, every mode $e \ge 2$ satisfies $\varphi(e) - \mu(e) \ge 1$
     (`totient_sub_moebius_ge_one`), yielding the universal shift-difference floor
     $\mathcal{E}_{\mathrm{add}}(N, c, 1) \ge 2 \sum_{e=2}^N (\operatorname{selbergMultiplesCoord}(N, c, e))^2$
     with vanishing iff all nonconstant Selberg coordinates vanish (`periodShiftDifferenceEnergy_one_eq_zero_iff`).
   - **Bi-Scale Joint Additive–Multiplicative Rigidity:** Simultaneous additive $q$-periodicity and
     multiplicative $q$-dilation invariance holds iff $f$ is constant (`periodic_and_scale_invariant_iff_const`),
     and the finite-window joint energy `biScaleJointEnergy K N f` vanishes iff $f$ is constant on
     $[1, N]$ (`biScaleJointEnergy_eq_zero_iff_const`).

2. **Second Fundamental Theorem — Hyperbolic Lorentz Boost ($\mathrm{SO}^+(1,1)$) Representation & Minkowski Light-Cone Rigidity**
   ([`HyperbolicLorentzBoostAndMinkowskiLightCone.lean`](HyperbolicLorentzBoostAndMinkowskiLightCone.lean),
   `second_fundamental_theorem_lorentz_boost_and_light_cone`):
   - The hyperbolic multipliers $(C_\alpha f)(u) = \cosh(\alpha u)f(u)$ and
     $(S_\alpha f)(u) = \sinh(\alpha u)f(u)$ form a faithful representation of the 1+1 Lorentz boost
     group $\mathrm{SO}^+(1,1)$ satisfying the hyperbolic Weyl commutation relations with translation $T_x$.
   - **Scale-Invariant Hyperbolic Casimir Invariant:**
     $$\mathcal{C}_\alpha(f, x) := \frac{h_{C_\alpha f}(x) - h_{S_\alpha f}(x)}{\cosh(\alpha x)} = h_f(x)$$
     is strictly independent of the boost rapidity $\alpha \in \mathbb{R}$ (`hyperbolicCasimirInvariant_rapidity_invariant`).
   - **Minkowski Light-Cone Identity & Null-Cone Zero-Grid Equivalence (`↔`):**
     $$h_{C_\alpha f}(x)^2 - h_{S_\alpha f}(x)^2 = \cosh(\alpha x)\,h_f(x)\,\bigl(h_{C_\alpha f}(x) + h_{S_\alpha f}(x)\bigr),$$
     with $h_f(x) = 0 \iff h_{C_\alpha f}(x) = h_{S_\alpha f}(x)$ (`autocorr_eq_zero_iff_coshMultiplier_eq_sinhMultiplier`)
     and $h_{C_\alpha f}(0)^2 - h_{S_\alpha f}(0)^2 \ge h_f(0)^2$ (`minkowski_lightCone_origin_ge_sq`).
   - **Exact $L^2$ Hilbert-Space Defect Identities:** The Peter–Paul chord inequality and Krein's
     doubling/increment inequalities are upgraded to exact $L^2$ square-integral defect identities
     (`autocorr_chord_peter_paul_defect_eq_integral`, `autocorr_krein_doubling_defect_eq_integral`,
     `autocorr_krein_increment_defect_eq_integral`).

3. **Third Fundamental Theorem — Origin Allocation Uniqueness (`↔`), Coupled Sphere Gain & Odd-Dyadic Incommensurability**
   ([`OriginAllocationUniquenessAndCoupledSphereGain.lean`](OriginAllocationUniquenessAndCoupledSphereGain.lean),
   `third_fundamental_theorem_origin_allocation_and_coupled_gain`):
   - **Unique Optimal Origin Allocation (`↔`):** By the exact Lagrange identity
     $(W^2 + A^2)(a^2 + q^2) - (Wa + Aq)^2 = (Aa - Wq)^2$, an origin allocation $\sum_{i \in s} a_i = W > 0$
     against collar loads $q_i \ge 0$ ($\sum_{i \in s} q_i = A > 0$) attains the sphere lower bound
     $\sqrt{W^2 + A^2}$ **if and only if** $A a_i = W q_i$ for all $i \in s$
     (`origin_allocation_cost_eq_lower_iff`, `origin_allocation_unique_minimizer_iff`).
   - **Universal Dominance of Joint Hilbert Coupling:** Combining Hilbert packets $p_i \in E$ prior
     to applying the origin-collar sphere penalty yields the nonnegative gain
     `coupledSphereGain W s p ≥ 0` over every partitioned allocation (`coupled_sphere_penalty_le_any_allocation`),
     with `coupledSphereGain W s p = 0 ↔ ∀ i, j ∈ s, ‖p j‖ • p i = ‖p i‖ • p j` (`coupledSphereGain_eq_zero_iff`).
   - **Diophantine Odd-Dyadic Incommensurability:** $(2q + 3)^k \ne n \cdot 2^k$ for all $q, n \in \mathbb{N}$
     and $k \ge 1$ (`odd_pow_ne_mul_two_pow`), so every nonzero multiple of $\log((2q+3)/2)$ is
     strictly disjoint from the integer logarithmic grid $\{\log n : n \in \mathbb{N}\}$
     (`odd_dyadic_log_progression_ne_log_nat`).

4. **Fourth Fundamental Theorem — Symmetric Polar Enforcement (`↔`) & Compensated Physical Logarithmic Producers**
   ([`EvenSourceSymmetricPolarEnforcement.lean`](EvenSourceSymmetricPolarEnforcement.lean) and
   [`CompensatedPhysicalLogarithmicProducer.lean`](CompensatedPhysicalLogarithmicProducer.lean),
   `fourth_fundamental_theorem_symmetric_polar_and_compensated_producer`):
   - **Even-Source Polar Infimum Equivalence (`↔`):** The symmetric 3-copy operator
     $g_T(u) = f(u) - \frac{1}{2\cosh(T/2)}(f(u - T) + f(u + T))$ preserves source parity
     (`evenPolarCopy_even_of_even`), kills both $\pm 1/2$ exponential moments simultaneously,
     preserves all local correlation ratios on $[-A, A]$ when $T > 2D + A$, and perturbs
     `normalizedArchEnergy` by $O(e^{-T})$, proving that any lower bound $C$ holds on even
     polar-neutral logarithmic-grid $C^r$ ($r \ge 2$) sources **if and only if** it holds on all
     even logarithmic-grid $C^r$ sources (`even_polar_log_grid_lower_bound_iff`).
   - **Compensated Physical Logarithmic Producers:** For every physical velocity $q \in L^2(\mathbb{R})$,
     the compensated velocity $v_n(q) = q_n - c_n(q)$ satisfies the exact orthogonal energy identity
     $\|v_n(q)\|^2 = \|q_n\|^2 + m_n(q)^2 / L_n \le (1 + e^{-(n+1)})\|q\|^2$ and $\int_{\mathbb{R}} v_n(q) = 0$,
     yielding compactly supported $C^1$ logarithmic states $g_n(q)(x) = F_{w_n(q)}(e^x)$ with exact
     weighted Dirichlet energy (`smoothedLogarithmicState_dirichlet_energy`).

5. **Fifth Fundamental Theorem — Critical Nyquist Finite Part $\mathcal{B}_m$ & Rescaled-Source Phase Transition**
   ([`NyquistCriticalFinitePartAndBroadClassification.lean`](NyquistCriticalFinitePartAndBroadClassification.lean),
   `fifth_fundamental_theorem_nyquist_critical_finite_part_and_classification`):
   - At the critical Nyquist Taylor exponent $\beta = m + 1$, subtracting the continuous mean
     counterterm $c_m \delta_k$ ($c_m = (m+1)^{m+1}/(2(m+2)!)$) from the cell mass $\alpha_k$ yields
     an absolutely summable cell discrepancy $|d_k(m)| \le D_m (k+1)^{-2}$ (`abs_nyquistCriticalCellDiscrepancy_le_inv_sq`),
     defining the **Critical Nyquist Finite Part** $\mathcal{B}_m = \sum_{k=0}^\infty d_k(m)$ with
     nodal convergence rate $|F_m(\log(N+1)) - \mathcal{B}_m| \le 2 D_m / (N + 1)$
     (`abs_nyquistCriticalPrefixPrimitive_sub_finitePart_le`).
   - By the autocorrelation total mass identity $\int_{\mathbb{R}} \operatorname{autocorr}(f, x)\,dx = (\int f)^2$
     (`integral_autocorr_eq_sq_integral`), rescaled broad sources undergo a sharp renormalization
     phase transition between positive-mean divergence and zero-mean cancellation (`nyquistZeroMeanWitness`).

---

## 5. The Ten Structural Traps (Obstructions & Design Laws)

Every researcher working in `BiScaleUncertainty` must know the following ten traps—each formally
proved as an obstruction or countermodel in the repository—and the exact mechanism that resolves it:

1. **Trap 1 — The Spectral-Moment / Derivative-Truncation Trap:**
   Replacing $\Omega(r)$ by $\Omega(0) \approx -2.752$ or by a polynomial Taylor moment
   $S(f) = \int r^2|\hat{f}(r)|^2\,dr = -h_f''(0)$ discards the non-local integral
   $\mathcal{J}_{\mathrm{arch}}(f)$, rendering discrete grid constraints invisible in the
   high-frequency regime $S(f)/h_f(0) \to \infty$.
   - *Rule:* Never bound quadrature or collar transport by $S(f)$; always bound increments directly
     by $\mathcal{J}_{\mathrm{arch}}(f)$ using Krein's derivative-free inequality.
2. **Trap 2 — The Ground-Subtraction / Translation-Invariance Trap:**
   Subtracting a translation-invariant continuum mean-field cannot distinguish the discrete
   logarithmic grid $\Lambda_{\log}$ from a shifted continuum unless the arithmetic node locations
   $\log n$ are coupled directly to the positive-definite correlation cone.
3. **Trap 3 — The Beurling–Deny Sign-Changing Nodal Collar Trap:**
   Applying standard Markov contraction ($f \mapsto |f|$) naively to a sign-changing state
   $f = f^+ - f^-$ drops the opposite-sign cross-collar interaction $4 f^+(u)f^-(u+x)$.
   - *Rule:* Track the nodal loss $4 f^+(u)f^-(u+x)$ explicitly via the exact modulus/clamp graph
     decomposition and transfer it into path slack or positive-definite Gram residuals.
4. **Trap 4 — The Single-Point Non-Dyadic Interpolation Trap ($x = \frac{4}{5}\log 2$):**
   Even when $h_f(\log 2) = 0$ for a smooth autocorrelation $h_f$, one **cannot** bound
   $h_f(0) - h_f(x) \ge c(x) h_f(0) > 0$ pointwise at non-dyadic points: a pulse train with spacing
   $\frac{4}{5}\log 2$ has $h_f(\log 2) = 0$ while $(h_f(0) - h_f(\frac{4}{5}\log 2))/h_f(0) \to 0$.
   - *Resolution:* By the **Reflected-Collar Sphere Law** $h_f(x)^2 + h_f(\log 2 - x)^2 \le h_f(0)^2$,
     $h_f(\frac{4}{5}\log 2) \to h_f(0)$ forces the reflected point $h_f(\frac{1}{5}\log 2) \to 0$.
     Folding the integral around the midpoint $\frac{1}{2}\log 2$ restores a strictly positive lower
     bound.
5. **Trap 5 — The Finite-Grid Distant-Copy Polar Decoupling Trap:**
   If only finitely many zeros $h_f(\log n) = 0$ ($2 \le n \le N_0$) are active, replacing $f(u)$ by
   $\operatorname{polarCopy}(f, T)(u) = f(u) - e^{-T/2}f(u - T)$ (or in the even sector by the
   symmetric 3-copy operator `evenPolarCopy f T`) for $T \gg \log N_0$ enforces the
   polar constraint $\int_0^\infty h(x)\cosh(x/2)\,dx = 0$ while changing
   $\mathcal{J}_{\mathrm{arch}}(f)/h_f(0)$ by only $O(e^{-T}) \to 0$.
   - *Resolution:* Keep the **infinite** logarithmic grid active: at scale $T = \log N$, the $N$
     Nyquist-packed nodes in $[\log N, \log(2N)]$ have spacing $\delta_n \asymp 1/N = e^{-T}$, forcing
     any fixed-profile polar lobe at scale $T$ to pay linear energy in $T$.
6. **Trap 6 — The Commutative Bochner / Beurling Semigroup Trap:**
   Translation inner products $\langle T_{t_i} f, T_{t_j} f\rangle = h_f(t_i - t_j)$ commute and
   only see multiplicative divisibility $m \mid n \implies \log n - \log m = \log(n/m)$, which is
   shared by Beurling generalized number systems that violate RH.
   - *Resolution:* Couple multiplicative shifts to the additive successor $n \mapsto n + 1$ (coprime
     shear and universal Ramanujan multi-lag covariance) and non-commutative hyperbolic multipliers $C_\alpha, S_\alpha$.
7. **Trap 7 — The Odd-Sector Hyperbolic Multiplier Leakage Trap:**
   Source blindness $h_f(\log 2) = 0$ for an odd function $f$ does **not** imply multiplier
   blindness $h_{S_\alpha f}(\log 2) = 0$: an odd 6-packet train can cancel $h_f(\log 2)$ while
   $\sinh(\alpha u)$ amplifies the outer pair by $e^{2\alpha T}$.
   - *Resolution:* Never assume $h_{S_\alpha f}(t) = 0$; use the Minkowski light-cone null-locus law
     $h_f(t) = 0 \iff h_{C_\alpha f}(t) = h_{S_\alpha f}(t)$ together with signed collar
     leverage on $C_\alpha f$ or centered source-Gram variance bounds.
8. **Trap 8 — The Midpoint-Compression / Narrow-Support Escape:**
   Rescaling a seed $f$ to support radius $r_1 \asymp 1/N$ and placing its polar copy at the
   logarithmic midpoint $T_N = \frac{\log N + \log(N+1)}{2}$ dodges every grid node $\log n$
   ($n \ge 2$) at logarithmic energy cost $\mathcal{J}_{\mathrm{arch}}(f)/h_f(0) \asymp \log N$.
   - *Resolution:* By **Bounded-Energy Width Rigidity**, because $w_{\mathrm{arch}}(x) \ge e^{-r_2/2}/x$
     on $(0, r_2]$, compressing support to radius $r_1$ costs at least
     $e^{-r_2/2}\log(r_2/r_1) h_f(0)$. In the bounded-energy regime
     $\mathcal{J}_{\mathrm{arch}}(f) \le |\Omega(0)| h_f(0)$, the support radius cannot be compressed
     into a distant midpoint gap $(\log N, \log(N+1))$.
9. **Trap 9 — The Homogeneous Blind-Subspace Trap:**
   Restricting to the grid-blind subspace $h_f(\log n) = 0$ multiplies $\Lambda(n)/\sqrt{n}$ by zero,
   erasing prime weights and failing to distinguish $\zeta(s)$ from off-line countermodels such as
   $\zeta(s-a)\zeta(s+a)$.
   - *Resolution:* Always formulate theorems for **general signed correlations** $h_f(\log n) \in \mathbb{R}$
     using signed collar leverage, the all-scale von Mangoldt weight $w_\Lambda(n)$, and
     Chebyshev–polar Stieltjes transport.
10. **Trap 10 — The Receiver-Only / Pre-Floor Divisor-Contamination Trap:**
    Building more receivers that merely reformulate Weil positivity into unproved Chebyshev bounds
    ("RH is $X$"), or subtracting the discrete counterterm $j$ *before* floor summation
    ($\sum_{d \le N} (\psi - \mathrm{id} + 2\gamma)(\lfloor N/d \rfloor)$), replaces the smooth
    archimedean counterterm by Dirichlet's divisor summatory $D(N) = \sum_{d \le N} \lfloor N/d \rfloor$,
    contaminating the $O(\log N)$-smooth Chebyshev factorial sum $T(N) = \sum_{m \le N} \log m$ with
    $O(\sqrt{N})$ divisor noise.
    - *Resolution:* Construct **explicit producers** with unconditional error bounds: instantiate the
      Nyquist-cell polar producer $\operatorname{nyquistPolarConstant}(n) = \cosh((\log n)/2)$
      ($O(1/n^2)$ cell $L^2$ error), the compensated physical box producer `smoothedLogarithmicState n q`,
      and the critical Nyquist finite part $\mathcal{B}_m$, and apply pole-cancelling dilation stencils
      directly to $T(N)$ ($T(2N) - 2T(N)$ and $T(4N) - 4T(2N) + 4T(N)$) to achieve unconditional
      $O(\log N)$ bounds.

---

## 6. How to Navigate & Extend the Codebase

Do **not** read every file sequentially—use the repository search tool to find exact declarations,
lemmas, and proof patterns:
```bash
scripts/formal_tools.py research "allScaleVonMangoldtWeight"
scripts/formal_tools.py research "ramanujanLagWeight periodCovariance"
scripts/formal_tools.py research "hyperbolicCasimirInvariant minkowski_lightCone"
scripts/formal_tools.py research "nyquistCriticalFinitePart compensatedVelocity"
```

### Engineering & Mathematical Discipline for Future Agents
1. **Unconditional Producers First:** Do not add more receiver-only "RH $\leftrightarrow X$"
   reformulations or leave producer weights $W(x)$ uninstantiated. Construct explicit producers and
   prove their unconditional quantitative bounds on concrete objects (`RealWeilTestFn`,
   `RealEvenPolarTestFn`, `C_c(ℝ, ℝ)`, `ℕ`, `ℝ`).
2. **Lean 4 Performance on `RealEvenPolarTestFn`:** Because `RealEvenPolarTestFn` is a nested
   `Subtype`, never run bare `linarith` or `nlinarith` when `g : RealEvenPolarTestFn` is in the
   local context (it recursively unfolds `Subtype.property` and stalls); always use
   `linarith only [h1, h2, ...]`, and invoke namespace theorems explicitly as
   `RealEvenPolarTestFn.foo g` rather than dot-projection `g.foo`.
3. **Umbrella & Lint Gate:** Wire new modules into
   [`formal/GaloisForLFunctions/BiScaleUncertainty.lean`](../BiScaleUncertainty.lean),
   verify `#print axioms` via a `/tmp` scratch file (only `[propext, Classical.choice, Quot.sound]`
   allowed), and keep zero `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations.

