# Bi-Scale Uncertainty

**Bi-Scale Uncertainty** is the theory of states and correlation kernels that are constrained at
the same time by two incompatible structures on the logarithmic line: the integer grid
$\{\log n\}$, which is an additive-translation object that compresses exponentially, and the
hyperbolic scale weight of the archimedean place, which is a multiplicative-dilation object that
grows exponentially. Its continuum objects are a real source $f$, its autocorrelation
$h_f(x)=\int f(u)f(u+x)\,du$, the singular archimedean energy
$\mathcal J(f)=\int_0^\infty (h_f(0)-h_f(x))\,\frac{e^{x/2}}{\sinh x}\,dx$, and the signed
prime–polar measure $\nu_N=\sum_{n\le N+2}\Lambda(n)n^{-1/2}\delta_{\log n}-2\cosh(t/2)\,\mathbf 1_{[0,L]}dt$.
Its arithmetic objects are finite divisor-sieve signals on their factorial period and the
translated moments that observe them. Its purpose is to state, as exact unconditional
inequalities, what the two structures force on each other, and to express the square-root
barrier of prime counting as a single bi-scale energy law.

Everything here is unconditional. The Riemann Hypothesis enters only through equivalences and
through criteria whose premise is an explicit energy bound; no theorem asserts such a premise.

---

## 1. Why

### 1.1 Two structures on one state

Additive Fourier analysis lives on $(\mathbb R,+)$ with the uniform lattice $\mathbb Z$;
multiplicative Mellin analysis lives on $(\mathbb R_{>0},\times)$ and becomes additive in the
coordinate $x=\log t$. A problem governed by both at once puts four structures on one state
$f\in L^2(\mathbb R)$ in logarithmic coordinates:

1. **The positive-definite cone.** Multiplicative correlations become the translation
   autocorrelation $h_f=f\star\tilde f$, with $\widehat{h_f}=|\hat f|^2\ge 0$. It carries the
   chord metric $\|T_xf-T_yf\|^2=2(h_f(0)-h_f(x-y))$.
2. **The logarithmic grid.** The integers become $\Lambda_{\log}=\{\log n:n\ge 2\}$ with
   spacing $\delta_n=\log\frac{n+1}{n}\in[\frac1{n+1},\frac1n]$: of order one near the origin, and
   of Nyquist density $e^x$ at scale $x$.
3. **The hyperbolic polar weight.** The measure $dt$ and the poles $s=0,1$ become the weight
   $2\cosh(x/2)$ and the **polar balance law** $\int_0^\infty h_f(x)\cosh(x/2)\,dx=0$, which
   says that the positive and negative lobes of $h_f$ carry equal hyperbolic mass.
4. **The singular archimedean energy.** The scale generator
   $\Omega(r)=\operatorname{Re}\psi(\tfrac14+\tfrac{ir}2)-\log\pi$ becomes the non-local
   increment functional $\mathcal J(f)$ with weight
   $$
   w_{\mathrm{arch}}(x)=\frac{e^{x/2}}{\sinh x}=\frac{2}{e^{x/2}-e^{-3x/2}},
   \qquad w_{\mathrm{arch}}(x)\sim\frac1x\ (x\to0^+),\qquad w_{\mathrm{arch}}(x)\sim 2e^{-x/2}\ (x\to\infty),
   $$
   and $w_{\mathrm{arch}}(\log n)=\frac{2}{\sqrt n}+\frac{2}{\sqrt n\,(n^2-1)}$: the critical-line
   prime weight $2/\sqrt n$ up to an explicit remainder.

The theory is the geometry of a state that has to satisfy constraints from all four at once.

### 1.2 Where the Riemann Hypothesis sits

For every real compact source $f$ the real part of Weil's explicit-formula functional with the
von Mangoldt coefficients is
$$
\operatorname{Re}W(f)=\Omega(0)\,h_f(0)+\mathcal J(f)-2\Bigl(\sum_{n\ge 2}\frac{\Lambda(n)}{\sqrt n}h_f(\log n)-\int_0^\infty 2\cosh(x/2)\,h_f(x)\,dx\Bigr),
$$
with $\Omega(0)=-(\gamma+\tfrac\pi2+\log 8\pi)$. On the polar hyperplane the archimedean part is
nonnegative exactly when $|\Omega(0)|\,h_f(0)\le\mathcal J(f)$: the **bi-scale uncertainty
inequality**. The prime term vanishes on the **blind cone** $h_f(\log n)=0$ for all $n\ge 2$, which
is therefore the prime-free half of the problem, and the sharp question on it is the infimum of
the normalized energy $\mathcal J(f)/h_f(0)$ against the constant $|\Omega(0)|$.

The square-root barrier appears in the same coordinates. With $\tilde E(t)=e^{-t/2}(\psi(e^t)-e^t)$
the normalized Chebyshev error and $L=\log(N+2)$,
$$
\int_0^L\tilde E(t)^2\,dt=\int_1^{e^L}\frac{(\psi(x)-x)^2}{x^2}\,dx ,
$$
and this mean square is $O(L)$ if and only if the Gram energy of $\nu_N$ against the Laplace
kernel $e^{-|s-t|/2}$ is $O(L)$, if and only if the pole-subtracted truncated series
$\sum_{n\le N+2}\Lambda(n)n^{-s}$ has weighted mean square $O(L)$ on the critical-line band
$|t|\le 2\pi\sqrt{N+2}$. The first statement is the mean-square form of RH. The theory proves
the equivalences and everything around the band unconditionally; the band itself is the wall.

### 1.3 Why "uncertainty" and why "bi-scale"

A compact source of width $w$ has spectral window $|\hat f|^2$ concentrated on $|\xi|\lesssim 1/w$.
Probing the band $|\xi|\le\sqrt x$ that carries the barrier needs sources of width $\lesssim1/\sqrt x$,
while the grid at scale $\log x$ has spacing $1/x$. The product of the position scale $\sqrt x$ and
the frequency scale $\sqrt x$ is the bi-scale uncertainty of probes. The origin singularity of
$w_{\mathrm{arch}}$ is what pays for the compression: on the $n$-th cell the weight dominates the
Nyquist density, $n\le w_{\mathrm{arch}}(y)$ for $0<y\le\delta_n$, and the critical exponent
$\frac12$ is exactly the one for which the resulting cell budgets $n^{-1/2}\cdot n^{-1}$ are
summable. On the arithmetic side the same tension appears as observation versus recovery: a
divisor-sieve signal is observed through translated moments on its period, and the question is
which moments determine it, up to which translation, with which stability exponent.

---

## 2. What: objects and language

### 2.1 Sources and correlations

For a real compactly supported source $f$ (continuous, $C^1$, or $C^2$ as the statement needs):

- **autocorrelation** $h_f(x)=\int f(u)f(u+x)\,du$; $h_f(0)=\|f\|^2$, $|h_f(x)|\le h_f(0)$, and
  $h_f(0)-h_f(x)=\tfrac12\|T_xf-f\|^2$ is the **increment**;
- **Krein's inequality** $(h_f(x)-h_f(y))^2\le 2h_f(0)\,(h_f(0)-h_f(x-y))$, the only regularity
  the theory ever uses: no derivative of $h_f$ and no spectral second moment;
- **lobes** $h_f=h_f^+-h_f^-$ with $0\le h_f^\pm\le h_f(0)$;
- **spectral density** $\rho=|\hat f|^2$ with $h_f(y)=\int\rho(\xi)\cos(2\pi\xi y)\,d\xi$ and
  total mass $\int h_f=(\int f)^2$.

A **grid source** at level $n$ is a compact continuous source with $h_f(\log k)=0$ for
$2\le k\le n+2$; the **blind cone** is the infinite-level version. A **clique** is a finite family
of shifts $t_i$ with $h_f(t_i-t_j)=0$ for $i\ne j$; under grid blindness every dyadic-odd coset
$\{\log(m2^k)\}$, $m$ odd, is a clique, because $\log n-\log m=\log(n/m)$ when $m\mid n$.

### 2.2 The archimedean weights and energies

| weight | formula | role |
|---|---|---|
| forward Lévy weight | $w_{\mathrm{arch}}(x)=e^{x/2}/\sinh x$ | the weight of $\mathcal J$; singular at $0$, $\sim 2e^{-x/2}$ at $\infty$ |
| dual weight | $w_{\mathrm{dual}}(x)=e^{-x/2}/\sinh x$ | image of $w_{\mathrm{arch}}$ under $x\mapsto-x$ (the functional equation) |
| secant core | $\operatorname{sech}(x/2)=1/\cosh(x/2)$ | smooth positive-definite part: $w_{\mathrm{arch}}=\operatorname{sech}(x/2)+w_{\mathrm{dual}}$ |
| half-angle split | $w_{\mathrm{arch}}=\tfrac{1}{2\sinh(x/2)}+\tfrac{1}{2\cosh(x/2)}$ | cosecant singularity plus secant |
| reciprocal weight | $1/w_{\mathrm{arch}}(y)=e^{-y/2}\sinh y\le y\,e^{y/2}$ | vanishes linearly at $0$: the price of transport |
| Lévy density | $e^{-x/2}/(1-e^{-2x})$ | the Lévy–Khintchine density of the Gamma phase rate |

The **Lévy energy** is $\mathcal J(f)=\int_0^\infty (h_f(0)-h_f(x))\,w_{\mathrm{arch}}(x)\,dx\ge 0$,
the **normalized energy** is $\mathcal J(f)/h_f(0)$, and the forward–dual split gives
$\mathcal J=\mathcal J_{\mathrm{sech}}+\mathcal J_{\mathrm{dual}}$ with both parts nonnegative.

### 2.3 Polar objects

The **polar density** is $2\cosh(x/2)=e^{x/2}+e^{-x/2}$. The **pole term** of a real source is
$2\bigl((\int f\cosh(u/2))^2-(\int f\sinh(u/2))^2\bigr)$, and for every real test
$\operatorname{weilArchRe}=\text{pole term}+\Omega(0)h_f(0)+\mathcal J(f)$. The **polar copy**
$f(u)-e^{-T/2}f(u-T)$ kills the positive exponential moment; the **symmetric copy**
$f(u)-\frac{1}{2\cosh(T/2)}(f(u-T)+f(u+T))$ kills both moments, preserves parity, multiplies
$h_f$ by $1+2b^2$ on any bounded window once $T$ is large, and changes the normalized energy by
$O(e^{-T})$.

### 2.4 The signed prime–polar measure and the hyperbolic gauge

With $L=\log(N+2)$ the **cutoff**:

- $\nu_N=\sum_{n\le N+2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}-2\cosh(t/2)\mathbf 1_{[0,L]}\,dt$;
  the **pairing** is $\langle h,\nu_N\rangle$, the **full pairing** its $N\to\infty$ form on the
  half line;
- the **signed packet** $P_f(u)=\int f(u+s)\,d\nu_N(s)$ and the **packet energy**
  $\|P_f\|^2=\iint h_f(s-t)\,d\nu_N(s)d\nu_N(t)$, which retains the prime–polar cancellation;
- the **normalized Chebyshev error** $\tilde E(t)=e^{-t/2}(\psi(e^t)-e^t)$ and the **gauge
  derivative** $f\mapsto f'-f/2=e^{u/2}(e^{-u/2}f)'$, the derivative in the hyperbolic gauge of the
  critical line;
- the **causal kernel** $K(x)=e^{-x/2}\mathbf 1_{x\ge0}$, the **causal response** $R_N=K\star\nu_N$,
  the **Laplace kernel** $e^{-|x|/2}=K\star\tilde K$, and the **Laplace energy**
  $\iint e^{-|s-t|/2}\,d\nu_N d\nu_N=\int R_N^2$;
- the **Fourier pairing** $\hat\nu_N(\xi)$ and the **spectral density**
  $S_N(\xi)=|\hat\nu_N(\xi)|^2/(\tfrac14+4\pi^2\xi^2)$, with the **band frequency** $\sqrt{N+2}=e^{L/2}$.

### 2.5 Hyperbolic multipliers

$(C_\alpha f)(u)=\cosh(\alpha u)f(u)$ and $(S_\alpha f)(u)=\sinh(\alpha u)f(u)$. They do not
commute with translation; they form a representation of the boost group $\mathrm{SO}^+(1,1)$;
$S_\alpha$ maps odd sources to even ones. The **Casimir** $(h_{C_\alpha f}-h_{S_\alpha f})/\cosh(\alpha x)=h_f$
is independent of $\alpha$.

### 2.6 Allocation objects

A **collar** is an interval $[t,t+y]$ or $[t-y,t]$ next to a node $t$. The **clique sphere
duality factor** of weights $w$ on a clique is $\sum_i w_i-\sqrt{\sum_i w_i^2}\ge 0$. A **physical
collar partition** assigns to each node a measurable nonnegative share of the physical interval
with exact mass conservation; its **coefficient** is the certified lower bound on the normalized
energy it produces. **Signed Gram certificates** keep every node correlation and every cross
entry of the translation packet, with no blindness assumption.

### 2.7 Producers

A **producer** is an explicit test or weight with an unconditional error bound, dual to the
receiver inequalities. The ones that recur: the **Nyquist polar constant** $\cosh(\tfrac12\log n)$
on the cell $[\log n,\log(n+1)]$; the **Taylor producers** of order $m$ for the weight $\cosh(\beta x)$;
the **Chebyshev factorial sum** $T(N)=\sum_{m\le N}\log m=\sum_{d\le N}\psi(\lfloor N/d\rfloor)$ and
its **bi-null stencils** $T(4N)-4T(2N)+4T(N)$ and $T(6N)-2T(3N)-3T(2N)+6T(N)$; the **factorial
lift** $\sum_{j\le K}e^{t/2}\mathbf 1_{[0,\log(K/j)]}$ and its compact continuous and causal
smoothings; in the Fermi–Nyman picture on $(0,1]$ the generators
$\varphi_a(t)=\{\tfrac1{at}\}-2\{\tfrac1{2at}\}$, the Haar target, the self-similar profile $s_0$
and the fold-free kernel $\ker P$.

### 2.8 The discrete side

**Coprime shear**: the multiplicative shift $(M_kv)(n)=v(kn)$, the additive step $(\Delta v)(n)=v(n+1)-v(n)$,
and the fact $\gcd(n,n+1)=1$. **Physical velocities** $q\in L^2(\mathbb R)$ with their locally
absolutely continuous primitives, logarithmic transport, **tent frames** at the multiples of a
divisor, **integer dilation** and its block aggregation. **Divisor-sieve signals**
$s_{N,c}(k)=\sum_{d\le N,\,d\mid k}c(d)$ on the period $N!$, their Selberg coordinates
$Y_{N,c}(e)=\sum_{e\mid d\le N}c(d)/d$, the **Ramanujan lag weight**
$c_e(h)=\sum_{d\mid\gcd(e,h)}d\,\mu(e/d)$, the **translated moments**
$\frac1{N!}\sum_{n<N!}\prod_i s_{N,c}(n+h_i)$, the **affine moments**
$\frac1{N!}\sum_k s_{N,c}(k)s_{N,c}(ak+b)$, the **top dyadic order** $2^{\lfloor\log_2N\rfloor}$,
**visibility** of a mode from a support through zero-sum frequency words of length five or six,
and **local pairwise Hölder stability** of exponent $\alpha$: recovery of the signal up to one
translation with error $C\varepsilon^\alpha$ from fifth and sixth arrays within $\varepsilon$.

### 2.9 Glossary

| object | Lean |
|---|---|
| autocorrelation, Lévy weight, Lévy energy, normalized energy | `autocorr`, `archLevySinhWeight`, `biScaleLevyEnergy`, `normalizedArchEnergy` |
| dual weight, secant weight, Lévy density | `archDualLevySinhWeight`, `archSechHalfWeight`, `archLevyDensity` |
| grid source, infinite-grid energy source | `LogarithmicGridSource`, `InfiniteGridEnergySource` |
| polar density, polar copy, symmetric copy | `polarDensity`, `polarCopy`, `evenPolarCopy` |
| prime weight, cutoff, pairing, full pairing | `primeWeight`, `cutoff`, `SignedPrimePolar.pairing`, `fullPairing` |
| signed packet, packet energy | `signedSource`, `packetEnergy` |
| normalized Chebyshev error, gauge derivative | `normalizedLogError`, `gaugeDerivative` |
| causal response, Laplace energy, Fourier pairing | `causalResponse`, `laplaceEnergy`, `fourierPairing` |
| hyperbolic multipliers | `coshMultiplier`, `sinhMultiplier` |
| clique sphere factor, collar partition | `cliqueSphereDualityFactor`, `PhysicalCollarPartition` |
| Nyquist polar constant, Taylor residual kernel | `nyquistPolarConstant`, `nyquistWeightKernel` |
| Chebyshev stencil producers | `chebyshevAlternatingProducer`, `chebyshevBiNullProducer`, `coprimeTwoThreeChebyshevProducer` |
| factorial lift, factorial sources | `factorialLift`, `factorialSourcePlus`, `factorialMuntzCompletion` |
| coprime shear | `mulShift`, `addShift`, `addDiff` |
| Ramanujan lag weight, period covariance | `ramanujanLagWeight`, `periodCovariance` |
| translated and affine moments | `translatedMoment`, `affineMoment` |
| visibility, local stability, top order | `Visible`, `LocalPairwiseHolder`, `TopAnchor.topOrder` |

---

## 3. How: the mechanisms

### 3.1 Krein geometry on the cone

Everything starts from the chord metric. The Peter–Paul inequality
$h(0)-h(x+y)\le(1+t)(h(0)-h(x))+(1+1/t)(h(0)-h(y))$ gives the subadditive triangle law
$\sqrt{h(0)-h(x+y)}\le\sqrt{h(0)-h(x)}+\sqrt{h(0)-h(y)}$, hence **doubling** $h(0)-h(2x)\le 4(h(0)-h(x))$,
the multiple law with $m^2$, and the **dyadic cascade** with $4^k$. At any node where $h(x_0)\le0$
every harmonic subdivision satisfies $h(0)-h(x_0/m)\ge h(0)/m^2$. These are derivative-free
and are the only way the theory ever moves information from one lag to another.

### 3.2 Bessel spheres, origin leverage, and the folded collar

A clique $\{t_i\}$ makes the translates $f(\cdot+t_i)$ an orthogonal frame of norm $\sqrt{h(0)}$,
so for every $y$ the **collar vector** $u_i=h(y-t_i)$ lies in the ball $\sum_iu_i^2\le h(0)^2$;
adjoining the origin gives $h(y)^2+\sum_i h(t_i\pm y)^2\le h(0)^2$. The exact convex dual of the
ball is the **clique sphere duality**
$$
\sum_i w_i\,(h(0)-h(y-t_i))\ \ge\ \Bigl(\sum_i w_i-\sqrt{\textstyle\sum_i w_i^2}\Bigr)h(0),
$$
attained on the extremal ray $u_i\propto w_i$; for $M$ equal weights the per-node defect fraction
is $1-1/\sqrt M$. **Origin-singularity leverage** adds an origin weight $W_0$:
$$
W_0(h(0)-h(y))+\sum_i w_i(h(0)-h(t_i\pm y))\ \ge\ \Bigl(\sum_i w_i-\frac{\sum_i w_i^2}{2W_0}\Bigr)h(0),
$$
and since $w_{\mathrm{arch}}(y)\sim1/y$ the Lévy energy supplies $W_0\to\infty$ at small offsets,
so the whole collar weight transfers into a lower bound on $\mathcal J$. The multi-node exact
completion of squares behind this needs no blindness: with signed node values it reads
$W_0(h(0)-h(y))+\sum_iw_i(h(0)-h(t_i\pm y))+\sum_iw_ih(t_i)\ge(\sum_iw_i-\sum_iw_i^2/2W_0)h(0)$,
and the off-diagonal Gram sum $\sum_{i\ne j}w_iw_jh(t_i-t_j)$, which for a dyadic coset involves
only prime-two-power correlations, is the exact price of sharing one origin collar among many nodes.

A single zero $h(t_1)=0$ does not bound $h(0)-h(x)$ at an isolated $x$: the sphere
$h(x)^2+h(t_1-x)^2\le h(0)^2$ lets $h(x)\to h(0)$ provided $h(t_1-x)\to0$. It does bound the
**reflected pair**, $w_L(h(0)-h(x))+w_R(h(0)-h(t_1-x))\ge(2-\sqrt2)\min(w_L,w_R)h(0)$, so folding the
Lévy integral about $t_1/2$ gives a strictly positive derivative-free lower bound on $\mathcal J$
from one grid zero.

### 3.3 Nyquist absorption and the all-scale critical-line weight

On the cell $[\log n,\log(n+1)]$, $\sinh y<1/n$ for $y\le\delta_n$, so $n\le w_{\mathrm{arch}}(y)$ and
$$
\int_0^{\delta_n}(h(0)-h(y))\,dy\ \le\ \frac1n\int_0^{\log2}(h(0)-h(y))\,w_{\mathrm{arch}}(y)\,dy .
$$
The origin collar $(0,\log 2]$ and the tail $[\log 2,\infty)$ are disjoint, so a dyadic window and
its origin charges together cost **one** copy of $\mathcal J$. Sharing the origin across all
scales at once uses the **canonical weight** $\varpi_n=\sqrt2\,n(n^{-1/2}-(n+1)^{-1/2})\le 2/\sqrt{n+1}\le w_{\mathrm{arch}}(\log(n+1))$:
with $w_n=W_{0,n}=\varpi_n$ the coercive coefficient is exactly $\varpi_n/2$, and the origin shares
$\varpi_n/n=\sqrt2(n^{-1/2}-(n+1)^{-1/2})$ telescope to at most $1$. This is where $\sigma=\tfrac12$
is used: the share is $n^{-1/2}\cdot n^{-1}=n^{-3/2}$, summable. Multiplying by
$\theta_\Lambda(n)=\Lambda(n)/\log n\in[0,1]$ gives $w_\Lambda(n)=\theta_\Lambda(n)\varpi_n$ with
$w_\Lambda-w_\Lambda^2/2\varpi_n\ge w_\Lambda/2$, hence, for every real even polar test $g$ and every $N$,
$$
\bigl(\Omega(0)+\mathcal C_{\Lambda}(N)\bigr)h_g(0)\ \le\ \operatorname{weilArchRe}(g)+\sum_{n=2}^{N+1}\delta_n\,w_\Lambda(n)\,h_g(\log n),
$$
with an explicit $\mathcal C_\Lambda(N)>0$ supported on prime powers. The same absorption gives
derivative-free Euler–Maclaurin cell quadrature: the error of replacing $\int_t^{t+\delta}\rho h$
by $(\int\rho)h(t)$ is bounded by an origin collar integral plus $h(0)\int\rho^2/2W_0$.

### 3.4 Polar enforcement and what the infinite grid detects

Polar balance is cheap to impose and expensive to hide. A distant copy enforces it at normalized
energy cost $O(e^{-T})$, so **polar and non-polar finite-grid classes have the same infimum** at
every regularity order, for even sources as well through the symmetric copy; finite exponential
moments never change the grid energy infimum. But the infinite grid sees the copy: the node
$\log\lceil e^T\rceil$ lies within $e^{-T}$ of $T$, samples the copy's correlation near its own
origin, and forces a translation defect; a separated copy that keeps its grid sample pays energy
linear in $T$. Under a quadratic origin collar $h(0)-h(y)\le Ky^2$, Nyquist compression forces
$\int_{\log N}^{\log 2N}h^2\le 2Kh(0)/N^2$, while $\int\cosh(x/2)^2$ on the window is $O(N)$, so
negative polar mass $\mu$ placed in the window costs $N\mu^2\le 4\log2\,K\,h(0)$: **distant lobes
pay linearly in $e^T$**. Compressing a seed to radius $\asymp1/N$ and hiding its copy at the
midpoint $\tfrac12(\log N+\log(N+1))$ realizes all grid zeros and polar balance at normalized
energy $\asymp\log N$, and **width rigidity** says this is forced: $w_{\mathrm{arch}}\ge e^{-r_2/2}/x$
on $(0,r_2]$, so a correlation that is nonpositive on $[r_1,r_2]$ costs at least
$e^{-r_2/2}\log(r_2/r_1)h(0)$; a bounded-energy source cannot be compressed into a far gap.

For finite coefficient trains on a common seed with separation at least two, a smooth all-grid
source exists exactly when every active positive lag misses the grid, and then the normalized
energy is pinned between $c\log(1/d_{\min})$ and $C-\log d_{\min}$ in the smallest active grid
distance. Bounded-energy blind correlations are relatively compact in the supremum norm, every
limit keeps the grid and finite energy, and a convergent energy defect sits entirely at the
origin; the grid, energy and polar topologies are pairwise distinct, with smooth witnesses.

### 3.5 Linear Krein smoothing and the logarithmic modulus

Krein controls an increment only by the square root of an origin increment. Averaging over a lag
progression removes the root: for $Sh(x)=m^{-2}\sum_{i,j<m}h(x+(i-j)\lambda)$, the profile $h-Sh$
is positive definite, so $|h(x)-Sh(x)|\le h(0)-Sh(0)$, and $Sh$ moves by at most $2h(0)/m$ per lag
step. With the singular energy paying the averaged origin defect this gives, for every compact
$C^2$ source, the **linear logarithmic modulus**
$$
\log\frac1{|x-y|}\;|h(x)-h(y)|\ \le\ 32\sqrt e\,\mathcal J(f)+2h(0),
$$
sharp in both the rate and the linear energy dependence (modulated bumps have
$\mathcal J+h(0)\le 8\log(1/d)(h(0)-h(d))$). On the integer-log blind cone this is the
inverse-linear tail $T|h(T)|\le 32\sqrt e\,\mathcal J+2h(0)$ with square-integrable tails
$\int_T^\infty h^2\le(32\sqrt e\,\mathcal J+2h(0))^2/T$; a node in every window $(e^T,e^T+e^{\theta T}]$
gives $(1-\theta)T|h(T)|$ on the same right side, and the corpus's unconditional Hoheisel exponent
$\theta=71/100$ makes this a law for every source blind at the logarithms of the primes.

In the Beurling–Turán window the clique argument gives
$\int_0^{(M+1)\delta}h\le\delta\sqrt{M+1}\,h(0)$ when $h(m\delta)=0$ for $1\le m\le M$; the true
order is logarithmic, $|\int_0^{(M+1)\delta}h|\le 12\delta(4+\log(M+1))h(0)$, because the zeros
make every spectral Dirichlet energy flat, $\int\rho(\xi)D_{M+1}(\theta-2\pi\delta\xi)=(M+1)h(0)$ for
every phase, which caps the spectral mass of each arc of length $\asymp1/(M\delta)$ and turns the
window kernel into a harmonic sum.

### 3.6 Hyperbolic multipliers and the odd sector

For every source and every $\alpha,x$,
$$
h_{C_\alpha f}(x)-h_{S_\alpha f}(x)=\cosh(\alpha x)\,h_f(x),\qquad
\bigl(h_{C_\alpha f}(0)-h_{C_\alpha f}(x)\bigr)+2\sinh^2(\tfrac{\alpha x}2)h_f(0)=\cosh(\alpha x)(h_f(0)-h_f(x))+\bigl(h_{S_\alpha f}(0)-h_{S_\alpha f}(x)\bigr),
$$
both right-hand terms nonnegative, and the **light cone**
$h_{C}^2-h_{S}^2=\cosh(\alpha x)h_f(h_C+h_S)$ with $h_f(x)=0\iff h_C(x)=h_S(x)$. At $\alpha=\tfrac12$
the secant core is $h_f\operatorname{sech}(x/2)=(h_C-h_S)/\cosh^2(x/2)$, which ties the odd-sector
functionals (secant energy and the plastic crossover) to multiplier Gram energies.

Source blindness does not transfer to the multiplier: an odd train of six separated packets has
$h_f(\log2)=0$ while $h_{S_\alpha f}(\log 2)$ grows like $e^{2\alpha T}$. The remedy is never to assume
multiplier zeros: use signed collar leverage on $C_\alpha f$ and $S_\alpha f$, control the
multiplier defect by source Gram data on node differences, project the difference packet off the
source (a Schur residual), and bound arithmetic collision energy of equal pair differences.
Coherent packets then reduce the odd hyperbolic moment penalty to a **coherent price** whose best
universal coefficient on the odd hyperbolic class is $\log 2$, attained by inverse-hyperbolic
images of two symmetric tents; a finite symmetric filter realizes the coherent slope with
coefficient square sum $13/9$ in place of $2$, the gain is strict exactly off the even sources,
and the folded sinh source's cell variance is the exact remaining slack.

### 3.7 Collar allocation as convex optimisation

The collar coefficient of §3.2 is a concave functional of a physical partition, and the theory
treats it as such. Equal-multiplicity shares are an explicit inhabitant; supporting prices of the
shared-origin block norm give a nonnegative comparison remainder that splits into radial curvature
and block-direction terms, so a trial partition certifies its own distance to the optimum; Hilbert
coordinates on the share space give weak compactness and **attainment** of the physical optimum
without any assumed compactness. The optimum is monotone in the grid cutoff and loses at most the
physical tail mass under retraction; the leading tail is exactly $4/\sqrt N$ with an inverse-cutoff
remainder. Paired-sign spheres (every block of one sign shares a sphere with every block of the
other, once grid zeros reach $K^2$) strictly beat independent blocks, the delayed paired
hierarchy saturates at the fourth root of the cutoff, and capped low-node coupling keeps every
high node. With the full signed Gram matrix retained, cutoff error is at most twice the source
energy times the retention tail, and a finite minimum-price iteration with step $2/(t+2)$ reaches
any prescribed accuracy in a source-independent number of steps. One fixed smooth source realizes
the anchored dyadic Gram minimum $1/(m+1)$ at cutoff $2^m$, with triangular weights attaining it.

### 3.8 Signed prime–polar transport

To compare $\sum\Lambda(n)n^{-1/2}h(\log n)$ with $\int 2\cosh(x/2)h$ without derivatives: average
$h(t+y)$ over an annulus $y\in[e^a,e^a+e^b]$, which is $C^1$ with explicit derivative for any
continuous compact source; integrate by parts in the Stieltjes sense against $\psi(e^x)$, which
turns the prime sum into **Chebyshev work** against $\psi(e^x)-e^x$ plus endpoint values; and pay
the local transport with Krein's inequality and the reciprocal weight $e^{-y/2}\sinh y$. Replacing
unsigned mass by the signed packet keeps the prime–polar cancellation in the cost; a collar source
supplies its own regularity so that compact continuous sources are admitted; an optimal scalar
collar compensation is computed from the source covariance; the whole half line is admitted from a
cutoff built from the source alone. On the full real Weil test space the pole term at weight one
is absorbed identically as the continuum part of the pairing, so the untruncated Weil functional is
$\Omega(0)h(0)+\mathcal J-2\,\text{fullPairing}(h)$ for every parity.

### 3.9 The hyperbolic gauge and the square-root barrier

For a compact $C^1$ source and $L=\log(N+2)$, Stieltjes summation against $\psi(e^t)$ gives the
exact representation
$$
P_f(u)=f(u)-\int_0^Le^{-t/2}f(u+t)\,dt+\tilde E(L)f(u+L)-\int_0^L\tilde E(t)\,(f'-f/2)(u+t)\,dt ,
$$
so the arithmetic content of every packet sits in $\tilde E$, and the convolution energy is the
quadratic form of $\tilde E$ against the positive-definite kernel $h_{f'-f/2}$. Young's inequality
gives two-sided control between packet energy and $\int_0^L\tilde E^2$ up to source constants. On
the cell $[\log n,\log(n+1))$, $\psi(e^t)=\psi(n)$ and
$$
\int_{\log n}^{\log(n+1)}\tilde E^2=\frac{(\psi(n)-m_n)^2}{n(n+1)}+c_n,\qquad
m_n=n(n+1)\log\tfrac{n+1}{n}\in[n,n+1],\quad 0\le c_n\le\tfrac{2}{n(n+1)},
$$
so $\int_0^{\log M}\tilde E^2$ is the weighted mean square $\sum_{n<M}(\psi(n)-m_n)^2/(n(n+1))$ up to
an additive $2$.

The causal response is explicit, $R_N(t)=\tilde E(t)+(1-t)e^{-t/2}$ on $[0,L]$, zero before, decaying
as $e^{-(t-L)/2}R_N(L)$ after; hence $\text{laplaceEnergy}=\int_0^LR_N^2+R_N(L)^2$ and
$\int_0^L\tilde E^2$ control each other up to a factor $2$ and constants. Plancherel gives the
spectral form $\int|\hat\nu_N|^2/(\tfrac14+4\pi^2\xi^2)$ with
$\hat\nu_N(\xi)=\sum_{n\le N+2}\Lambda(n)n^{-s}-\frac{e^{(1-s)L}-1}{1-s}-\frac{1-e^{-sL}}{s}$ at
$s=\tfrac12+2\pi i\xi$. The Montgomery–Vaughan mean value theorem bounds the atomic part's mean
square on $[-u,u]$ by $2uD_1+208D_2$ with $D_1=\sum\Lambda(n)^2/n$, $D_2=\sum\Lambda(n)^2$, and one
integration by parts against $1/u^2$ gives an explicit $O(L)$ bound for all frequencies
$|\xi|\ge\sqrt{N+2}$: **the barrier lives entirely in the band** $|\xi|<\sqrt{N+2}$. The
discrepancy transform law $\hat\nu_N=s\int_0^L\tilde E\chi_\xi+\tilde E(L)\chi_\xi(L)+1-(1-e^{-sL})/s$
shows that a sharp window on $\tilde E$ creates an endpoint jump of height $\tilde E(L)$ whose
high-frequency energy is $\asymp\tilde E(L)^2/\xi_0$; the band-limited object is the Laplace energy,
not the windowed Chebyshev energy.

The exponential kernel is Markov, so sampling $R_N$ at a geometric ladder $t_k=kh$ gives the
**renewal chain** $x_{k+1}=e^{-h/2}x_k+r_k$ driven by normalized block discrepancies
$r_k=e^{-(k+1)h/2}\bigl((\psi(e^{(k+1)h})-\psi(e^{kh}))-(e^{(k+1)h}-e^{kh})-h\bigr)$; the window
energy is equivalent, with explicit constants, to $\sum x_k^2$ plus the fine block energies, the
Schur test gives $\sum x_k^2\le(1-q)^{-2}\sum r_k^2$, and the fine energy on $[X,2X)$ is the
in-block variance of the integer error $\psi(n)-n$ normalized by $X^3$. At $h=\log 2$ the blocks
are dyadic and $q=1/\sqrt2$. The window energy is also an exact finite quadratic form in the values
$\psi(n)$ with coefficient $1/(n(n+1))$ on $\psi(n)^2$. At zero frequency,
$\sum_{n\le N+2}\Lambda(n)/\sqrt n-4\sinh(L/2)=\tfrac12\int_0^L\tilde E+\tilde E(L)-1+2e^{-L/2}$.
The Fermi–Nyman generators on $(0,1]$, under $t=e^{-u}$, are dyadic block bricks of this gauge
space, and they pair with $\nu_N$ to exactly the coarse dyadic block discrepancies.

### 3.10 Producers

Receivers rewrite the explicit formula; producers bound it. The theory insists on both.

- **Chebyshev stencils.** $T(N)=\sum_{m\le N}\log m$ is smooth to $O(\log N)$ by Stirling, and
  $T(N)=\sum_{d\le N}\psi(\lfloor N/d\rfloor)$ is the floor sum of $\psi$. Any bi-null stencil kills
  both the $N\log N$ and the $N$ terms without introducing Dirichlet's divisor sum:
  $T(2N)-2T(N)=(2\log2)N+O(\log N)$, $|T(4N)-4T(2N)+4T(N)|\le 5\log(4N+1)+1$, and for the coprime
  pair $(2,3)$, $|T(6N)-2T(3N)-3T(2N)+6T(N)|\le 12\log(6N+1)+2$. The bi-null producer is the
  logarithmic excess of the doubled central binomial coefficient, between $\tfrac12\log(N+1)$ and
  $\tfrac12\log(N+1)+O(1)$.
- **Factorial lift.** The rectangle $e^{t/2}\mathbf 1_{[0,a]}$ pairs to $(\psi(e^a)-e^a)+1-a$, and
  the lift $\sum_{j\le K}$ at $a=\log(K/j)$ pairs to $2\log K!-K\log K-KH_K+K$, in which the
  $K\log K$ terms cancel identically; the divisor-sampled causal response
  $\sum_{j\le K}\sqrt{K/j}\,R_N(\log(K/j))$ lies in the linear channel $[-2K,-K+2\log(K+1)+2]$ and
  its $(1,-4,4)$ stencil is bounded by $10\log(4K+1)+3$. Compact continuous and causal smoothings
  keep every integer-grid value and have full pairing $O(\log N/\sqrt N)$.
- **Compact factorial sources.** The ramp–tent pair has Lipschitz and jump-energy bounds that
  admit it to the spectral Weil form without two derivatives; on it the literal Weil energy is
  coercive with normalized energy tending to infinity logarithmically, the mixed ramp–tent
  coefficient decays like $\log n/\sqrt n$, and the polar loss has asymptotic coefficient $\tfrac14$
  and dominates the Gram error.
- **Müntz completion.** The factorial ramp is the positive-logarithmic restriction of an explicit
  arithmetic sum whose Mellin transform vanishes at every zeta zero with positive real part. The
  omitted tail is exactly the negative-logarithmic part; after the unique polar correction it has
  a uniform envelope $12(n+1)^{-1/2}e^{-3|x|/2}$, its prime and pole costs are $O(1/(n+1))$ times its
  mass, but its archimedean energy grows like $\tfrac12\log(n+1)$ times its mass: the smoothed
  correction tails have **unbounded normalized Weil energy**.
- **Nyquist polar producers.** $\cosh(\tfrac12\log n)$ approximates $\cosh(x/2)$ on its cell with
  $L^2$ error $\le1/(16n^2)$, $\le 1/(16N)$ over a dyadic window, and the all-tail residual is an
  explicit positive bounded operator. Taylor producers of order $m$ for $\cosh(\beta x)$ have an
  integrable residual kernel exactly when $\beta<m+1$, with sharp tail mass; at the critical order
  $\beta=m+1$ the cell masses diverge logarithmically and the **critical finite part**
  $\mathcal B_m=\sum_k d_k(m)$ with $|d_k|\le D_m(k+1)^{-2}$ is the renormalized limit, with nodal rate
  $2D_m/(N+1)$. Wide sources attain the residual norm under every energy ceiling; the diffuse
  ternary train has correlation error $1/(n+2)$, convergent energy and divergent polar moment.
- **Compensated physical producers.** Every physical velocity $q\in L^2$ has, at scale $n$, a
  compensated truncation $v_n$ with $\int v_n=0$, $\|v_n\|^2\le(1+e^{-(n+1)})\|q\|^2$, and a compact
  $C^1$ logarithmic state with exact weighted Dirichlet energy; the negative physical half line is
  invisible to the logarithmic primitive.

### 3.11 Coprime shear and the Sobolev side

The dilated additive step telescopes, $v(k(n+1))-v(kn)=\sum_{j<k}\Delta v(kn+j)$, so by Cauchy–Schwarz
$\sum_{n<N}(v(k(n+1))-v(kn))^2\le k\sum_{m<kN}(\Delta v(m))^2$: multiplicative energy is additive
energy times the scale. Because $\gcd(n,n+1)=1$, a state supported on the multiples of $d\ge2$
vanishes at both neighbours of every active node and pays $(v(n)-v(n-1))^2+(v(n+1)-v(n))^2=2v(n)^2$.
Taking the modulus of a sign-changing state drops the cross collar $4f^+(u)f^-(u+x)$; the theory
keeps it as an exact nodal loss and transfers it to path slack.

In the continuum, primitives of $L^2$ velocities have weighted logarithmic energy
$\int e^{-x}(f')^2$, the edge from $x$ to $x+\log(n+1)$ has resistance $ne^x$, path congestion
transports jump energy of mixed diffuse and arithmetic edge measures to the additive density with
exact slack, compact source graphs admit every velocity, the diffuse kernel controls the weighted
variance across components, and modulus and clamp are firm contractions with an exact nodal loss
that is an explicit multiple of the product of the two lobe masses. Tent velocities at the
multiples of a divisor form an isometric frame whose adjoint reads centred second differences; the
coprime projections form an arithmetic lattice (intersection at the lcm), the reduced product of
two projections has square $\tfrac14$ of itself ($\tfrac12$ when a spacing is two), alternating
projections converge at that exact rate, and a divisor family has closed trace range exactly when
its active runs are bounded, with the sharp sine constants attained. Integer dilation on
velocities is a block aggregation with explicit coisometry and convergent block variance; the
physical affine commutator has sharp norm with deficit $2|a|/(n+1)$ realized by alternating cells
and not attained.

### 3.12 Arithmetic observation theory

The complete-period centred covariance of a divisor-sieve signal at additive lag $h$ is diagonal
in the Selberg coordinates with eigenvalue the Ramanujan sum $c_e(h)$, the unique weight with
$\sum_{e\mid g}c_e(h)=g\mathbf 1_{g\mid h}$; at $h=0,1,2$ it is $\varphi,\mu,$ and the lag-two
eigenvalue, and simultaneous additive periodicity and dilation invariance force a constant. The
joint $(\varphi,\mu,\lambda_2)$ cone has five rays, realized by finite weights.

Observation proceeds by degree. **Affine moments** recover exactly the products $Y(e_1)Y(e_2)$ on
divisibility edges, leaving one sign per component of the divisibility graph; modes $3$ and $5$
show the ambiguity at every cutoff. **Odd moments** vanish on parity-lifted weights with the
antiperiod $15$, and sixth moments recover the relative sign of $\{6,10\}$ through the cross term
$960a^3b^3$; all data through degree five are blind to it. **Valuation classes** organise the rest:
within a two-adic order class primitive triples sum to a common frequency and the sixth moment
aligns the class up to one sign; across classes a quintic resonance reads the cube of the lower
coordinate times the square of the higher; the remaining ambiguity after all fifth and sixth
moments is exactly one **canonical translation**, by the odd part of the period, which reverses the
greatest active two-adic class, and labelled affine moments remove it exactly when an active edge
joins the highest class to a lower one. For arithmetic edge families on $2pq$ with pairwise coprime
odd blocks the fourth array is equivalent to coordinate squares plus triangle and four-cycle
equations, and the ambiguity is $2^{\text{nullity}}$ of an explicit binary code. For finite families
at twice odd primes a fixed protocol of $64M^2$ raw sixth moments recovers the vector up to common
sign, an adaptive one uses $128M-64$, and no protocol with fewer observations than coefficients can
(invariance of domain).

Stability is sharp and stratified. Normalized sixth readouts recover with exponent $1/6$ at zero
and $1/3$ on a nonzero-mass stratum, both optimal. With a nonzero coordinate at the top dyadic
order $2^{\lfloor\log_2N\rfloor}$, fifth and sixth arrays within $\delta^3$ give recovery up to one
translation with error $2(\sum_{q\le N}\varphi(q))\delta$: cube-root stability, sharp already at
cutoff three. In a neighbourhood of the pure parity source the first sign-sensitive degree is
$1,3,5,6$ according to the cutoff ($N=2$, $N<12$, $N<20$, else), the local exponent is its
reciprocal, and both are attained and maximal. First-order visibility of a mode from the active
support (a zero-sum word of length at most six with the mode occurring once) gives local Lipschitz
recovery, and every mode of prime-factor width at most five is visible from the prime powers.
Squarefree-supported rows, hence every Möbius taper, have zero top dyadic coordinate for $N\ge4$;
visibility from a squarefree support is closed under squarefreeness, so with $N\ge 9$ no exponent
above $1/3$ holds for any such row, while any retained even anchor still gives cube-root recovery
of the odd modes.

Coercivity of the joint additive–multiplicative energy on integer windows has sharp doubling
scale: every window $N\ge1024$ carries a doubling-resonant cosine with energy at most $384$ and
variance at least $N/16$, so a valid constant is at least $N/6144$ while $6N$ always works, and no
constant is valid on all windows for a fixed finite dilation horizon.

### 3.13 Bridges

The field speaks to the other graphs of the corpus in its own coordinates. On the causal
hyperbolic–modular source graph: five-term nodal-lobe jump bounds, the balanced nodal graph with
its three-term nonnegative prime-shift form, Beurling–Deny Markov positivity of the stationary
resolvent, $\cosh(x/2)$-decaying ground potential bounds, the chiral Euler–Poisson drift identity
and prime-shift rigidity under weight perturbation, and the mass and edge kernels of the prime
clocks, which retain their centre $\log(N/q)$ and lag $\log(q/p)$. On the Fermi–Nyman side: the
centred Bernoulli sawtooth and its exact sign flip, the multi-octave step-brick partition and
single-cell combinators, Vasyunin's exact global-minus-head tail Gram, witness transfer of every
bulk cell into the origin tail, the Selberg $\Lambda^2$ tail form, the lossless signed lcm defect
with its successor recurrence, the $\ker P$ projection, and the Barban–Vehov logarithmic pinch.
On the sieve side: large-value level sets and Halász $L^1$ bounds on the atomic polynomial, the
Vinogradov–Korobov rate for the Chebyshev sequences, the Ramaré ladder with discharged
Halász–Montgomery–Huxley steps, Watt and Heath-Brown mean values, prime-log Rajchman clocks,
Hurwitz anchor contact, the squarefree discrepancy carriers, and the valuation core of Robin
counterexamples.

---

## 4. Traps and sharp boundaries

| trap | correct statement |
|---|---|
| Bounding by the spectral second moment $S(f)=-h''(0)$ or by $\Omega(0)$ alone. | Discards $\mathcal J$; grid constraints become invisible as $S(f)/h(0)\to\infty$. Bound increments by $\mathcal J$ through Krein's inequality. |
| Subtracting a translation-invariant mean field. | Cannot distinguish $\Lambda_{\log}$ from a shifted continuum; the node positions must enter the cone. |
| Applying $f\mapsto\lvert f\rvert$ to a sign-changing state. | Drops the cross collar $4f^+(u)f^-(u+x)$; keep the nodal loss and move it to slack. |
| One zero bounds the increment at one interior point. | At $x=\tfrac45\log2$ a pulse train has $h(\log2)=0$ and $(h(0)-h(x))/h(0)\to0$; only the reflected pair is bounded, so fold the interval. |
| Finitely many grid zeros plus polar balance. | A distant copy enforces balance at cost $O(e^{-T})$; only the infinite grid forces linear cost in $e^T$. |
| Commutative Bochner or Beurling reasoning. | Translation inner products see only divisibility, shared with Beurling systems off the line; use the successor coupling and non-commuting multipliers. |
| Source blindness implies multiplier blindness. | False: the odd six-packet train. Use the light cone and signed collar leverage on $C_\alpha f$, $S_\alpha f$. |
| Compressing support into a midpoint gap. | Costs $\asymp\log N$ normalized energy; width rigidity forbids it at bounded energy. |
| Working only on the blind subspace. | Multiplies $\Lambda(n)/\sqrt n$ by zero and cannot see off-line countermodels; state theorems for signed correlations. |
| Receiver-only reformulations; subtracting the counterterm before the floor sum. | The second replaces $T(N)$ by Dirichlet's divisor sum with $O(\sqrt N)$ noise. Build producers with unconditional bounds. |
| "The clique window bound is sharp." | $\int_0^{(M+1)\delta}h\le\delta\sqrt{M+1}h(0)$ holds but the true order is $\log M$. |
| Squared or finite-order closed-cycle data determine polar balance. | Polar-attenuated opposite copies share all squared correlations and all closed products through any fixed order; recovery needs all orders, or energy-controlled cycles with explicit mesh. |
| The local cube-root classification applies to Möbius rows. | It needs a nonzero top dyadic coordinate; squarefree rows have none for $N\ge4$, and a prime anchor does not transfer the argument. For $N\ge9$ no exponent above $1/3$ holds for them. |
| Witness factors are recovery constants. | The $(N!)^6$ factors in sharpness witnesses bound particular moments; the recovery constants are $2+2\sum\varphi(q)$ and depend on $N$; all observations are full-period moments, not polynomial-horizon ones. |
| Positivity on the whole source graph. | The constant lift has energy $-c^2/2$; a positivity target must name its odd or otherwise constrained family. |
| Windowed Chebyshev energy is band-limited. | The sharp window creates the jump $\tilde E(L)$ with energy $\asymp\tilde E(L)^2/\xi_0$; the Laplace energy is the band-limited object. |
| A bound for the compact factorial source bounds its completion. | The omitted Müntz tail has unbounded normalized Weil energy. |
| Coherent price controls source energy. | A nonzero kernel family has zero coherent price and arbitrary energy. |
| Prime clock kernels are lag-only. | They retain the centre and cutoff; no translation invariance or sign of edge minus mass is proved. |

**Lean conventions.** Even polar tests are nested subtypes, so plain `linarith` or `nlinarith`
with such a term in context stalls; use `linarith only [...]` and call namespace theorems
explicitly rather than by dot projection. Inside the field's namespaces `open RHTower` resolves to
the field's own `RHTower` namespace; write `_root_.RHTower.…` for the root one. Capstones are stated
on data parameters; theorems that conclude `RiemannHypothesis` are implications or equivalences
whose premise is one explicit energy bound, never asserted. Analytic inputs (Mertens, Chebyshev,
Vinogradov–Korobov, Hoheisel, Montgomery–Vaughan) are proved corpus theorems.

---

## 5. The frontier

**The band.** In the field's coordinates the square-root barrier is
$\int_0^L\tilde E^2=O(L)$, equivalently $O(L)$ energy of $\nu_N$ in the band $|\xi|\le\sqrt{N+2}$,
equivalently stabilization of the packet energy over compact $C^1$ sources up to source
constants. Everything outside the band is bounded; the band is RH in both directions, and the
direction from RH to the band (Cramér's mean square) is not in the corpus either. What a mechanism
must do: fail for Beurling systems, survive the degenerate point of one character and modulus one,
carry information beyond polynomial length equal to height at square-root precision, and separate
$\log4$ from $\log6$. Additive tools do the first and third only after averaging over a family;
multiplicative tools are Beurling-invariant.

**The blind cone.** Blind geometry is now controlled: inverse-linear tails, square-integrable tails,
prime-gap transfer, logarithmic window law, compactness and origin concentration of energy defects.
Open: the infimum of $\mathcal J/h(0)$ on the blind polar class against $|\Omega(0)|$; whether the polar
constraint improves the single-prime dyadic bathtub when only the powers of two are blind; whether
the logarithmic window law is attained.

**The odd sector.** The coherent price $\log 2$ is sharp and the finite-filter gain is strict, but
the full odd Weil sign is not proved; at pole weight one the odd bound retains a positive
$\sinh$-moment cost.

**Arithmetic observation.** All recovery theorems observe full-period moments; polynomial-horizon
recovery with constants independent of $N$ is open. A common organizing theorem for the two
halves exists only as a classification by sign characters of the subgroup generated by the
support; the quantitative version through bounded-length relations, with energy and realization
costs on both sides, is open. Stability off the strata (vanishing top coordinate, changing
support) and a stable mixed-stratum formulation are open.

**Producers.** The Müntz correction tail shows that the compact factorial family cannot be
completed inside the decay-class Weil domain at bounded normalized energy; a producer family with
bounded completion cost, or a proof that none exists, is open. For the prime clocks the arithmetic
estimates for the mass and edge kernels and the sign of their difference are open.

---

## 6. Working in the theory

- **Never differentiate the correlation.** Every bound goes through Krein's inequality or its
  linear smoothing and is paid by $\mathcal J$; the spectral second moment is never admissible.
- **Keep the signs.** Signed node values, signed packets, signed Gram entries; blindness is a
  sharpness check, not a hypothesis. A theorem on the blind cone must say so.
- **Say which regime.** Finite grid or infinite; compact source, $C^1$, $C^2$, or decay class;
  period moments or finite horizon; polar or non-polar; even, odd, or arbitrary parity. The
  infima and the sharp exponents change with each.
- **Receivers come with producers.** Do not add a reformulation of the explicit formula without an
  explicit test, weight or stencil whose error is bounded unconditionally.
- **Test against Beurling and against the degenerate point.** If the mechanism would hold for a
  generalized number system, or needs a family average to work, it cannot close the band.
- **Use the gauge dictionary.** For any statement about packet energy, pass through the hyperbolic
  gauge: the arithmetic sits in $\tilde E$ alone, and all correlation tools act on $h_{f'-f/2}$.
- **Search before building.** The corpus already holds the exact identities for the objects of §2;
  check the sieve, Fermi–Nyman and source-graph modules before constructing a new bridge.
