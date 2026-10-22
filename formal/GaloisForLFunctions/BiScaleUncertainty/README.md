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

## The shared target: the sign of the critical arithmetic form

Nine programmes of this corpus work on one object. The Riemann Hypothesis is the nonnegativity of
one critical arithmetic form, and the form can be read in three equivalent faces:

- the **incidence face** (Arithmetic Incidence Positivity, `ArithmeticIncidencePositivity`):
  conductance by conductance, on pairs of points `(x, y)` of the logarithmic line, with the
  arithmetic edges indexed by divisibility (`a ∣ b`) and by products (`ab` a prime power), and the
  pole as the only positive source on crossing pairs;
- the **lag face** (Square-Root Threshold, `SquareRootThreshold`): one window inequality `P_v ≥ 0`
  per scale on the prime side, for the difference tests of one generic width, at height `T` and
  bandwidth `λ = log X / log T`;
- the **aperture face** (Arithmetic Criticality Theory, `ArithmeticCriticalityTheory`; Arithmetic
  Positivity Theory, `ArithmeticPositivityTheory`; the odd Weil-weight route OWU in `RHTower`): the
  ground-energy path `μ(A)` of the restricted Weil form at aperture `A`, which must never cross zero,
  and the gauge and source theories that would prove it.

The finite arithmetic programmes (Bézout–Valuation Incidence, `BezoutValuationIncidence`;
Trans-Horizon Incidence Mechanics, `TransHorizonIncidenceMechanics`; Bi-Scale Uncertainty,
`BiScaleUncertainty`) supply the additive, single-modulus structure of the integers that the three
faces cannot see on their own: Bézout relations, residue classes, pronic Gram matrices, horizon
mechanics, and the two-scale constraint of the integer grid against the hyperbolic weight.

The continuation layer (Arithmetic Continuation and Critical Energy,
`ArithmeticContinuationAndCriticalEnergy`) supplies what no face states on its own: the transport
of a finite critical energy along a parameter — damping, coefficient cutoff or aperture — so that a
certificate at one parameter becomes a certificate at another, with the observation horizon
quantified uniformly throughout.

The admissibility layer (Scale-Signed Incidence Criticality, `ScaleSignedIncidenceCriticality`)
supplies the price list. A mechanism is not the arithmetic it studies but a *reading* of it — a map
from its data to the observables it actually uses — and each reading has an exact resolution limit:
the best bound on the target invariant that any method reading it can prove. The layer computes
those limits, so a route can be priced before it is built, and states the separations a reading must
perform to be admissible at all.

**Why one theory.** Each existing layer stops where the corpus proves it stops. Sieve and bilinear
methods see the additive structure of `ℕ` only after averaging over a family, and below half
damping no sign-blind datum decides the receiver. Multiplicative, spectral and explicit-formula
methods hold verbatim for Beurling systems with off-line zeros. Dirichlet-form and criticality
identities hold for every even positive kernel, and positivity on restricted families is paid by an
archimedean gain that is absent on the RH-complete cone. A closing theorem must at once see both
operations of `ℕ` at a single modulus, carry a sign structure (one negative square, the pole plane,
the signs of the Möbius row), and be resolved at the zero spacing, at square-root precision at every
scale. No existing field has its basic objects built with all three; the nine programmes build
them.

**The mechanisms the shared target needs**, with the programme that owns each:

1. A prime-side inequality with no slack: payment of each anti-diagonal atom `Λ(n) n^{−1/2}` by
   same-side atoms and the variance, on all even profiles, in sign-changing gauges, with a
   Harnack-type propagation across the prime shifts `log 2, log 3, …`
   (`ArithmeticIncidencePositivity` with `ArithmeticCriticalityTheory`).
2. Single-modulus bilinear dispersion on the pronic Gram, through the reciprocity
   `{N/pq} ↔ p̄/q + q̄/p`, for the actual Möbius or prime row; it reduces exactly to the
   single-modulus statistics `Σ_p |Λ_p(c')|/p` of that row (`BezoutValuationIncidence`).
3. A no-crossing law for the ground-energy path, equivalently the absence of a first negative lag
   for `ζ` (`ArithmeticCriticalityTheory`, `ArithmeticPositivityTheory` and OWU on the aperture side;
   `SquareRootThreshold` on the lag side).
4. A definite spectral realization with a prime modification as large as `S(T)`: a Hilbert space
   and a self-adjoint operator whose spectral measure is the critical-zero measure, with
   non-unit-modulus Euler factors (`ArithmeticPositivityTheory` for the source class and the
   realization problem; the operators of the routes HF, CHMD and Connes–Consani–Moscovici in
   `RHTower`). Every certificate of positivity is the critical-zero measure, so this is mechanism 3
   seen from the other side.
5. A sign-reading additive input at a single modulus: below half damping a bound on the receiver
   must read the signs of the coefficients, through first-order data at prime moduli (`k ↦ pk`) or
   odd-degree additive moments (`k ↦ k + v`) (`TransHorizonIncidenceMechanics` with
   `BezoutValuationIncidence`; `BiScaleUncertainty` for the node criticality `log 4` against
   `log 6`).
6. A continuation theorem transporting a finite critical energy from the unconditionally admitted
   end of a parameter range towards the critical end: a horizon-free bound on the negative part of
   one complete signed pairing on each compact subinterval, which is weaker than a bound on the
   corresponding norm and already yields an explicit zero-free strip when it covers only part of
   the range (`ArithmeticContinuationAndCriticalEnergy`).
7. An admissible reading: a mechanism presented as a reading of its own data whose fibres fail to
   realise the maximum of the invariant it claims to bound. On the zero side this forces the
   aperture past the Nyquist aperture of the configuration addressed and forces the *size* of the
   Weil deficit to be estimated rather than its sign; on the prime side it forces `Λ` to be
   separated from each of its single-index perturbations
   (`ScaleSignedIncidenceCriticality`).

**Criteria every contribution to the shared target must meet.**

- *Selectivity.* State what the result gives for `ζ(s−a)ζ(s+a)`, for a Beurling system with an
  off-line zero, and for the Liouville-twisted weight; a statement surviving all three is not
  about RH (test models: `BiScaleUncertainty`).
- *No family average.* One character, modulus one, shift zero. This is an exact floor and not a
  preference: the worst width inside a joint certificate over a family of any cardinality is the
  trivial one, because the extremal datum is already uniform across the family.
- *Square-root precision beyond the diagonal.* Prime sums of length at least the height,
  controlled beyond the mean-value regime: one inequality per window at every scale on the lag
  family, `θ = 2` on the Gram. On the aperture face the same demand is a theorem: a method
  controlling the Weil deficit of a configuration of scale `L` to precision `η` resolves depths
  only down to `√(η/L³)`, so excluding depth `β` costs precision `β²L³`.
- *Every scale, not almost every.* A statement about an exceptional set, a proportion or a typical
  member is infrastructure (the every-height problem: `SquareRootThreshold`). The two monotone
  faces may be verified along an unbounded sequence of apertures or radii, with nothing proved in
  between; the incidence face admits no sampling at all, since every prime power is individually
  necessary.
- *Node criticality.* The mechanism distinguishes `log 4` from `log 6`; sampling-density and
  generic uncertainty arguments are excluded in advance.
- *Signs read.* Below half damping the mechanism uses first-order data at prime moduli or
  odd-degree additive moments; magnitude, two-point and translated-moment data are blind, since the
  parity pairs exist at every damping `ε ≤ 1/2`.
- *Complete expression, no margin, no archimedean subsidy.* Mean, diagonal, mixed terms, Gamma and
  polar charges, endpoints and history are retained; a gain of size `log(1/w)` or `log M` at the
  archimedean place against a bounded prime cost is nonselective by construction. The dividing line
  is growth, not size: a subsidy growing with the frequency of the test is satisfied by the
  all-ones weight and removes the criterion outright, while a subsidy constant or linear in the
  aperture leaves it intact.
- *Units.* Positivity is measured by the aperture `A` or the support through which the inequality
  holds for all profiles; cancellation by the exponent `θ` obtained or the lag `V` beyond which
  `P_v ≥ 0` is proved; localization by the depth `δ(n, R)` excluded below height `T(n, R)` and by
  the visibility lag `V₀(w, η, δ₀)`; damping by the smallest `ε` at which the receiver is bounded;
  admissibility by the pair (class of readings, exact resolution limit). Identities, finite
  classifications and nonselective positivity count as zero in these units.
- *Grading.* A sign criterion with no partial value is incomplete. Every face of the target now has
  a one-parameter family whose endpoint is RH and whose interior is an explicit zero-free strip:
  the graded odd-sector floor and the graded incidence allocation at rate `2σ`, the graded pole
  cross entry at rate `1 + 2α`, and the partial damping continuation above `a₀`. State which member
  of the family a partial result reaches.
- *Calibration.* Reproduce the corresponding theorem over `F_q[T]`, or say why it cannot be done
  (`BiScaleUncertainty`).
- *Pairs.* Every invisibility theorem comes with a visibility witness, every identity with the
  estimate it enables or the sharp boundary it proves, every obstruction with its replacement
  hypothesis proved sufficient.

### This programme's role

BiScale is the uncertainty face. It owns the two-structure constraint on the logarithmic line (the
integer grid against the hyperbolic weight), the band formulation of the square-root barrier, the
blind cone (prime-blind positivity, `log 4` against `log 6`), packets and multiplicity, and the
sign-character classification of arithmetic observation. It owns the node-criticality criterion,
the Beurling test of selectivity and the function-field calibration of the shared criteria: a
statement that holds verbatim for a Beurling system with an off-line zero is not about RH, and a
claimed cofinal sign or cancellation must reproduce its counterpart over `F_q[T]` or name the step
that uses `ℤ`. It supplies to `ArithmeticIncidencePositivity` and
`ArithmeticCriticalityTheory` the exact slack of the blind polar class and to `SquareRootThreshold`
the band energy law. It also owns the exponent dictionary of the barrier: the Chebyshev mean square,
the Laplace energy, the band energy and the two-exponential pole compression all have one
exponential rate, and that rate is the zero width — so a partial estimate on any of them is read
off as an explicit zero-free strip rather than as progress towards a sign.

### How the programme connects to the other programmes

BiScale is the hub of the finite arithmetic side and the laboratory of the analytic side: it owns
the coordinates (autocorrelation, Lévy energy, polar density, the signed prime–polar measure, the
hyperbolic gauge) in which the other programmes state their estimates, and it consumes their
arithmetic.

- **Arithmetic Positivity Theory is built on BiScale sources.** The factorial Müntz family (tail
  primitive, analytic repair of the readout, zero-side smoothing limit, prime–polar budget, Weil
  smoothing, Gram decoupling of the tent direction), the signed prime–polar jump domain, the
  logarithmic increment energy and the origin-collar leverage of §3.2 and §3.5, the compact
  Lipschitz Lévy energy and the polar moment identity are the objects APT continues at the
  critical envelope `β = 1/2`. The Müntz tail's unbounded normalized energy (§3.12) is the fact
  APT turns into the critical factorial family. In return APT's complete critical form, dyadic
  dilation inequality and tent family are the producers of this programme at unbounded support.
- **Bézout–Valuation Incidence and Trans-Horizon Incidence Mechanics supply the finite
  arithmetic of §3.14.** The translation prediction and exact compression of divisor-sieve
  signals, the six-mode stability and sharp quarter decorrelation, the gcd-orbit projection and
  exact translation periods, the Ramanujan lag coefficient, the pronic Bézout split and the
  successor moment region are BVI theorems; the radical checkpoint sign rigidity and the finite
  multiplicative observation state are THIM theorems. BiScale's arithmetic observation theory
  (recovery degrees, stability exponents, sign characters) is stated on top of them, and the
  passage from period moments to polynomial horizons stays in BVI. In the other direction BVI's
  Barban–Vehov pinch, Vasyunin tail Gram, witness-cell transfer, sieve phase recoveries and the
  two-lag moment cone, and THIM's producer–consumer duality, Lorentz boost, stationary resolvent
  Markov positivity and Euler–Poisson chiral drift, are built on BiScale's coordinates. THIM's
  parity pairs are the receiver-side reason why the sign-character classification of §3.14 is
  the right organizing principle: below half damping no sign-blind observable decides.
- **Arithmetic Criticality Theory and Arithmetic Incidence Positivity receive the blind cone.**
  The exact slack of the blind polar class, the power-node removal law and the deletion prices of
  §3.16 are the archimedean inputs to the sign-changing gauges of ACT and the pair-by-pair
  payment of AIP: a gauge that pays the prime atoms must at least pay the Euler prices
  `Λ(m)/√m` of the nodes it uses, and the `log 4`/`log 6` thresholds of §3.16 are the node
  criticality every such gauge is measured against. ACT's Lévy–Krein rigidity of the even sector
  and its Euler–Maclaurin cell quadrature are shared with §3.3.
- **Square-Root Threshold reads the same barrier at height `T`.** BiScale's band
  `|ξ| ≤ √(N+2)` and SRT's bandwidth `λ = log X/log T` are two coordinates of the square-root
  threshold; the band spectrum of §3.10 and SRT's zero width `sup|Re ρ − ½|` are the same number,
  read here from the Chebyshev mean square and the packet growth, there from the first negative lag.
  The window remainder `|c(L) − e^{L/2}| ≤ Ce^{L/2−κL^ex}` (every `ex < 3/5`) of §3.16 is the window
  form of SRT's lag envelope `P_v ≥ −|φ(0)| − Ce^{v/2−v^ex}`, both of Vinogradov–Korobov strength;
  SRT's de Bruijn–Newman heat-time bound uses the width this programme reads from the band.
- **RHTower supplies the analytic theorems** the mechanisms consume: Hardy's theorem and the
  superlinear count of simple critical zeros, the critical-Mellin resolvent width and the
  generalized von Koch bound, Cramér's dyadic mean square, the one-sided Landau engine and the
  Chebyshev-deficit criterion, Montgomery–Vaughan, Vinogradov–Korobov and the prime number
  theorem with error term, the Selberg and Barban–Vehov diagonals, the Fermi–Nyman generators, the
  CHMD graph mollification and the Weil deletion test kit. The blind symbol slacks of §3.6 refine
  RHTower's prime-blind archimedean constants, whose full-grid zero-pole version is RH.
- **Arithmetic Continuation and Critical Energy transports what this programme measures.** The
  continuation layer's own calibration is a BiScale-style model computation: over `F_q[T]` the
  degree-wise Möbius sums vanish beyond degree one, the centred damped prefix is exactly constant,
  the critical energy is bounded by one uniformly in the damping and the horizon, and the
  continuation budget is zero — so the whole number-field difficulty sits in the absence of that
  cancellation, not in the shape of the transport. In the other direction BiScale's exponent
  dictionary is what gives the continuation layer its units: a partial transport above a damping
  `a₀` reports the strip `½ + a₀`, in the same width unit as the band rate.
- **Scale-Signed Incidence Criticality turns the node criticality into a statement about methods.**
  Node criticality is the deletion law of §3.16; the admissibility layer proves that no reading
  unchanged by finitely many nodes resolves node positivity, classifies the positive node sets as
  the principal up-set generated by the prime powers, and attaches the number `(smallest prime
  power)⁻¹ = ½` to the face. The `½` of the node face and the `½` of the band's extremal depth are
  independent arithmetic facts that happen to coincide: the first because `2` is the first prime
  power, the second because `½` is the deepest an off-line zero can sit.
- **Calibration duty.** BiScale owns the test models of the shared criteria: the shifted pair
  `ζ(s−a)ζ(s+a)`, Beurling systems with an off-line zero, the Liouville twist and `F_q[T]`. The
  twist invariance of window spectra (§3.16) is the first calibration theorem: window extremes
  see atoms only through their sizes, so they cannot read GRH.

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
  total mass $\int h_f=(\int f)^2$; the **probe transform** $\hat f(\gamma)=\int e^{i\gamma v}f(v)\,dv$
  at a real or complex ordinate $\gamma$; a source **sees** a zero $\rho=\tfrac12+i\gamma$ when
  $\hat f(\gamma)\ne0$ and is **blind** to it otherwise.

A **grid source** at level $n$ is a compact continuous source with $h_f(\log k)=0$ for
$2\le k\le n+2$; the **blind cone** is the infinite-level version. More generally a source or a
nonnegative combination of sources is **blind on a node set** $\mathcal N\subseteq\{2,3,\dots\}$
when its correlation vanishes at $\log n$ for every $n\in\mathcal N$. A node set is **gapped**
when it has arbitrarily far logarithmic gaps of half-width $1/5$ (the powers of one integer are
gapped); it has **sub-square-root window density** when, along arbitrarily far unit windows
$X\le\log n\le X+1$, its node count $K$ satisfies $M(K+1)(1+\log(K+1))\le e^{X/2}$ for every fixed
$M$ (the $S$-smooth integers for any finite $S$ do; the full grid, with $\asymp e^X$ nodes per
window, does not). A **clique** is a finite family of shifts $t_i$ with $h_f(t_i-t_j)=0$ for
$i\ne j$; under grid blindness every dyadic-odd coset $\{\log(m2^k)\}$, $m$ odd, is a clique,
because $\log n-\log m=\log(n/m)$ when $m\mid n$.

### 2.2 The archimedean weights, energies and the folded symbol

| weight | formula | role |
|---|---|---|
| forward Lévy weight | $w_{\mathrm{arch}}(x)=e^{x/2}/\sinh x$ | the weight of $\mathcal J$; singular at $0$, $\sim 2e^{-x/2}$ at $\infty$ |
| dual weight | $w_{\mathrm{dual}}(x)=e^{-x/2}/\sinh x$ | image of $w_{\mathrm{arch}}$ under $x\mapsto-x$ (the functional equation) |
| secant core | $\operatorname{sech}(x/2)=1/\cosh(x/2)$ | smooth positive-definite part: $w_{\mathrm{arch}}=\operatorname{sech}(x/2)+w_{\mathrm{dual}}$ |
| half-angle split | $w_{\mathrm{arch}}=\tfrac{1}{2\sinh(x/2)}+\tfrac{1}{2\cosh(x/2)}$ | cosecant singularity plus secant |
| reciprocal weight | $1/w_{\mathrm{arch}}(y)=e^{-y/2}\sinh y\le y\,e^{y/2}$ | vanishes linearly at $0$: the price of transport |
| Lévy density | $e^{-x/2}/(1-e^{-2x})$ | the Lévy–Khintchine density of the Gamma phase rate |
| Lévy symbol | $\int_0^\infty(1-\cos tx)\,w_{\mathrm{arch}}(x)\,dx$ | the spectral form of $\mathcal J$; grows like $\log|t|$ |

The **Lévy energy** is $\mathcal J(f)=\int_0^\infty (h_f(0)-h_f(x))\,w_{\mathrm{arch}}(x)\,dx\ge 0$,
the **normalized energy** is $\mathcal J(f)/h_f(0)$, and the forward–dual split gives
$\mathcal J=\mathcal J_{\mathrm{sech}}+\mathcal J_{\mathrm{dual}}$ with both parts nonnegative.

On the spectral side the archimedean symbol is the even function $\Omega(r)$ of §1.1, minimal at
$r=0$ and increasing in $|r|$. For a nonnegative combination $c$ of sources with **combined
spectral density** $G_c(r)=\sum_fc_f|\hat f(r)|^2$:
$$
\mathrm{mass}(c)=\frac1{2\pi}\int G_c,\qquad
A(c)=\frac1{2\pi}\int G_c\,\Omega=\sum_fc_f\bigl(\Omega(0)h_f(0)+\mathcal J(f)\bigr),\qquad
v_c(n)=\frac1{\pi\sqrt n}\int G_c(r)\cos(r\log n)\,dr ,
$$
the **archimedean part without the pole**, and the **node value** at $n$ (the correlation of
the combination at $\log n$ with the critical weight). For an integer $q\ge2$ with $\ell=\log q$
the **folded symbol** is $F(z)=\Omega(\|z\|/\ell)$ on the circle $\mathbb R/2\pi\mathbb Z$, where
$\|z\|$ is the distance to $0$; its **period mean** $m_q=\int F=\frac\ell\pi\int_0^{\pi/\ell}\Omega$,
its **cosine coefficients** $\varphi_d=\frac1{2\pi}\int F(z)\cos(dz)\,dz$, and its **orbit
averages** $F_d(z)=\frac1d\sum_{k<d}F(z+2\pi k/d)$ are the constants of the power-grid theory.
The **phase measure** of $G_c$ is the image of $G_c(r)\,dr$ under $r\mapsto r\ell\bmod2\pi$; its
Fourier coefficients are the node values $\pi\sqrt{q^j}\,v_c(q^j)$, and $\Omega$ dominates
$F\circ\mathrm{phase}$ pointwise, the difference being the **fold defect**.

**Symbol slack.** A real $M$ is a **blind symbol slack on $\mathcal N$** when every nonnegative
combination blind on $\mathcal N$ satisfies $A(c)+M\,\mathrm{mass}(c)\ge0$, and a **zero-pole**
slack when the same holds for combinations of total pole mass zero with the pole retained. The
exact slack on a node set is the infimum of $-A(c)/\mathrm{mass}(c)$ over its blind cone. On the
full grid, zero-pole positivity (slack $0$) is RH. For a set of exponents $J$ the **moment value**
$$
V_q(J)=\inf\Bigl\{\int F\,d\nu:\ \nu\text{ a probability measure on }\mathbb R/2\pi\mathbb Z,\ \int\cos(jz)\,d\nu=0\ \forall j\in J\Bigr\}
$$
is the value of the circle moment problem of the folded symbol. A **design** is a finite list
of weighted angles; its cosine moments are $\sum w\cos(j\theta)$.

### 2.3 Polar objects

The **polar density** is $2\cosh(x/2)=e^{x/2}+e^{-x/2}$. The **pole term** of a real source is
$2\bigl((\int f\cosh(u/2))^2-(\int f\sinh(u/2))^2\bigr)$, and for every real test
$\operatorname{weilArchRe}=\text{pole term}+\Omega(0)h_f(0)+\mathcal J(f)$. The **polar copy**
$f(u)-e^{-T/2}f(u-T)$ kills the positive exponential moment; the **symmetric copy**
$f(u)-\frac{1}{2\cosh(T/2)}(f(u-T)+f(u+T))$ kills both moments, preserves parity, multiplies
$h_f$ by $1+2b^2$ on any bounded window once $T$ is large, and changes the normalized energy by
$O(e^{-T})$. The **distant pair** $b(u)-\sigma b(u-T)$ of a bump has pole
$2(1-\sigma e^{T/2})(1-\sigma e^{-T/2})m_+m_-$ of either sign and size $\asymp e^{T/2}$ while its
archimedean part without the pole stays bounded in $T$.

### 2.4 The signed prime–polar measure, packets and the hyperbolic gauge

With $L=\log(N+2)$ the **cutoff**:

- $\nu_N=\sum_{n\le N+2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}-2\cosh(t/2)\mathbf 1_{[0,L]}\,dt$;
  the **pairing** is $\langle h,\nu_N\rangle$, the **full pairing** its $N\to\infty$ form on the
  half line;
- the **signed packet** $P_f(u)=\int f(u+s)\,d\nu_N(s)$ and the **packet energy**
  $\|P_f\|^2=\iint h_f(s-t)\,d\nu_N(s)d\nu_N(t)$, which retains the prime–polar cancellation;
- the **stationary packet** of a real compact $C^2$ source vanishing outside $[-w,w]$, at shift
  $\tau$,
  $$
  P_f(\tau)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}f(\log n-\tau)-\int_0^\infty2\cosh(x/2)f(x-\tau)\,dx ,
  $$
  the pairing of the translate $f(\cdot-\tau)$ with the untruncated measure; it is a linear
  functional of $f$, in contrast to the quadratic Weil functional of $h_f$;
- the **zero series** $\sum_\rho m_\rho e^{i\gamma_\rho\tau}\hat f(\gamma_\rho)$ over the zeros
  $\rho=\tfrac12+i\gamma_\rho$ with multiplicities, the **archimedean tail**
  $A_f(\tau)=\frac1{2\pi}\int e^{ir\tau}\hat f(r)\Omega(r)\,dr$, and the two **critical energies**
  $E(f)=\sum_{\Re\rho=1/2}m_\rho^2|\hat f(\gamma_\rho)|^2$ and
  $W(f)=\sum_{\Re\rho=1/2}m_\rho|\hat f(\gamma_\rho)|^2$;
- the **normalized Chebyshev error** $\tilde E(t)=e^{-t/2}(\psi(e^t)-e^t)$, the **gauge
  derivative** $f\mapsto f'-f/2=e^{u/2}(e^{-u/2}f)'$, the derivative in the hyperbolic gauge of the
  critical line, and the **stationary gauge convolution**
  $\Phi_f(\tau)=\int_0^\infty\tilde E(t)\,(f'-f/2)(t-\tau)\,dt$;
- the **causal kernel** $K(x)=e^{-x/2}\mathbf 1_{x\ge0}$, the **causal response** $R_N=K\star\nu_N$,
  the **Laplace kernel** $e^{-|x|/2}=K\star\tilde K$, and the **Laplace energy**
  $\iint e^{-|s-t|/2}\,d\nu_N d\nu_N=\int R_N^2$;
- the **Fourier pairing** $\hat\nu_N(\xi)$ and the **spectral density**
  $S_N(\xi)=|\hat\nu_N(\xi)|^2/(\tfrac14+4\pi^2\xi^2)$, with the **band frequency** $\sqrt{N+2}=e^{L/2}$;
- the **zero width** $\beta$: every zero of $\Xi$ has $\Re\rho\le\tfrac12+\beta$; width $0$ is RH.

A **probe** is a source used to read zeros through its packet; the **dilates** $f_t(u)=f(u/t)$,
the **tuned probes** $f_R(u)=\varphi(u/R)\cos(\gamma_0u)$, and the **boosts** $e^{tu}\varphi(u)$
are the probe families that recur. A **universal probe** sees every zero.

### 2.5 Hyperbolic multipliers

$(C_\alpha f)(u)=\cosh(\alpha u)f(u)$ and $(S_\alpha f)(u)=\sinh(\alpha u)f(u)$. They do not
commute with translation; they form a representation of the boost group $\mathrm{SO}^+(1,1)$;
$S_\alpha$ maps odd sources to even ones. The **Casimir** $(h_{C_\alpha f}-h_{S_\alpha f})/\cosh(\alpha x)=h_f$
is independent of $\alpha$. The boost $e^{tu}=C_t+S_t$ translates the transform,
$\widehat{e^{t\cdot}\varphi}(z)=\hat\varphi(z-it)$.

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
and the fold-free kernel $\ker P$. On the blind side the producers are **spectral designs**:
cosine and sine modulations of a wide envelope at prescribed frequencies, whose correlation
vanishes at prescribed lags exactly by telescoping identities.

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
| blind on a node set, gapped node set, zero-pole positivity on a node set | `BlindOn`, `GappedNodeSet`, `ZeroPoleBlindPositiveOn` |
| mass, archimedean part without pole, pole mass, node values | `massOf`, `nodeArchOnly`, `nodePoleMass`, `nodeVector` |
| blind and zero-pole symbol slack on a node set | `BlindSymbolSlackOn`, `ZeroPoleBlindSymbolSlackOn` |
| combined spectral density, phase measure | `combinationSpectralDensity`, `exists_phase_measure` |
| folded symbol, period mean $m_q$, cosine coefficient $\varphi_d$, orbit average $F_d$ | `foldedSymbol`, `symbolPeriodMean`, `foldedCosineCoefficient`, `orbitAverage` |
| moment value $V_q(J)$, designs and their moments | `powerMomentValue`, `designMoment`, `designValue` |
| polar density, polar copy, symmetric copy | `polarDensity`, `polarCopy`, `evenPolarCopy` |
| prime weight, cutoff, pairing, full pairing | `primeWeight`, `cutoff`, `SignedPrimePolar.pairing`, `fullPairing` |
| signed packet, packet energy | `signedSource`, `packetEnergy` |
| stationary packet, zero series, critical packet and Weil energies | `stationaryPacket`, `zeroSeries`, `criticalPacketEnergy`, `criticalWeilEnergy` |
| stationary gauge convolution, tuned probe, universal probe | `stationaryGaugeConvolution`, `tunedProbe`, `SeesAllZeros` |
| simplicity criterion of a universal probe | `riemannHypothesis_and_simple_iff_of_universal` |
| normalized Chebyshev error, gauge derivative | `normalizedLogError`, `gaugeDerivative` |
| causal response, Laplace energy, Fourier pairing, spectral density of $\nu_N$ | `causalResponse`, `laplaceEnergy`, `fourierPairing`, `spectralDensity` |
| zero width | `XiZeroHalfPlaneBound` |
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

### 3.4 Polar enforcement: gaps against density

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

The dividing line is not finite against infinite but **gaps against density**. On every gapped
node set the distant pair of a bump placed in a far gap is blind, carries a pole of either sign
and size $\asymp e^{T/2}$, and has archimedean part bounded uniformly in $T$: every pole mass is
available at arbitrarily small archimedean cost, every blind mixture is $\varepsilon$-close in
archimedean energy to a zero-pole blind mixture, and zero-pole positivity fails. The same holds
on every node set of sub-square-root window density: a pigeonhole node-free point at distance
$1/(2(K+1))$ hosts the pair of the bump compressed by $L=K+1$, with pole $\asymp e^{X/2}/L^2$ and
archimedean part $O((1+\log L)/L)$, so the transport cost $O(L(1+\log L)e^{-X/2})$ tends to zero.
The $S$-smooth integers of any finite set $S$ of primes have at most
$(\lfloor(X+1)/\log2\rfloor+1)^{|S|}$ nodes per window and fall on this side; the full grid,
with $\asymp e^X$ nodes per window, is RH. The pole weight $e^{x/2}$ makes square-root node
density the critical density for pole visibility. On a gapped node set the zero-pole slack
equals the slack, so every blind-cone constant below is simultaneously a zero-pole constant.

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
order is logarithmic in both directions:
$$
\frac{\delta}{4\pi}\log(M+2)\,h(0)\ \le\ \sup_f\int_0^{(M+1)\delta}h_f\ \le\ 12\delta\,(4+\log(M+1))\,h(0).
$$
The upper bound holds because the zeros make every spectral Dirichlet energy flat,
$\int\rho(\xi)D_{M+1}(\theta-2\pi\delta\xi)=(M+1)h(0)$ for every phase, which caps the spectral
mass of each arc of length $\asymp1/(M\delta)$ and turns the window kernel into a harmonic sum.
The lower bound is a spectral design: with $A=(M+1)\delta$ and the quarter-shifted frequencies
$\omega_k=2\pi(k+\tfrac14)/A$, the mixture $(M+1)^{-1}\sum_{k\le M}\cos(\omega_kx)$ vanishes at
every $m\delta$ by telescoping (the sum closes because $(M+1)\theta\in2\pi\mathbb Z$), while every
atom contributes $A/(2\pi(k+\tfrac14))>0$ to the window, a harmonic sum; a wide envelope with
increment bounded by $M_b|x|$ uniformly and mass $\asymp R$ realizes the mixture as a compact
$C^2$ source with exact zeros and keeps a definite fraction of the sum.

### 3.6 The folded symbol and the circle moment problem

Blindness at the powers of one integer is a statement about one phase. For a nonnegative
combination $c$ blind at every $q^j$, $j\ge1$, the Fourier coefficients of the phase measure of
$G_c$ at every nonzero integer vanish, so the phase $r\ell\bmod2\pi$ is uniformly distributed for
even observables, and since $\Omega\ge F\circ\mathrm{phase}$ pointwise,
$$
A(c)\ \ge\ m_q\,\mathrm{mass}(c):
$$
the **single-integer bathtub**, with blindness required only at the powers of $q$ and no
assumption on the other nodes. It is exact: midpoint atoms $\omega_k=(k+\tfrac12)\pi/(N\ell)$,
$k<N$, satisfy $\sum_k\cos(\omega_kj\ell)=0$ for $1\le j<2N$ (the telescoping
$2\sin(\theta/2)\cos((k+\tfrac12)\theta)=\sin((k+1)\theta)-\sin(k\theta)$ closes at
$N\theta=\pi j$), cosine and sine modulations of an envelope whose correlation vanishes beyond
$2N\ell$ are therefore blind at all $q^j$, their symbol is $h(0)\sum_k\Omega(\omega_k)$ up to the
envelope energy, and the midpoint sum is at most $Nm_q+\Omega(\pi/\ell)-\Omega(0)$; the bathtub is
attained at rate $O(1/N)$. The pole does not move it: the powers of $q$ are gapped, so the exact
zero-pole slack on them is also $-m_q$. Among all integers the prime $2$ leaves the smallest gap,
$m_q\le m_2$.

**Incidence, not spacing.** Add blindness at one further integer $n\ge2$, $t=\log n$. If $n$ is a
power of $q$ nothing changes. Otherwise, with the folded radius
$\rho(r)=\|r\ell\bmod2\pi\|/\ell\in[0,\pi/\ell]$, power blindness gives
$\int G\cos(t\rho)=s\int G$ with $s=\sin(\pi t/\ell)/(\pi t/\ell)\ne0$, blindness at $n$ gives
$\int G\cos(rt)=0$, and the cosine defect is paid pointwise by the fold defect,
$|\cos(rt)-\cos(t\rho(r))|\le C\,(\Omega(r)-\Omega(\rho(r)))$: a frequency outside the
fundamental period either straddles $\pi/\ell$, where $\Omega$ has slope at least
$\kappa=(\pi/8\ell)/(\tfrac1{16}+\pi^2/\ell^2)^2$ from the first Gauss term, or lies beyond
$2\pi/\ell$, where the fold defect is at least $\kappa\pi/\ell$. Hence
$A(c)\ge(m_q+|s|/C)\,\mathrm{mass}(c)$: one multiplicatively independent node improves the
bathtub by an explicit amount, and the improvement is zero exactly on the multiplicative
dependence. Blindness at the powers of $2$ and at $3$ gives a slack strictly below the dyadic
constant.

**Each power node has a price.** Deleting one node $q^d$ leaves exactly one free cosine moment
$c=\int G\cos(d\ell r)$; by Fourier uniqueness the phase measure is then the density
$(\int G+2c\cos(dz))\,dz/2\pi$, whose positivity forces $2|c|\le\int G$, so the exact slack on
$\{q^j:j\ne d\}$ is $-(m_q-|\varphi_d|)$, attained by the translated pairs $f\pm f(\cdot-d\ell)$
of a near-extremal combination, which multiply the spectral density by $2\pm2\cos(d\ell r)$ and
keep every other power node blind. Far nodes are cheap, $|\varphi_d|\le(\Omega(\pi/\ell)-\Omega(0))/d$.
Blindness only off the multiples of $d$ makes the phase measure invariant under rotation by
$2\pi/d$, so the exact slack on $\{q^j:d\nmid j\}$ is $-\min F_d$, attained by an exact design
with atoms at the folded radii of the orbit of a minimizer (the cosine mixture
$\sum_k\cos(\alpha+2\pi jk/d)$ vanishes for $d\nmid j$ for every envelope, with no discretization
error); the powers of $q^d$ are worth exactly $m_q-\min F_d$.

**The moment theorem.** For every set $J$ of exponents the exact blind symbol slack on
$\{q^j:j\in J,\ j\ge1\}$, with or without zero pole mass, is
$$
-V_q(J),\qquad V_q(J)=\inf\Bigl\{\int F\,d\nu:\ \nu\ \text{probability on the circle},\ \int\cos(jz)\,d\nu=0\ (j\in J)\Bigr\}.
$$
The lower bound is the normalized phase measure, which is admissible. The upper bound is design
theory: on $N>2K$ equally spaced angles the weights $(1\pm\cos(j\theta_k))/N$ have cosine moment
$\pm\tfrac12$ at $j$ and $0$ at every other frequency in $[1,K]$; the finitely many moments and
the value of any probability measure lie in the closed convex hull of the traced curve, so a
design matches them up to $\eta$; a small mixture of quadrature designs removes the residual
moments exactly at cost $O(\lambda)$; modulations at the folded radii of the design angles under
an envelope with correlation radius below $(K+1)\ell$ are blind at all of $J$, up to $K$ by the
design and beyond $K$ by the envelope, with envelope energy $O(1/K)$. The three closed forms are
$V_q(\mathbb N)=m_q$, $V_q(\mathbb N\setminus\{d\})=m_q-|\varphi_d|$ and
$V_q(\{j:d\nmid j\})=\min F_d$.

**The signed bathtub.** No blindness is needed for the identity behind all of this. The phase
measure of a compact combination has finitely many nonzero Fourier coefficients
$\pi\sqrt{q^j}\,v_c(q^j)$ (node values vanish beyond the support), so it is the trigonometric
density $(\int G+2\sum_j\pi\sqrt{q^j}v_c(q^j)\cos(jz))\,dz/2\pi$, and
$$
A(c)\ =\ m_q\,\mathrm{mass}(c)+\sum_{j\ge1}\varphi_j\sqrt{q^j}\,v_c(q^j)+\frac1{2\pi}\int G_c\,(\Omega-F\circ\mathrm{phase}),
$$
with the last term nonnegative and zero exactly when the spectral density lives on the
fundamental period. Every power node is priced by one Fourier coefficient of the folded symbol
in an exact signed identity; blind combinations recover the bathtub and the removal law is its
one-free-node case.

### 3.7 Hyperbolic multipliers and the odd sector

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
and the folded sinh source's cell variance is the exact remaining slack. The boost $e^{tu}$ is
also the generic way to make a probe see every zero: for each zero the map
$t\mapsto\hat\varphi(\gamma_\rho-it)$ is a nonzero entire function of $t$, so all but countably
many boosts of a nonzero source are universal probes.

### 3.8 Collar allocation as convex optimisation

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

### 3.9 Signed prime–polar transport

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

### 3.10 The hyperbolic gauge and the square-root barrier

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

**The band spectrum is the zero width.** The three forms of the barrier have one exponential
rate, and it is the depth of the zeros. For $0\le\alpha<\tfrac12$ the following are equivalent:
every zero of $\Xi$ has $\Re\rho\le\tfrac12+\alpha$; for every $\beta>\alpha$,
$\int_0^L\tilde E^2=O(e^{2\beta L})$; for every $\beta>\alpha$, the Laplace energy of $\nu_N$ is
$O((N+2)^{2\beta})$; for every $\beta>\alpha$, the band energy
$\int_{|\xi|\le\sqrt{N+2}}S_N$ is $O((N+2)^{2\beta})$. From the mean square to the width, the
resolvent $Q(t)=e^{-t}(\int_0^te^h\tilde E-\tfrac23)$ is bounded by $(C+1)e^{\beta t}$ through
$2|ab|\le\mu a^2+b^2/\mu$ at the scale $\mu=e^{(\beta-1)t}$, and an exponentially bounded
resolvent continues the critical Mellin defect across $\Re s>\tfrac12+\beta$; from the width to
the mean square, the generalized von Koch bound $|\tilde E(t)|\le Ce^{\beta t}$. At the endpoint
the band **self-improves**: RH gives the linear band $\int_0^L\tilde E^2\le C(1+L)$ (Cramér's
dyadic mean square summed through the gauge dictionary), every subexponential band gives RH, and
hence $\int_0^L\tilde E^2=e^{o(L)}$ already forces $O(L)$. No growth strictly between linear and
exponential is possible. Both directions of "RH $\iff$ linear band" are theorems in the field.

**The two-by-two pole criterion reads the same exponent, and it reads a size, not a sign.**
Compressing the restricted Weil form onto the two polar exponentials leaves a $2\times2$ matrix,
and RH is the statement that its cross entry never exceeds its diagonal at any aperture. The
mechanism behind that criterion is an identification: the cross entry *is* the integrated Chebyshev
deficit $D(2a)=\int_0^{2a}(e^t-\psi(e^t))\,dt$, up to its Gamma boundary mass and an explicit linear
radius correction. Three consequences follow, all in the band's own unit.

* *Size, not sign.* A bound $\lvert\text{cross}(a)\rvert\le Ce^{a}$ at every aperture already gives
  RH, with no reference to the diagonal and no sign. Since the diagonal itself satisfies
  $\lvert\text{diag}(a)\rvert\le C_0e^{a}$, the published positivity criterion is the special case
  in which the bound happens to be realised by the diagonal: the compression may fail, by as much
  as the square-root scale $e^{a}$, and still decide the line.
* *Graded by the width.* For $0\le\alpha<\tfrac12$ a bound
  $\lvert\text{cross}(a)\rvert\le Ce^{(1+2\alpha)a}$ gives the half-plane
  $\Re\rho\le\tfrac12+\alpha$; the transport is the one-sided width criterion, which needs the
  deficit primitive bounded on one side only.
* *Faithful.* The growth rate of $\lvert\text{cross}(a)\rvert$ is exactly $1+2\cdot\text{width}$,
  so the matrix is a lossless reading of the width and not merely a sufficient condition. The
  unconditional input available is Vinogradov–Korobov, $\lvert D(T)\rvert\ll e^{T}e^{-cT^{3/5}}$,
  that is rate $2$ against the needed $1+2\alpha$.

**The band slope reads the zero energy.** If $\int_0^L\tilde E^2\le C(1+L)+K$, then for every
finite family of distinct critical ordinates $\gamma_k$, with $n_k$ the order of $(s-1)\zeta(s)$
at $\rho_k=\tfrac12+i\gamma_k$,
$$
\sum_k\frac{n_k^2}{|\rho_k|^2}\ \le\ C ,
$$
so every zero has multiplicity at most $\sqrt C\,|\rho|$. Under a bound $\int_0^L\tilde E^2\le Ce^{2\beta L}+K$
with $0<\beta<\tfrac12$ the same inequality holds with $2\beta C$ on the extremal line
$\Re\rho=\tfrac12+\beta$: the leading constant of the band reads the zeros on the line of the
width. The mechanism is Abel means against critical characters: a width $\beta$ makes the Laplace
transform $\mathcal L(z)=\int_0^\infty e^{-zt}\tilde E$ holomorphic on $\Re z>\beta$, where it
equals $-((\zeta_u'/\zeta_u)(z+\tfrac12)+1)/(z+\tfrac12)$ with $\zeta_u(s)=(s-1)\zeta(s)$; the
logarithmic residue gives Abel coefficients $\sigma\mathcal L(\beta+\sigma+i\gamma)\to-n/\rho$;
integration by parts against the primitive of $\tilde E^2$ turns the band into an Abel energy
$\sigma\int_0^\infty e^{-\sigma t}\tilde E^2\le C(1+\sigma)$ (tilted by $e^{-\beta t}$ on the
extremal line); the characters $e^{-i\gamma_kt}$ are Abel-orthonormal, and $2|ab|\le a^2+|b|^2$
gives Bessel's inequality for Abel coefficients. Consequences: **the barrier is never sublinear**,
since Hardy's theorem supplies a critical zero and the slope law forbids slope below $1/|\rho|^2$,
so no bound $c(1+L)+K$ holds for every $c>0$; and a zero of order $n$ at $\Re\rho=\tfrac12+\beta$
makes $\int_0^L\tilde E^2-Ce^{2\beta L}$ unbounded above whenever $2\beta C|\rho|^2<n^2$.

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

### 3.11 Packets as spectral filters

The stationary packet of a compact source is the explicit formula read linearly. For a real
$C^2_c$ source vanishing outside $[-w,w]$ and every $\tau>w$, the negative logarithms drop out of
the translate, the two pole terms are exactly the polar density of $\nu$, and
$$
\sum_\rho m_\rho\,e^{i\gamma_\rho\tau}\hat f(\gamma_\rho)\ =\ A_f(\tau)-P_f(\tau)
$$
absolutely, with the archimedean tail $A_f(\tau)\to0$ by Riemann–Lebesgue. Beyond its support a
packet is a bounded tail minus a zero series $\sum_\rho c_\rho e^{\lambda_\rho\tau}$ with
$\lambda_\rho=\rho-\tfrac12$ and $c_\rho=m_\rho\hat f(\gamma_\rho)$.

**Growth law.** For $\sigma\ge0$, $P_f(\tau)=O(e^{\sigma\tau})$ if and only if $\hat f(\gamma_\rho)=0$
at every zero of depth $\Re\rho-\tfrac12>\sigma$: a source is a filter whose packet grows exactly
at the largest depth among the zeros it sees. A growth bound makes the Laplace transform of the
zero series holomorphic on $\Re z>\sigma$; on $\Re z>\tfrac12$ it is the zero resolvent
$\sum_\rho c_\rho e^{(\lambda_\rho-z)b}/(z-\lambda_\rho)$, holomorphic off the locally finite set
$\{\lambda_\rho\}$; the half-plane minus a countable set is preconnected, the two agree, and the
residue $c_\rho$ at every deep $\lambda_\rho$ vanishes. No rightmost zero and no separation of
ordinates is needed. Hence a packet is bounded iff the source is blind right of the line, RH iff
every compact packet is bounded, and the zero width is the universal packet growth exponent.

**One side suffices.** An eventual upper bound $P_f\le Ke^{\sigma\tau}$ alone, or a lower bound
alone, forces the same blindness: $\varepsilon e^{\sigma u}-\eta P_f(u)\mathbf 1_{u>b}$ is the density
of a nonnegative measure, its transform $\varepsilon/(z-\sigma)-\eta(\mathcal L_A-R)$ is analytic
at every real $t>\sigma$ because $\zeta$ has no real zero in the strip, Landau's theorem puts the
abscissa at $\sigma$, and the resolvent continues with vanishing deep residues. So RH iff every
compact packet is eventually bounded above, iff bounded below; a source that sees a zero of depth
$>\sigma$ has a packet above $Ke^{\sigma\tau}$ and below $-Ke^{\sigma\tau}$ at arbitrarily large
shifts, for every $K$. For a universal probe $U$ the single packet $P_U$ decides everything: RH
iff $P_U$ is eventually bounded above, and the zero width is the one-sided growth exponent of
$P_U$.

**Parseval and the packet–Weil law.** If the packet is eventually bounded above (under RH, for
every source), the zero series splits into the critical almost periodic part and a decaying part
over zeros left of the line, and Parseval for absolutely convergent almost periodic series with
injective real frequencies gives
$$
\frac1L\int_w^LP_f^2\ \longrightarrow\ E(f)=\sum_{\Re\rho=1/2}m_\rho^2|\hat f(\gamma_\rho)|^2 ,
\qquad
\operatorname{Re}W(h_f)=W(f)=\sum_{\Re\rho=1/2}m_\rho|\hat f(\gamma_\rho)|^2 ,
$$
the second because $\widehat{h_f}(\gamma)=\hat f(\gamma)\overline{\hat f(\bar\gamma)}$ and
$\bar\gamma_\rho=\gamma_{1-\bar\rho}$ pairs each zero left of the line with a zero right of it,
which the source does not see. Hence $0\le W(f)\le E(f)$, with equality iff every critical zero
seen by $f$ is simple. In the field's coordinates,
$0\le\Omega(0)h_f(0)+\mathcal J(f)-2\langle h_f,\nu\rangle\le\lim\frac1L\int_w^LP_f^2$ for every
real source whose packet is bounded above, and for a pairing-null source this is the bi-scale
uncertainty inequality $|\Omega(0)|h_f(0)\le\mathcal J(f)$ obtained from a one-sided bound on a
single linear packet. Under RH, all zeros are simple iff $E(f)=W(f)$ for every source.

**Persistence and amplitude.** Every nonzero compact source sees a critical zero (its transform
is entire of exponential type while the simple critical ordinates have superlinear density), so
$W(f),E(f)>0$, the strict inequality $|\Omega(0)|h_f(0)<\mathcal J(f)$ holds for every nonzero
pairing-null source with packet bounded above, and every nonzero packet oscillates: there is
$c>0$ with $P_f>c$ and $P_f<-c$ at arbitrarily large shifts, because the critical series has no
zero frequency ($\zeta(\tfrac12)\ne0$), so the packet has Cesàro mean $0$ and mean square $E(f)>0$,
and $-M\le P\le c$ eventually would force $E\le Mc$. Quantitatively, $\limsup|P_f|\ge\sqrt{E(f)}$,
and for the dilates $f_t$ of a source with $\int f\ne0$ the window $|\xi|\le\xi_0/t$ contains at
least $(72\pi)^{-1}(\xi_0/t)\log(\xi_0/t)$ simple critical zeros, each contributing
$t^2|\int f|^2/4$, so $E(f_t)\ge ct\log(1/t)$ and $|P_{f_t}|$ exceeds $\sqrt{ct\log(1/t)}$ at
arbitrarily large shifts. Since $\|f_t\|^2=t\|f\|^2$, the packet energy per unit source energy
grows like $\log(1/t)$: the zero density, the signature of the barrier, as a quantitative
uncertainty principle for probes.

**Resolution and spectroscopy.** Under RH, a linear band for the stationary gauge convolution,
$\int_0^L\Phi_f^2\le C(1+L)+K$, gives $\sum_kn_k^2|\hat f(\gamma_k)|^2\le C$: the gauge
derivative cancels the height damping exactly, $\widehat{f'-f/2}(i\gamma)=-\rho\hat f(\gamma)$,
so a probe weighs a zero by $n^2|\hat f(\gamma)|^2$ where the bare band weighs it by $n^2/|\rho|^2$,
and the Parseval law shows the probe slope is attained. A tuned probe
$f_R(u)=\varphi(u/R)\cos(\gamma_0u)$ has transform
$\tfrac R2(\hat\varphi(R(\xi-\gamma_0))+\hat\varphi(R(\xi+\gamma_0)))$, which concentrates at
$\pm\gamma_0$ as $R\to\infty$, and $E(f_R)/W(f_R)\to m_{\rho_0}$ unconditionally (dominated by
$m_\rho/(1+\gamma_\rho^2)$, summable over the zeros). Under RH both $E(f_R)$ and $W(f_R)$ are
prime-side quantities, the asymptotic mean square of the packet and the Weil functional of the
autocorrelation, so multiplicities are prime-side observables.

**Simplicity as one packet identity.** For a universal probe $U$ the two critical energies agree,
$E(U)=W(U)$, exactly when every critical zero is simple, unconditionally. Hence RH together with
the simplicity of every zero of $\zeta$ is equivalent to two prime–polar statements about the one
source $U$: its packet $P_U$ is eventually bounded above, and the asymptotic mean square of $P_U$
equals the Weil functional of $h_U$, which in the field's coordinates is
$\Omega(0)h_U(0)+\mathcal J(U)-2\langle h_U,\nu\rangle$. A linear packet energy equal to a
quadratic bi-scale energy, for one compact source, is RH and simple zeros at once; such sources
are boosts of every nonzero source.

**Every zero a probe sees is felt in both directions.** Unconditionally, for every critical zero
$\rho$, $\limsup_{\tau\to\infty}P_f(\tau)\ge m_\rho\lvert\hat f(\gamma_\rho)\rvert$ and
$\liminf P_f\le-m_\rho\lvert\hat f(\gamma_\rho)\rvert$ (`packet_zero_amplitude_law`): the Bohr mean of the
critical series against $e^{-i\gamma_\rho\tau}$ picks out its coefficient. When the packet is bounded
above, the sign changes occur in every window of one fixed length, so under RH the smoothed
prime–polar discrepancy changes sign in every multiplicative interval $[X,e^\ell X]$
(`packet_sign_changes_in_every_window_of_riemannHypothesis`).

**The Weil energy is the recurrent maximum of the translated pairings.** The packet of the
autocorrelation at shift $\tau$ is the translated pairing $\langle h_f(\cdot-\tau),\nu\rangle$; beyond
the support its negative is a series with nonnegative coefficients $m_\rho\lvert\hat f(\gamma_\rho)\rvert^2$,
bounded by its value at $0$ and returning to it by simultaneous recurrence of finitely many
characters. Hence $W(h_f)\le\limsup_\tau-\langle h_f(\cdot-\tau),\nu\rangle$ unconditionally
(`weil_le_translated_pairing_frequently`), with equality when the packet is bounded above
(`pairing_recurrence_law`): the Lévy energy of a source is fixed by prime–polar pairings alone, its
pairing at the origin and the recurrent maximum of its translates.

**Multiplicities, bands and an explicit probe.** $E\le KW$ for every compact source iff every
critical zero has multiplicity at most $K$ (`multiplicity_ceiling_law`): $\sup_fE(f)/W(f)$ is the
maximal critical multiplicity, read by one family of tuned splines. The band of a single packet obeys
the band law of §3.10: $\int_T^LP_f^2=O((1+L)e^{2\sigma L})$ iff $f$ is blind beyond depth $\sigma$
(`packet_band_iff`), so for a universal probe RH is linearity of the band of one packet
(`riemannHypothesis_iff_packet_band_of_universal`) and the zero width is half its exponential rate. A
universal probe is explicit: for a source whose transform is real-rooted every boost $e^{tu}\varphi$
with $\lvert t\rvert\ge1/2$ is universal (`seesAllZeros_tiltedSource_of_im_ne_zero`), and the cubic
spline $B=U_1^{\star4}$, transform $(\sin z/z)^4$, gives
$\text{RH}\iff\sum_n\Lambda(n)\sqrt n\,B(\log n-\tau)\le\int_0^\infty2\cosh(x/2)e^xB(x-\tau)\,dx+Ke^\tau$ for
all large $\tau$: one fixed spline-weighted prime sum against its polar prediction.

**The band is eventually above the zero energy.** Under RH, for every finite set $S$ of zeros and
every $\varepsilon>0$, $(1/M)\int_0^M\tilde E^2\ge\sum_{\rho\in S}m_\rho^2/\lvert\rho\rvert^2-\varepsilon$ for
all large $M$ (`cramer_liminf_law`), not only infinitely often: Cramér's lower bound in liminf form,
through the gauge bridge from the packet to the Chebyshev gauge convolution.

### 3.12 Producers

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
- **Spectral designs.** Midpoint atoms, quarter-shifted atoms, orbit atoms and mixed quadrature
  designs under a wide envelope realize prescribed correlation zeros exactly and prescribed
  symbol values up to the envelope energy; they are the producers of the blind cone and attain
  every bathtub, window and moment constant of §3.5 and §3.6.

### 3.13 Coprime shear and the Sobolev side

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

### 3.14 Arithmetic observation theory

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

The passage from full-period moments to polynomial-horizon windows (tuple and Chinese-remainder
transfer, top-anchor recovery from windows, the horizon hierarchy $N^{m\pm o(1)}$) is owned by the
Bézout–Valuation Incidence programme and is used from there, not rebuilt here.

### 3.15 Bridges

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
counterexamples. On the zero side: the unconditional explicit formula of the zero configuration,
the critical-Mellin resolvent continuation and generalized von Koch bound, the one-sided Landau
engine, the exponential-type non-annihilation theorem and the superlinear count of simple critical
zeros, which the packet laws of §3.11 consume; the blind symbol slacks of §3.6 refine the
prime-blind archimedean positivity constants of the RH tower, whose full-grid zero-pole version
is RH itself.

---

### 3.16 Node criticality: deletion prices, window spectra and composite nodes

Write $A(c)$ for the archimedean part with the pole, $W(c)$ for the Weil functional, so that
$A-W=\sum_n\Lambda(n)L_n(c)$ with the node values $L_n$, and $w(m)=\Lambda(m)/\sqrt m$.

**Incidence decides zero-pole positivity.** On every node set $\mathcal N$, zero-pole blind positivity
holds iff RH holds and every prime power lies in $\mathcal N$; the pole constraint is invisible to
node criticality, density never suffices (the primes miss $4$), and a non-prime-power such as $6$ can be
added or deleted freely (`PrimePowerZeroPoleNodeCriticality`).

**Deletion prices are local Euler factors.** On the cone blind at every prime power outside a set $D$,
$(A-W)/\|c\|^2$ ranges over: $[-w(m),w(m)]$ for $D=\{m\}$ (tower Fejér bound, narrow pairs);
$\pm\sum_{p\in P}w(p^{e(p)})$ for one prime power per prime (iterated pairs: a lag $\log(m_A/m_B)$ between
subset products is a prime power only along $A=B\cup\{r\}$); the open interval
$(-\sum_p 2\log p/(\sqrt p+1),\ \sum_p 2\log p/(\sqrt p-1))$ for whole towers, the range of the local
factor $2\operatorname{Re}(-\zeta_p'/\zeta_p)(\tfrac12+it)$ through the spectral identity
$\pi\sum_kL_{p^k}=\int G_c\,S_{p^{-1/2}}(t\log p)$, $S_x(\theta)=\sum_{k\ge1}x^k\cos k\theta$; inside one tower the
prices interact (for $\{2,4\}$: $(\sqrt{17}-1)\log2/4$). Prices add across primes and never inside a
tower (`PrimePowerNodeDeletionPrice`, `PrimePowerDeletionPriceAdditivity`,
`PrimePowerDeletionPriceEulerAdditivity`, `PrimePowerTowerDeletionInteraction`,
`PrimeTowerDeletionLocalEulerFactor`).

**Composite nodes.** On the integer-grid cone (blindness also at every composite), deleting one prime
power per prime costs exactly the same supremum: staircase trains at $k\log(m_2/m_1)+\varepsilon\log m_1$
live on the slab of exponent sum $0,1$, whose only integer lags are $m_1$ and $m_2$
(`PrimePowerDeletionStaircaseTrains`). Deleting whole towers does not: blindness at $pq$ lowers the
supremum by an explicit constant, $\ge 9/10$ for $\{2,3\}$, because the prime-power extremal sits at the
joint phase where every composite is charged; the certificate is $-(c_0/2)\cos(t\log pq)$ against the
quadratic drop $S_x(\theta)\le x/(1-x)-x(1-\cos\theta)/(1-x^2)$ (`PrimeTowerDeletionCompositeCharge`).
So $\log 6$ is free for the nodes $\{2,3\}$ and costs for their towers. For any finite set of
primes the same slab construction gives the Euler price on the integer grid
(`PrimePowerDeletionSlabTrains`). Attainment is rigid: the deletion defect at $m$ is the energy of
the alternating periodization along $\log m$ over one period, so only pairs $g+g(\cdot-\log m)$
attain $w(m)$ (`PrimePowerDeletionPeriodizationDefect`); peeling primes one at a time, with the
periodizations of the remainder forced to vanish by the density of $\log m_1\mathbb Z+\log m_2\mathbb Z$,
the Euler price is attained on windows of length $L$ iff $L>\log\prod_pm_p$
(`PrimePowerDeletionPairThreshold`, `PrimePowerDeletionEulerThreshold`). Composites are free for the
price and forced for its extremals. A tower pair behaves differently: deleting $\{m,m^2\}$, the
window spectrum is $\{0\}$ up to $\log m$, exactly $[-w(m),w(m)]$ up to $\log m^2$ (the square's lag
does not fit, so the square is blind for free), and the joint range of the tower beyond
(`PrimePowerTowerPairWindowSpectrum`). The joint price of $\{2,4\}$ appears at $\log 4$, the lag of a
deleted node; that of $\{2,3\}$ at $\log 6$, the lag of a node that is never charged.

**Window spectra.** For tests in intervals of length $L=\log X$ the prime side is the compressed
operator $\sum_{n<X}w(n)(S_{\log n}+S_{\log n}^*)$. Its extremes: $\pm\lambda_{23}$,
$\lambda_{23}=(w_3+\sqrt{w_3^2+4w_2^2})/2$, for $\log3<L<\log4$ (path components, `PrimeWindowCeilings`);
the $\{2,3\}$ price is $\le 1.11<w_2+w_3$ for $L\le\log6$ and exactly $w_2+w_3$ beyond, since below
$\log 6$ the lag graph is a union of Sturmian paths with double-$w_2$ vertices
(`PrimeTwoThreeDecouplingLength`); asymptotically $c(L)/e^{L/2}\to1$ and $\mathrm{floor}(L)/e^{L/2}\to-1$, the
spectral pair of the polar kernel $e^{|s-t|/2}$ with eigenfunction $e^{-t/2}\pm e^{-(L-t)/2}$
(`PrimeWindowCeilingPolarAsymptotics`, `PrimeWindowFloorPolarAsymptotics`), and to de la Vallée
Poussin precision, unconditionally: $|c(L)-e^{L/2}|\le Ce^{L/2-\kappa\sqrt L}$ and
$|\mathrm{floor}(L)+e^{L/2}|\le Ce^{L/2-\kappa\sqrt L}$ for all large $L$, the window analogue of the
lag envelope $P_v\ge-|\varphi(0)|-Ce^{v/2-\sqrt v/10}$: the prime number theorem with error term
enters the polar Schur bound, and the polar weight loses at the window midpoint only against power
errors $x^\gamma$, never against $xe^{-c\sqrt{\log x}}$ (`PrimeWindowCeilingDeLaValleePoussinRemainder`).
The polar Schur bound holds for every nonincreasing error profile $E\le1$, with gain
$E(L/4)+e^{-L/4}$, so the window remainder carries exactly the strength of the prime number theorem
that enters: with the Vinogradov–Korobov theorem, for every $ex<3/5$,
$|c(L)-e^{L/2}|\le Ce^{L/2-\kappa L^{ex}}$, $|\mathrm{floor}(L)+e^{L/2}|\le Ce^{L/2-\kappa L^{ex}}$, and
$|D(T)|\le Ce^{T-\kappa T^{ex}}$ for the integrated Chebyshev deficit $D(T)=\int_0^T(e^t-\psi(e^t))\,dt$
(`PrimeWindowCeilingVinogradovKorobovRemainder`).
At square-root precision:
$c(L)\le e^{L/2}+O(L)$ forces RH, the excess exponent $\theta^*$ satisfies
$\mathrm{width}\le\theta^*\le\mathrm{width}/2+\tfrac14$ (`PrimeWindowCeilingRHCriterion`,
`PrimeWindowCeilingWidthLaw`, through the width-$\alpha$ Landau criterion of
`DeficitPrimitiveOneSidedWidth`), and the spectrum is mirror-symmetric to $O(\log X)$:
$|c(L)+\mathrm{floor}(L)|\le4L+O(1)$, so the floor reads RH and the width as the ceiling does
(`PrimeWindowLiouvilleMirror`). The mirror is Kronecker's theorem: modulating by $e^{i\xi u}$ with
$p^{i\xi}\approx-1$ for all $p<X$ turns the prime measure into its Liouville twist up to the squares;
window extremes see the atoms only through their sizes; more generally the window ceiling and
floor of every unimodular completely multiplicative twist of the atoms (Dirichlet characters,
vertical shifts) equal those of $\zeta$ (`PrimeWindowTwistInvariance`), so window extremes cannot
read GRH.

## 4. Traps and sharp boundaries

| trap | correct statement |
|---|---|
| Bounding by the spectral second moment $S(f)=-h''(0)$ or by $\Omega(0)$ alone. | Discards $\mathcal J$; grid constraints become invisible as $S(f)/h(0)\to\infty$. Bound increments by $\mathcal J$ through Krein's inequality. |
| Subtracting a translation-invariant mean field. | Cannot distinguish $\Lambda_{\log}$ from a shifted continuum; the node positions must enter the cone. |
| Applying $f\mapsto\lvert f\rvert$ to a sign-changing state. | Drops the cross collar $4f^+(u)f^-(u+x)$; keep the nodal loss and move it to slack. |
| One zero bounds the increment at one interior point. | At $x=\tfrac45\log2$ a pulse train has $h(\log2)=0$ and $(h(0)-h(x))/h(0)\to0$; only the reflected pair is bounded, so fold the interval. |
| Finitely many grid zeros plus polar balance; or "the infinite grid forces the pole". | The boundary is gaps against density, not finite against infinite: on every gapped or sub-square-root-density node set the pole is carried at vanishing archimedean cost and zero-pole positivity fails; on the full grid it is RH. |
| The polar constraint improves a single-prime bathtub. | It does not: the zero-pole slack on the powers of any integer equals the slack, exactly $-m_q$. |
| Blindness at all nodes is needed for the bathtub. | Blindness at the powers of one integer alone gives $A\ge m_q\,\mathrm{mass}$, and this is exact. |
| A second blind node improves the bathtub by an amount depending on its spacing. | The gain is an incidence law: zero if the node is a power of $q$, strictly positive and explicit otherwise. |
| Blind slacks on power sets need bespoke constructions. | Every such slack is the value of one circle moment problem for the folded symbol; designs solve it. |
| Commutative Bochner or Beurling reasoning. | Translation inner products see only divisibility, shared with Beurling systems off the line; use the successor coupling and non-commuting multipliers. |
| Source blindness implies multiplier blindness. | False: the odd six-packet train. Use the light cone and signed collar leverage on $C_\alpha f$, $S_\alpha f$. |
| Compressing support into a midpoint gap. | Costs $\asymp\log N$ normalized energy; width rigidity forbids it at bounded energy. |
| Working only on the blind subspace. | Multiplies $\Lambda(n)/\sqrt n$ by zero and cannot see off-line countermodels; state theorems for signed correlations. |
| Receiver-only reformulations; subtracting the counterterm before the floor sum. | The second replaces $T(N)$ by Dirichlet's divisor sum with $O(\sqrt N)$ noise. Build producers with unconditional bounds. |
| "The clique window bound $\delta\sqrt{M+1}\,h(0)$ is sharp." | The true order is $\log M$ in both directions, between $(\delta/4\pi)\log(M+2)$ and $12\delta(4+\log(M+1))$. |
| Squared or finite-order closed-cycle data determine polar balance. | Polar-attenuated opposite copies share all squared correlations and all closed products through any fixed order; recovery needs all orders, or energy-controlled cycles with explicit mesh. |
| The local cube-root classification applies to Möbius rows. | It needs a nonzero top dyadic coordinate; squarefree rows have none for $N\ge4$, and a prime anchor does not transfer the argument. For $N\ge9$ no exponent above $1/3$ holds for them. |
| Witness factors are recovery constants. | The $(N!)^6$ factors in sharpness witnesses bound particular moments; the recovery constants are $2+2\sum\varphi(q)$ and depend on $N$; all observations here are full-period moments. |
| Positivity on the whole source graph. | The constant lift has energy $-c^2/2$; a positivity target must name its odd or otherwise constrained family. |
| Windowed Chebyshev energy is band-limited. | The sharp window creates the jump $\tilde E(L)$ with energy $\asymp\tilde E(L)^2/\xi_0$; the Laplace energy is the band-limited object. |
| A mean square $\int_0^L\tilde E^2$ strictly between linear and exponential growth. | Impossible: subexponential forces linear; the exponential rate is twice the zero width. |
| The two-by-two pole inequality needs a sign or positivity mechanism. | Its content is an order of magnitude: $\lvert\text{cross}(a)\rvert\le Ce^{a}$ gives RH on its own, the diagonal is of the same size, and the exact rate of the cross entry is $1+2\cdot\text{width}$. The missing input is a square-root-scale bound on the integrated Chebyshev deficit, not a positivity argument. |
| The barrier might be $o(L)$. | Never: Hardy's critical zero and the slope law give slope at least $1/|\rho|^2$. |
| Zeros are read only through quadratic forms. | The linear packet reads them: growth exponent, one-sided bounds and persistence are per-source statements, and a universal probe's single packet is RH-equivalent. |
| Two-sided control of a packet is needed. | One side suffices, by the one-sided Landau engine and the absence of real zeros in the strip. |
| A compact packet converges, or has bounded energy per unit source energy. | Every nonzero packet oscillates with amplitude at least $\sqrt{E(f)}$, and for width-$t$ probes the energy ratio grows like $\log(1/t)$. |
| Packet energy equals Weil energy. | $W\le E$ always; equality holds exactly when the critical zeros seen are simple. |
| A bound for the compact factorial source bounds its completion. | The omitted Müntz tail has unbounded normalized Weil energy. |
| Coherent price controls source energy. | A nonzero kernel family has zero coherent price and arbitrary energy. |
| Prime clock kernels are lag-only. | They retain the centre and cutoff; no translation invariance or sign of edge minus mass is proved. |
| Rebuilding polynomial-horizon moment transfer here. | It is owned by the Bézout–Valuation Incidence programme; search the whole Lean tree, including other programmes' folders, before building arithmetic-observation tools. |

**Lean conventions.** Even polar tests are nested subtypes, so plain `linarith` or `nlinarith`
with such a term in context stalls; use `linarith only [...]` and call namespace theorems
explicitly rather than by dot projection. Inside the field's namespaces `open RHTower` resolves to
the field's own `RHTower` namespace; write `_root_.RHTower.…` for the root one. Capstones are stated
on data parameters; theorems that conclude `RiemannHypothesis` are implications or equivalences
whose premise is one explicit energy bound, never asserted. Analytic inputs (Mertens, Chebyshev,
Vinogradov–Korobov, Hoheisel, Montgomery–Vaughan, Hardy's theorem, the explicit formula of the
zero configuration, the one-sided Landau engine) are proved corpus theorems. Blind-cone
statements are made on node sets (`BlindOn 𝒩`) and slacks on node sets, so that the full grid,
single-integer power sets and gapped sets are instances of one definition.

---

## 5. The frontier

**The band.** In the field's coordinates the square-root barrier is $\int_0^L\tilde E^2=O(L)$,
equivalently $O(L)$ Laplace energy of $\nu_N$, equivalently $O(L)$ energy in the band
$|\xi|\le\sqrt{N+2}$; everything outside the band is bounded, the band's exponential rate is the
zero width, its slope dominates the zero energy $\sum m_\rho^2/|\rho|^2$, it is never sublinear,
it cannot grow strictly between linear and exponential, and the linear band is RH in both
directions. What remains is the linear band itself. A mechanism that closes it must fail for
Beurling systems, survive the degenerate point of one character and modulus one, carry
information beyond polynomial length equal to height at square-root precision, and separate
$\log4$ from $\log6$; additive tools do the first and third only after averaging over a family,
multiplicative tools are Beurling-invariant. Sharper questions inside the band: whether the band
constant under RH equals the zero energy (Cramér's limiting constant; the liminf of the band mean
is at least the zero energy), the asymptotics of the
finite-cutoff packet energy including the endpoint term $\tilde E(L)^2$, and an effective version
of the universal-probe criterion in which the boost is explicit.

**The blind cone.** On the powers of one integer the slack is completely known, as a circle
moment problem with closed forms for the full set, one deleted node and the off-multiples. On the
powers of two integers the spectral law is a probability law on the line with uniform projections
on both circles $r\mapsto r\ell_i\bmod 2\pi$; the joint phase winds densely around the torus and
the symbol $\gamma(r)$ is a function on the line, not on the torus. Weak duality holds with *line
certificates*, continuous circle observables with $P_1(r\ell_1)+P_2(r\ell_2)\le\gamma(r)$ for all
real $r$, and product midpoint designs $\omega_a\pm\omega'_b$, whose cosine sums factor, attain the
mean $T(q_1,q_2)$ of $\gamma$ under the convolution of the two uniform period laws. Hence the exact
slack lies in $[-T(q_1,q_2),\,-m_{q_1}-\eta(q_1,q_2)]$ (`TwoTowerBlindSlackEnclosure`). Open: its exact
value (the box convolution is the admissible law of smallest support, not expected to be
optimal); the infimum of $\mathcal J/h(0)$ on the full blind polar class against $|\Omega(0)|$,
which is prime-blind archimedean positivity; and, since zero-pole positivity on a node set is
decided by incidence rather than density (§3.16: RH together with containment of every prime
power, so the primes alone never suffice and no composite matters), the slack of the cone blind
at exactly the prime powers as a function of the window length, between the Euler prices of
§3.16 and the full-grid value.

**The odd sector.** The coherent price $\log 2$ is sharp and the finite-filter gain is strict, but
the full odd Weil sign is not proved; at pole weight one the odd bound retains a positive
$\sinh$-moment cost.

**Packets.** The maximal critical multiplicity is $\sup_fE(f)/W(f)$, every zero a probe sees is
felt with its amplitude in both directions, and the Weil energy is bounded by the recurrent
maximum of the translated pairings of one packet. Open: whether the identity $E(U)=W(U)$ can be
tested through finitely many primes, and whether the Weil energy of $h_f$ is bounded above by
prime-side data of a single linear packet without the one-sided hypothesis, which is the question
that separates the packet laws from an RH proof.

**Arithmetic observation.** A common organizing theorem for the two halves exists only as a
classification by sign characters of the subgroup generated by the support; the quantitative
version through bounded-length relations, with energy and realization costs on both sides, is
open. Stability off the strata (vanishing top coordinate, changing support) and a stable
mixed-stratum formulation are open.

**Producers.** The Müntz correction tail shows that the compact factorial family cannot be
completed inside the decay-class Weil domain at bounded normalized energy; a producer family with
bounded completion cost, or a proof that none exists, is open. For the prime clocks the arithmetic
estimates for the mass and edge kernels and the sign of their difference are open.

### Research topics toward the shared target

1. **Node criticality.** What in the multiplicative incidence of the node set `{log n}` makes
   `log 4` indispensable and `log 6` redundant beyond the deletion prices and window thresholds of
   §3.16 (the price of `4` is a local Euler factor and appears at its own lag, `log 6` is the lag
   of a node that is never charged), and how a positivity argument at arbitrary support reads it;
   this is the criterion every mechanism of the shared target must pass.
2. **Prime-blind archimedean positivity.** The infimum of `𝒥/h(0)` on the full blind polar class
   against `|Ω(0)|`, with its exact slack, as the input to the sign-changing gauges of mechanism 1.
3. **The linear band itself**, tested against the four requirements of §5: failure for Beurling
   systems, survival at one character and modulus one, information beyond polynomial length at
   square-root precision, separation of `log 4` from `log 6`. Equivalent coordinates for the same
   demand, to be used interchangeably: a square-root-scale bound on the integrated Chebyshev
   deficit `D(T) = ∫_0^T(e^t − ψ(e^t))dt`, equivalently on the cross entry of the two-exponential
   pole compression; the unconditional rate there is `2` (Vinogradov–Korobov) against the needed
   `1 + 2α`, and any improvement of the rate is an explicit strip.
4. **Packets and multiplicity.** Whether the packet identity `E(U) = W(U)` can be tested through
   finitely many primes, and a one-packet upper bound for the Weil energy without the one-sided
   hypothesis, as the spectral input of mechanism 4.
5. **Selectivity and calibration models.** A Beurling system with an off-line zero, the shifted pair
   `ζ(s−a)ζ(s+a)`, the Liouville twist and the function-field case `F_q[T]`, each written in the
   coordinates of the shared target (node values, window spectra, packets, the blind cone), so that
   every positivity or cancellation theorem of the sibling programmes can be tested against them. The
   Beurling deletion and perturbation systems of `RHTower` and `HTGeometry` and the function-field
   window and purity modules are the starting objects; the unit is the list of shared-target
   statements each model refutes.

---

## 6. Working in the theory

- **Never differentiate the correlation.** Every bound goes through Krein's inequality or its
  linear smoothing and is paid by $\mathcal J$; the spectral second moment is never admissible.
- **Keep the signs.** Signed node values, signed packets, signed Gram entries; blindness is a
  sharpness check, not a hypothesis. A theorem on the blind cone must say so, and must say on
  which node set.
- **Say which regime.** Finite grid or infinite; compact source, $C^1$, $C^2$, or decay class;
  period moments or finite horizon; polar or non-polar; even, odd, or arbitrary parity; which
  node set. The infima and the sharp exponents change with each.
- **Pass to the right coordinates.** For blind-cone questions on power sets, pass to the phase
  measure on the circle and the folded symbol; for zero questions, pass to the linear stationary
  packet and its zero series rather than to the quadratic Weil form; for packet-energy questions,
  pass through the hyperbolic gauge, where the arithmetic sits in $\tilde E$ alone and all
  correlation tools act on $h_{f'-f/2}$.
- **Receivers come with producers.** Do not add a reformulation of the explicit formula without an
  explicit test, weight, stencil or spectral design whose error is bounded unconditionally.
- **Test against Beurling and against the degenerate point.** If the mechanism would hold for a
  generalized number system, or needs a family average to work, it cannot close the band.
- **Search before building.** The corpus already holds the exact identities for the objects of §2;
  check the sieve, Fermi–Nyman, source-graph and zero-configuration modules, and the other
  programmes' folders, before constructing a new bridge or an observation tool.
